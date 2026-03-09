module IR = SPolIRs.SPolIRs
module Loop = IR.Loop
module Instr = IR.Instr

let indent n = String.make (2 * n) ' '
let z0 = Camlcoq.Z.zero
let z1 = Camlcoq.Z.one
let z_eq a b = Camlcoq.Z.eq a b

let nth_or xs n default =
  try List.nth xs n with _ -> default

let name_of_ident id = Camlcoq.extern_atom id
let name_of_nat n = string_of_int (Camlcoq.Nat.to_int n)
let string_of_z z = Camlcoq.Z.to_string z

let rec string_of_loop_expr_raw env = function
  | Loop.Constant z -> string_of_z z
  | Loop.Var n -> nth_or env (Camlcoq.Nat.to_int n) ("v" ^ name_of_nat n)
  | Loop.Sum (a, b) -> Printf.sprintf "(%s + %s)" (string_of_loop_expr_raw env a) (string_of_loop_expr_raw env b)
  | Loop.Mult (k, e) -> Printf.sprintf "(%s * %s)" (string_of_z k) (string_of_loop_expr_raw env e)
  | Loop.Div (e, k) -> Printf.sprintf "(%s / %s)" (string_of_loop_expr_raw env e) (string_of_z k)
  | Loop.Mod (e, k) -> Printf.sprintf "(%s %% %s)" (string_of_loop_expr_raw env e) (string_of_z k)
  | Loop.Max (a, b) -> Printf.sprintf "max(%s, %s)" (string_of_loop_expr_raw env a) (string_of_loop_expr_raw env b)
  | Loop.Min (a, b) -> Printf.sprintf "min(%s, %s)" (string_of_loop_expr_raw env a) (string_of_loop_expr_raw env b)

let string_of_loop_expr env e =
  string_of_loop_expr_raw env e

let slot_expr slots n = nth_or slots (Camlcoq.Nat.to_int n) (Loop.Constant (Camlcoq.Z.of_sint 0))

let string_of_affine env slots aff =
  let rec go = function
    | Instr.AeConst z -> string_of_z z
    | Instr.AeVar n -> string_of_loop_expr env (slot_expr slots n)
    | Instr.AeAdd (a, b) -> Printf.sprintf "(%s + %s)" (go a) (go b)
    | Instr.AeSub (a, b) -> Printf.sprintf "(%s - %s)" (go a) (go b)
    | Instr.AeMul (k, e) ->
        if z_eq k z0 then "0"
        else if z_eq k z1 then go e
        else Printf.sprintf "(%s * %s)" (string_of_z k) (go e)
  in
  go aff

let string_of_access env slots = function
  | Instr.AcVar id -> name_of_ident id
  | Instr.AcArr (id, idxs) ->
      let base = name_of_ident id in
      List.fold_left
        (fun acc idx -> acc ^ "[" ^ string_of_affine env slots idx ^ "]")
        base idxs

let string_of_instr_expr env slots expr =
  let rec go = function
    | Instr.ExConst z -> string_of_z z
    | Instr.ExFloat lit -> Camlcoq.camlstring_of_coqstring lit
    | Instr.ExVar n -> string_of_loop_expr env (slot_expr slots n)
    | Instr.ExAccess a -> string_of_access env slots a
    | Instr.ExAdd (a, b) -> Printf.sprintf "(%s + %s)" (go a) (go b)
    | Instr.ExSub (a, b) -> Printf.sprintf "(%s - %s)" (go a) (go b)
    | Instr.ExMul (a, b) -> Printf.sprintf "(%s * %s)" (go a) (go b)
    | Instr.ExDiv (a, b) -> Printf.sprintf "(%s / %s)" (go a) (go b)
    | Instr.ExLe (a, b) -> Printf.sprintf "(%s <= %s)" (go a) (go b)
    | Instr.ExEq (a, b) -> Printf.sprintf "(%s == %s)" (go a) (go b)
    | Instr.ExAnd (a, b) -> Printf.sprintf "(%s && %s)" (go a) (go b)
    | Instr.ExCall (fn, args) ->
        let fn = Camlcoq.camlstring_of_coqstring fn in
        let args =
          match List.map go args with
          | [] -> ""
          | hd :: tl -> List.fold_left (fun acc s -> acc ^ ", " ^ s) hd tl
        in
        Printf.sprintf "%s(%s)" fn args
    | Instr.ExCond (c, t, f) ->
        Printf.sprintf "(%s ? %s : %s)" (go c) (go t) (go f)
  in
  go expr

let string_of_test env tst =
  let rec go = function
    | Loop.LE (a, b) -> Printf.sprintf "%s <= %s" (string_of_loop_expr env a) (string_of_loop_expr env b)
    | Loop.EQ (a, b) -> Printf.sprintf "%s == %s" (string_of_loop_expr env a) (string_of_loop_expr env b)
    | Loop.And (a, b) -> Printf.sprintf "(%s && %s)" (go a) (go b)
    | Loop.Or (a, b) -> Printf.sprintf "(%s || %s)" (go a) (go b)
    | Loop.Not t -> Printf.sprintf "!(%s)" (go t)
    | Loop.TConstantTest true -> "true"
    | Loop.TConstantTest false -> "false"
  in
  go tst

let rec stmt_list_to_list = function
  | Loop.SNil -> []
  | Loop.SCons (st, tl) -> st :: stmt_list_to_list tl

let fresh_loop_name env depth =
  let rec pick n =
    let cand = Printf.sprintf "i%d" (depth + n) in
    if List.mem cand env then pick (n + 1) else cand
  in
  pick 0

let rec lines_of_stmt env depth lvl = function
  | Loop.Loop (lb, ub, body) ->
      let v = fresh_loop_name env depth in
      let header = Printf.sprintf "%sfor %s in range(%s, %s) {"
        (indent lvl) v (string_of_loop_expr env lb) (string_of_loop_expr env ub)
      in
      let body_lines = lines_of_stmt (v :: env) (depth + 1) (lvl + 1) body in
      header :: body_lines @ [indent lvl ^ "}"]
  | Loop.Instr (instr, slots) ->
      begin match instr with
      | Instr.SSkip -> [indent lvl ^ "skip;"]
      | Instr.SAssign (lhs, rhs) ->
          [indent lvl ^ string_of_access env slots lhs ^ " = " ^ string_of_instr_expr env slots rhs ^ ";"]
      end
  | Loop.Seq stmts -> List.concat_map (lines_of_stmt env depth lvl) (stmt_list_to_list stmts)
  | Loop.Guard (tst, body) ->
      let header = Printf.sprintf "%sif (%s) {" (indent lvl) (string_of_test env tst) in
      let body_lines = lines_of_stmt env depth (lvl + 1) body in
      header :: body_lines @ [indent lvl ^ "}"]

let string_of_loop (((stmt, varctxt), _vars) : IR.Loop.t) =
  let ctxt_names = List.map name_of_ident varctxt in
  let header =
    match ctxt_names with
    | [] -> []
    | _ -> ["context(" ^ String.concat ", " ctxt_names ^ ");"; ""]
  in
  String.concat "\n" (header @ lines_of_stmt (List.rev ctxt_names) 0 0 stmt) ^ "\n"
