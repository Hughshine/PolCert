module IR = SPolIRs.SPolIRs
module Loop = IR.Loop
module Instr = IR.Instr

let indent n = String.make (2 * n) ' '
let z0 = Camlcoq.Z.zero
let z1 = Camlcoq.Z.one
let zminus1 = Camlcoq.Z.mone

let nth_or xs n default =
  try List.nth xs n with _ -> default

let name_of_ident id = Camlcoq.extern_atom id
let name_of_nat n = string_of_int (Camlcoq.Nat.to_int n)
let string_of_z z = Camlcoq.Z.to_string z
let z_eq a b = Camlcoq.Z.eq a b

let rec loop_expr_equal a b = a = b

let is_z z = function
  | Loop.Constant z' -> z_eq z z'
  | _ -> false

let rec collect_loop_sum c acc = function
  | Loop.Sum (a, b) ->
      let c, acc = collect_loop_sum c acc a in
      collect_loop_sum c acc b
  | Loop.Constant z -> (Camlcoq.Z.add c z, acc)
  | e -> (c, e :: acc)

let build_loop_sum terms c =
  let terms = List.rev terms in
  match terms, z_eq c z0 with
  | [], true -> Loop.Constant z0
  | [], false -> Loop.Constant c
  | [e], true -> e
  | [e], false -> Loop.Sum (e, Loop.Constant c)
  | e :: es, true -> List.fold_left (fun acc e -> Loop.Sum (acc, e)) e es
  | e :: es, false ->
      List.fold_left (fun acc e -> Loop.Sum (acc, e)) (Loop.Sum (e, Loop.Constant c)) es

let rec simplify_loop_expr = function
  | (Loop.Constant _ | Loop.Var _) as e -> e
  | Loop.Sum (a, b) ->
      let a = simplify_loop_expr a in
      let b = simplify_loop_expr b in
      let c, terms = collect_loop_sum z0 [] (Loop.Sum (a, b)) in
      build_loop_sum terms c
  | Loop.Mult (k, e) ->
      let e = simplify_loop_expr e in
      if z_eq k z0 then Loop.Constant z0
      else if z_eq k z1 then e
      else
        begin match e with
        | Loop.Constant z -> Loop.Constant (Camlcoq.Z.mul k z)
        | Loop.Mult (k', e') -> simplify_loop_expr (Loop.Mult (Camlcoq.Z.mul k k', e'))
        | _ -> Loop.Mult (k, e)
        end
  | Loop.Div (e, k) ->
      let e = simplify_loop_expr e in
      if z_eq k z1 then e
      else if is_z z0 e then Loop.Constant z0
      else
        begin match e with
        | Loop.Constant z -> Loop.Constant (Camlcoq.Z.div z k)
        | _ -> Loop.Div (e, k)
        end
  | Loop.Mod (e, k) ->
      let e = simplify_loop_expr e in
      if is_z z0 e then Loop.Constant z0
      else
        begin match e with
        | Loop.Constant z -> Loop.Constant (Camlcoq.Z.modulo z k)
        | _ -> Loop.Mod (e, k)
        end
  | Loop.Max (a, b) ->
      let a = simplify_loop_expr a in
      let b = simplify_loop_expr b in
      if loop_expr_equal a b then a
      else
        begin match a, b with
        | Loop.Constant za, Loop.Constant zb ->
            Loop.Constant (if Camlcoq.Z.ge za zb then za else zb)
        | _ -> Loop.Max (a, b)
        end
  | Loop.Min (a, b) ->
      let a = simplify_loop_expr a in
      let b = simplify_loop_expr b in
      if loop_expr_equal a b then a
      else
        begin match a, b with
        | Loop.Constant za, Loop.Constant zb ->
            Loop.Constant (if Camlcoq.Z.le za zb then za else zb)
        | _ -> Loop.Min (a, b)
        end

let rec simplify_instr_expr = function
  | (Instr.ExConst _ | Instr.ExFloat _ | Instr.ExVar _ | Instr.ExAccess _) as e -> e
  | Instr.ExAdd (a, b) ->
      let a = simplify_instr_expr a in
      let b = simplify_instr_expr b in
      begin match a, b with
      | Instr.ExConst za, Instr.ExConst zb -> Instr.ExConst (Camlcoq.Z.add za zb)
      | Instr.ExConst za, e when z_eq za z0 -> e
      | e, Instr.ExConst zb when z_eq zb z0 -> e
      | _ -> Instr.ExAdd (a, b)
      end
  | Instr.ExSub (a, b) ->
      let a = simplify_instr_expr a in
      let b = simplify_instr_expr b in
      begin match a, b with
      | Instr.ExConst za, Instr.ExConst zb -> Instr.ExConst (Camlcoq.Z.sub za zb)
      | e, Instr.ExConst zb when z_eq zb z0 -> e
      | _ -> Instr.ExSub (a, b)
      end
  | Instr.ExMul (a, b) ->
      let a = simplify_instr_expr a in
      let b = simplify_instr_expr b in
      begin match a, b with
      | Instr.ExConst za, Instr.ExConst zb -> Instr.ExConst (Camlcoq.Z.mul za zb)
      | Instr.ExConst za, _ when z_eq za z0 -> Instr.ExConst z0
      | _, Instr.ExConst zb when z_eq zb z0 -> Instr.ExConst z0
      | Instr.ExConst za, e when z_eq za z1 -> e
      | e, Instr.ExConst zb when z_eq zb z1 -> e
      | _ -> Instr.ExMul (a, b)
      end
  | Instr.ExDiv (a, b) ->
      let a = simplify_instr_expr a in
      let b = simplify_instr_expr b in
      begin match a, b with
      | Instr.ExConst za, Instr.ExConst zb -> Instr.ExConst (Camlcoq.Z.div za zb)
      | Instr.ExConst za, _ when z_eq za z0 -> Instr.ExConst z0
      | e, Instr.ExConst zb when z_eq zb z1 -> e
      | _ -> Instr.ExDiv (a, b)
      end
  | Instr.ExLe (a, b) ->
      let a = simplify_instr_expr a in
      let b = simplify_instr_expr b in
      Instr.ExLe (a, b)
  | Instr.ExEq (a, b) ->
      let a = simplify_instr_expr a in
      let b = simplify_instr_expr b in
      Instr.ExEq (a, b)
  | Instr.ExAnd (a, b) ->
      let a = simplify_instr_expr a in
      let b = simplify_instr_expr b in
      Instr.ExAnd (a, b)
  | Instr.ExCall (fn, args) ->
      Instr.ExCall (fn, List.map simplify_instr_expr args)
  | Instr.ExCond (c, t, f) ->
      Instr.ExCond (simplify_instr_expr c, simplify_instr_expr t, simplify_instr_expr f)

let normalize_loop_le a b =
  match a, b with
  | Loop.Mult (k, e), Loop.Constant z when z_eq k zminus1 ->
      (Loop.Constant (Camlcoq.Z.mul zminus1 z), simplify_loop_expr e)
  | Loop.Constant z, Loop.Mult (k, e) when z_eq k zminus1 ->
      (simplify_loop_expr e, Loop.Constant (Camlcoq.Z.mul zminus1 z))
  | _ -> (a, b)

let rec simplify_test = function
  | Loop.LE (a, b) ->
      let a = simplify_loop_expr a in
      let b = simplify_loop_expr b in
      let a, b = normalize_loop_le a b in
      if loop_expr_equal a b then Loop.TConstantTest true
      else
        begin match a, b with
        | Loop.Constant za, Loop.Constant zb -> Loop.TConstantTest (Camlcoq.Z.le za zb)
        | _ -> Loop.LE (a, b)
        end
  | Loop.EQ (a, b) ->
      let a = simplify_loop_expr a in
      let b = simplify_loop_expr b in
      if loop_expr_equal a b then Loop.TConstantTest true
      else
        begin match a, b with
        | Loop.Constant za, Loop.Constant zb -> Loop.TConstantTest (z_eq za zb)
        | _ -> Loop.EQ (a, b)
        end
  | Loop.And (a, b) ->
      begin match simplify_test a, simplify_test b with
      | Loop.TConstantTest true, t
      | t, Loop.TConstantTest true -> t
      | Loop.TConstantTest false, _
      | _, Loop.TConstantTest false -> Loop.TConstantTest false
      | a, b -> Loop.And (a, b)
      end
  | Loop.Or (a, b) ->
      begin match simplify_test a, simplify_test b with
      | Loop.TConstantTest false, t
      | t, Loop.TConstantTest false -> t
      | Loop.TConstantTest true, _
      | _, Loop.TConstantTest true -> Loop.TConstantTest true
      | a, b -> Loop.Or (a, b)
      end
  | Loop.Not t ->
      begin match simplify_test t with
      | Loop.TConstantTest b -> Loop.TConstantTest (not b)
      | t -> Loop.Not t
      end
  | Loop.TConstantTest _ as t -> t

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
  string_of_loop_expr_raw env (simplify_loop_expr e)

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
  go (simplify_instr_expr expr)

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
  go (simplify_test tst)

let rec stmt_list_to_list = function
  | Loop.SNil -> []
  | Loop.SCons (st, tl) -> st :: stmt_list_to_list tl

let fresh_loop_name env depth =
  let rec pick n =
    let cand = Printf.sprintf "i%d" (depth + n) in
    if List.mem cand env then pick (n + 1) else cand
  in
  pick 0

let is_singleton_range lb ub =
  let lb = simplify_loop_expr lb in
  let ub = simplify_loop_expr ub in
  match lb, ub with
  | Loop.Constant zlb, Loop.Constant zub ->
      z_eq (Camlcoq.Z.sub zub zlb) z1
  | _, Loop.Sum (e, Loop.Constant k)
  | _, Loop.Sum (Loop.Constant k, e) -> loop_expr_equal e lb && z_eq k z1
  | _ -> false

let rec lines_of_stmt env depth lvl = function
  | Loop.Loop (lb, ub, body) ->
      let lb = simplify_loop_expr lb in
      let ub = simplify_loop_expr ub in
      if is_singleton_range lb ub then
        (* Print singleton loops as a let-like substitution in the body. *)
        lines_of_stmt ((string_of_loop_expr env lb) :: env) (depth + 1) lvl body
      else
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
      begin match simplify_test tst with
      | Loop.TConstantTest true -> lines_of_stmt env depth lvl body
      | tst ->
          let header = Printf.sprintf "%sif (%s) {" (indent lvl) (string_of_test env tst) in
          let body_lines = lines_of_stmt env depth (lvl + 1) body in
          header :: body_lines @ [indent lvl ^ "}"]
      end

let string_of_loop (((stmt, varctxt), _vars) : IR.Loop.t) =
  let ctxt_names = List.map name_of_ident varctxt in
  let header =
    match ctxt_names with
    | [] -> []
    | _ -> ["context(" ^ String.concat ", " ctxt_names ^ ");"; ""]
  in
  String.concat "\n" (header @ lines_of_stmt (List.rev ctxt_names) 0 0 stmt) ^ "\n"
