open SLoopAst

module IR = SPolIRs.SPolIRs
module Loop = IR.Loop
module Instr = IR.Instr

exception Error of string

let errorf fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

let z_of_int = Camlcoq.Z.of_sint
let nat_of_int = Camlcoq.Nat.of_int

let ident_of_string s =
  AST.varname_to_ident (Camlcoq.coqstring_of_camlstring s)

let rec dedup = function
  | [] -> []
  | x :: xs -> if List.mem x xs then dedup xs else x :: dedup xs

let ensure_unique what names =
  let rec go seen = function
    | [] -> ()
    | x :: xs ->
        if List.mem x seen
        then errorf "duplicate %s name: %s" what x
        else go (x :: seen) xs
  in
  go [] names

type env = {
  params : string list;
  loops : string list;
}

let loop_env env = List.rev env.loops @ env.params
let slot_env env = env.params @ env.loops

let lookup_in names name =
  let rec go idx = function
    | [] -> None
    | x :: xs -> if String.equal x name then Some idx else go (idx + 1) xs
  in
  go 0 names

let lookup_loop env name = lookup_in (loop_env env) name
let lookup_slot env name = lookup_in (slot_env env) name

let ensure_not_bound env name kind =
  if List.mem name (loop_env env)
  then errorf "%s %s conflicts with a loop/context variable" kind name

let stmt_list_of_list stmts =
  List.fold_right (fun st acc -> Loop.SCons (st, acc)) stmts Loop.SNil

let stmt_of_list = function
  | [] -> Loop.Seq Loop.SNil
  | [st] -> st
  | sts -> Loop.Seq (stmt_list_of_list sts)

let slot_exprs env =
  List.map
    (fun name ->
      match lookup_loop env name with
      | Some idx -> Loop.Var (nat_of_int idx)
      | None -> errorf "internal error: missing slot binding for %s" name)
    (slot_env env)

let const_affine = function
  | Int n -> Some n
  | _ -> None

let const_expr = function
  | IntLit n -> Some n
  | _ -> None

let rec elab_loop_aff env = function
  | Int n -> Loop.Constant (z_of_int n)
  | Name x ->
      begin match lookup_loop env x with
      | Some idx -> Loop.Var (nat_of_int idx)
      | None -> errorf "free affine variable %s" x
      end
  | Add (a, b) -> Loop.make_sum (elab_loop_aff env a) (elab_loop_aff env b)
  | Sub (a, b) ->
      Loop.make_sum (elab_loop_aff env a)
        (Loop.make_mult (z_of_int (-1)) (elab_loop_aff env b))
  | Mul (a, b) ->
      begin match const_affine a, const_affine b with
      | Some k, _ -> Loop.make_mult (z_of_int k) (elab_loop_aff env b)
      | _, Some k -> Loop.make_mult (z_of_int k) (elab_loop_aff env a)
      | None, None -> errorf "non-affine multiplication is not supported"
      end

let rec elab_instr_aff env = function
  | Int n -> Instr.AeConst (z_of_int n)
  | Name x ->
      begin match lookup_slot env x with
      | Some idx -> Instr.AeVar (nat_of_int idx)
      | None -> errorf "free affine variable %s" x
      end
  | Add (a, b) -> Instr.AeAdd (elab_instr_aff env a, elab_instr_aff env b)
  | Sub (a, b) -> Instr.AeSub (elab_instr_aff env a, elab_instr_aff env b)
  | Mul (a, b) ->
      begin match const_affine a, const_affine b with
      | Some k, _ -> Instr.AeMul (z_of_int k, elab_instr_aff env b)
      | _, Some k -> Instr.AeMul (z_of_int k, elab_instr_aff env a)
      | None, None -> errorf "non-affine multiplication is not supported"
      end

let note_memory seen name =
  if List.mem name !seen then () else seen := !seen @ [name]

let elab_access env seen { base; indices } =
  ensure_not_bound env base "memory access";
  note_memory seen base;
  let id = ident_of_string base in
  match indices with
  | [] -> Instr.AcVar id
  | _ -> Instr.AcArr (id, List.map (elab_instr_aff env) indices)

let rec elab_expr env seen = function
  | IntLit n -> Instr.ExConst (z_of_int n)
  | NameRef x ->
      begin match lookup_slot env x with
      | Some idx -> Instr.ExVar (nat_of_int idx)
      | None ->
          note_memory seen x;
          Instr.ExAccess (Instr.AcVar (ident_of_string x))
      end
  | Access a -> Instr.ExAccess (elab_access env seen a)
  | AddE (a, b) -> Instr.ExAdd (elab_expr env seen a, elab_expr env seen b)
  | SubE (a, b) -> Instr.ExSub (elab_expr env seen a, elab_expr env seen b)
  | MulE (a, b) ->
      begin match const_expr a, const_expr b with
      | Some k, _ -> Instr.ExMul (z_of_int k, elab_expr env seen b)
      | _, Some k -> Instr.ExMul (z_of_int k, elab_expr env seen a)
      | None, None -> errorf "non-affine multiplication is not supported in instruction expressions"
      end

let rec elab_test env = function
  | Le (a, b) -> Loop.make_le (elab_loop_aff env a) (elab_loop_aff env b)
  | Eq (a, b) -> Loop.make_eq (elab_loop_aff env a) (elab_loop_aff env b)
  | And (t1, t2) -> Loop.make_and (elab_test env t1) (elab_test env t2)

let rec elab_stmt env seen = function
  | Assign (lhs, rhs) ->
      let lhs' = elab_access env seen lhs in
      let rhs' = elab_expr env seen rhs in
      Loop.Instr (Instr.SAssign (lhs', rhs'), slot_exprs env)
  | If (tst, body) ->
      let body' = stmt_of_list (List.map (elab_stmt env seen) body) in
      Loop.Guard (elab_test env tst, body')
  | For (iter, lb, ub, body) ->
      if List.mem iter (loop_env env)
      then errorf "loop iterator %s shadows an existing loop/context variable" iter;
      let lb' = elab_loop_aff env lb in
      let ub' = elab_loop_aff env ub in
      let env' = { env with loops = env.loops @ [iter] } in
      let body' = stmt_of_list (List.map (elab_stmt env' seen) body) in
      Loop.Loop (lb', ub', body')

let elaborate (prog : program) : IR.Loop.t =
  ensure_unique "context" prog.context;
  let seen_memory = ref [] in
  let env = { params = prog.context; loops = [] } in
  let body = stmt_of_list (List.map (elab_stmt env seen_memory) prog.body) in
  let varctxt = List.map ident_of_string prog.context in
  let vars =
    List.map
      (fun name -> (ident_of_string name, IR.Ty.dummy))
      (dedup (prog.context @ !seen_memory))
  in
  ((body, varctxt), vars)
