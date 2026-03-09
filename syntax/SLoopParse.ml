open SLoopAst

type token_kind =
  | KContext
  | KFor
  | KIf
  | KIn
  | KRange
  | Ident of string
  | Int of int
  | Float of string
  | LParen
  | RParen
  | LBrace
  | RBrace
  | LBracket
  | RBracket
  | Comma
  | Semi
  | Assign
  | Plus
  | Minus
  | Star
  | Slash
  | Le
  | EqEq
  | AndAnd
  | Question
  | Colon
  | Eof

type token = {
  kind : token_kind;
  pos : int;
}

exception Error of int * string

let error pos msg = raise (Error (pos, msg))

let string_of_token_kind = function
  | KContext -> "context"
  | KFor -> "for"
  | KIf -> "if"
  | KIn -> "in"
  | KRange -> "range"
  | Ident s -> Printf.sprintf "identifier(%s)" s
  | Int n -> Printf.sprintf "int(%d)" n
  | Float s -> Printf.sprintf "float(%s)" s
  | LParen -> "("
  | RParen -> ")"
  | LBrace -> "{"
  | RBrace -> "}"
  | LBracket -> "["
  | RBracket -> "]"
  | Comma -> ","
  | Semi -> ";"
  | Assign -> "="
  | Plus -> "+"
  | Minus -> "-"
  | Star -> "*"
  | Slash -> "/"
  | Le -> "<="
  | EqEq -> "=="
  | AndAnd -> "&&"
  | Question -> "?"
  | Colon -> ":"
  | Eof -> "<eof>"

let is_space = function
  | ' ' | '\t' | '\r' | '\n' -> true
  | _ -> false

let is_digit c = c >= '0' && c <= '9'

let is_ident_start = function
  | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
  | _ -> false

let is_ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
  | _ -> false

let keyword_or_ident s =
  match s with
  | "context" -> KContext
  | "for" -> KFor
  | "if" -> KIf
  | "in" -> KIn
  | "range" -> KRange
  | _ -> Ident s

let lex input =
  let len = String.length input in
  let rec skip_block_comment i =
    if i + 1 >= len then error i "unterminated block comment";
    if input.[i] = '*' && input.[i + 1] = '/'
    then i + 2
    else skip_block_comment (i + 1)
  in
  let rec skip i =
    if i >= len then i
    else if is_space input.[i] then skip (i + 1)
    else if i + 1 < len && input.[i] = '/' && input.[i + 1] = '/'
    then skip_line (i + 2)
    else if i + 1 < len && input.[i] = '/' && input.[i + 1] = '*'
    then skip (skip_block_comment (i + 2))
    else i
  and skip_line i =
    if i >= len then i
    else if input.[i] = '\n' then skip (i + 1)
    else skip_line (i + 1)
  in
  let rec ident_end i =
    if i < len && is_ident_char input.[i] then ident_end (i + 1) else i
  in
  let rec number_end i seen_dot seen_digit =
    if i >= len then (i, seen_dot, seen_digit)
    else if is_digit input.[i] then number_end (i + 1) seen_dot true
    else if input.[i] = '.' && not seen_dot then number_end (i + 1) true seen_digit
    else (i, seen_dot, seen_digit)
  in
  let rec go i acc =
    let i = skip i in
    if i >= len then List.rev ({ kind = Eof; pos = len } :: acc)
    else
      let two c1 c2 tok =
        if i + 1 < len && input.[i] = c1 && input.[i + 1] = c2
        then Some { kind = tok; pos = i }
        else None
      in
      match two '<' '=' Le with
      | Some tok -> go (i + 2) (tok :: acc)
      | None ->
          match two '=' '=' EqEq with
          | Some tok -> go (i + 2) (tok :: acc)
          | None ->
              match two '&' '&' AndAnd with
              | Some tok -> go (i + 2) (tok :: acc)
              | None ->
                  begin match input.[i] with
                  | '(' -> go (i + 1) ({ kind = LParen; pos = i } :: acc)
                  | ')' -> go (i + 1) ({ kind = RParen; pos = i } :: acc)
                  | '{' -> go (i + 1) ({ kind = LBrace; pos = i } :: acc)
                  | '}' -> go (i + 1) ({ kind = RBrace; pos = i } :: acc)
                  | '[' -> go (i + 1) ({ kind = LBracket; pos = i } :: acc)
                  | ']' -> go (i + 1) ({ kind = RBracket; pos = i } :: acc)
                  | ',' -> go (i + 1) ({ kind = Comma; pos = i } :: acc)
                  | ';' -> go (i + 1) ({ kind = Semi; pos = i } :: acc)
                  | '=' -> go (i + 1) ({ kind = Assign; pos = i } :: acc)
                  | '+' -> go (i + 1) ({ kind = Plus; pos = i } :: acc)
                  | '-' -> go (i + 1) ({ kind = Minus; pos = i } :: acc)
                  | '*' -> go (i + 1) ({ kind = Star; pos = i } :: acc)
                  | '/' -> go (i + 1) ({ kind = Slash; pos = i } :: acc)
                  | '?' -> go (i + 1) ({ kind = Question; pos = i } :: acc)
                  | ':' -> go (i + 1) ({ kind = Colon; pos = i } :: acc)
                  | c when is_ident_start c ->
                      let j = ident_end (i + 1) in
                      let s = String.sub input i (j - i) in
                      go j ({ kind = keyword_or_ident s; pos = i } :: acc)
                  | c when is_digit c || (c = '.' && i + 1 < len && is_digit input.[i + 1]) ->
                      let j, seen_dot, seen_digit = number_end (i + 1) (c = '.') (is_digit c) in
                      if not seen_digit then error i "malformed numeric literal";
                      let s = String.sub input i (j - i) in
                      if seen_dot then
                        go j ({ kind = Float s; pos = i } :: acc)
                      else
                        let n =
                          match int_of_string_opt s with
                          | Some n -> n
                          | None -> error i (Printf.sprintf "integer literal out of range: %s" s)
                        in
                        go j ({ kind = Int n; pos = i } :: acc)
                  | c -> error i (Printf.sprintf "unexpected character %C" c)
                  end
  in
  go 0 []

type stream = {
  tokens : token array;
  mutable idx : int;
}

let make_stream toks = { tokens = Array.of_list toks; idx = 0 }

let peek st =
  if st.idx < Array.length st.tokens then st.tokens.(st.idx)
  else { kind = Eof; pos = Array.length st.tokens }

let bump st =
  let tok = peek st in
  st.idx <- st.idx + 1;
  tok

let accept st pred =
  let tok = peek st in
  if pred tok.kind then Some (bump st) else None

let expect st pred expected =
  let tok = peek st in
  if pred tok.kind then bump st
  else error tok.pos (Printf.sprintf "expected %s, got %s" expected (string_of_token_kind tok.kind))

let expect_ident st =
  match bump st with
  | { kind = Ident s; _ } -> s
  | tok -> error tok.pos (Printf.sprintf "expected identifier, got %s" (string_of_token_kind tok.kind))

let expect_token st kind expected =
  ignore (expect st (fun k -> k = kind) expected)

let rec parse_program st =
  let context =
    match accept st (function KContext -> true | _ -> false) with
    | None -> []
    | Some _ -> parse_context_decl st
  in
  let body = parse_stmt_seq_until st (function Eof -> true | _ -> false) in
  ignore (expect st (function Eof -> true | _ -> false) "end of file");
  { context; body }

and parse_context_decl st =
  expect_token st LParen "( after context";
  let names = parse_ident_list st in
  expect_token st RParen ") after context list";
  expect_token st Semi "; after context declaration";
  names

and parse_ident_list st =
  match peek st with
  | { kind = RParen; _ } -> []
  | _ ->
      let rec go acc =
        let name = expect_ident st in
        match accept st (function Comma -> true | _ -> false) with
        | None -> List.rev (name :: acc)
        | Some _ -> go (name :: acc)
      in
      go []

and parse_block st =
  expect_token st LBrace "{";
  let body = parse_stmt_seq_until st (function RBrace -> true | _ -> false) in
  expect_token st RBrace "}";
  body

and parse_stmt_seq_until st stop =
  let rec go acc =
    if stop (peek st).kind then List.rev acc else go (parse_stmt st :: acc)
  in
  go []

and parse_stmt st =
  match peek st with
  | { kind = KFor; _ } -> parse_for st
  | { kind = KIf; _ } -> parse_if st
  | _ -> parse_assign st

and parse_for st =
  ignore (bump st);
  let iter = expect_ident st in
  ignore (expect st (function KIn -> true | _ -> false) "in");
  ignore (expect st (function KRange -> true | _ -> false) "range");
  expect_token st LParen "( after range";
  let lb = parse_affine st in
  expect_token st Comma ", in range";
  let ub = parse_affine st in
  expect_token st RParen ") after range";
  let body = parse_block st in
  For (iter, lb, ub, body)

and parse_if st =
  ignore (bump st);
  expect_token st LParen "( after if";
  let tst = parse_test st in
  expect_token st RParen ") after if condition";
  let body = parse_block st in
  If (tst, body)

and parse_assign st =
  let lhs = parse_access st in
  expect_token st Assign "=";
  let rhs = parse_expr st in
  expect_token st Semi ";";
  Assign (lhs, rhs)

and parse_access st =
  let base = expect_ident st in
  parse_access_after_base st base

and parse_access_after_base st base =
  let rec indices acc =
    match accept st (function LBracket -> true | _ -> false) with
    | None -> { base; indices = List.rev acc }
    | Some _ ->
        let idx = parse_affine st in
        expect_token st RBracket "]";
        indices (idx :: acc)
  in
  indices []

and parse_test st =
  let lhs = parse_cmp st in
  let rec more acc =
    match accept st (function AndAnd -> true | _ -> false) with
    | None -> acc
    | Some _ -> more (And (acc, parse_cmp st))
  in
  more lhs

and parse_cmp st =
  let lhs = parse_affine st in
  match bump st with
  | { kind = Le; _ } -> Le (lhs, parse_affine st)
  | { kind = EqEq; _ } -> Eq (lhs, parse_affine st)
  | tok -> error tok.pos (Printf.sprintf "expected <= or ==, got %s" (string_of_token_kind tok.kind))

and parse_affine st = parse_affine_add st

and parse_affine_add st =
  let lhs = parse_affine_mul st in
  let rec more acc =
    match peek st with
    | { kind = Plus; _ } -> ignore (bump st); more (Add (acc, parse_affine_mul st))
    | { kind = Minus; _ } -> ignore (bump st); more (Sub (acc, parse_affine_mul st))
    | _ -> acc
  in
  more lhs

and parse_affine_mul st =
  let lhs = parse_affine_atom st in
  let rec more acc =
    match peek st with
    | { kind = Star; _ } -> ignore (bump st); more (Mul (acc, parse_affine_atom st))
    | _ -> acc
  in
  more lhs

and parse_affine_atom st =
  match bump st with
  | { kind = Int n; _ } -> Int n
  | { kind = Ident s; _ } -> Name s
  | { kind = Minus; _ } -> Mul (Int (-1), parse_affine_atom st)
  | { kind = LParen; _ } ->
      let e = parse_affine st in
      expect_token st RParen ")";
      e
  | tok -> error tok.pos (Printf.sprintf "unexpected token in affine expression: %s" (string_of_token_kind tok.kind))

and parse_expr st = parse_expr_ternary st

and parse_expr_ternary st =
  let lhs = parse_expr_and st in
  match accept st (function Question -> true | _ -> false) with
  | None -> lhs
  | Some _ ->
      let then_e = parse_expr st in
      expect_token st Colon ":";
      let else_e = parse_expr st in
      CondE (lhs, then_e, else_e)

and parse_expr_and st =
  let lhs = parse_expr_cmp st in
  let rec more acc =
    match peek st with
    | { kind = AndAnd; _ } -> ignore (bump st); more (AndE (acc, parse_expr_cmp st))
    | _ -> acc
  in
  more lhs

and parse_expr_cmp st =
  let lhs = parse_expr_add st in
  match peek st with
  | { kind = Le; _ } -> ignore (bump st); LeE (lhs, parse_expr_add st)
  | { kind = EqEq; _ } -> ignore (bump st); EqE (lhs, parse_expr_add st)
  | _ -> lhs

and parse_expr_add st =
  let lhs = parse_expr_mul st in
  let rec more acc =
    match peek st with
    | { kind = Plus; _ } -> ignore (bump st); more (AddE (acc, parse_expr_mul st))
    | { kind = Minus; _ } -> ignore (bump st); more (SubE (acc, parse_expr_mul st))
    | _ -> acc
  in
  more lhs

and parse_expr_mul st =
  let lhs = parse_expr_atom st in
  let rec more acc =
    match peek st with
    | { kind = Star; _ } -> ignore (bump st); more (MulE (acc, parse_expr_atom st))
    | { kind = Slash; _ } -> ignore (bump st); more (DivE (acc, parse_expr_atom st))
    | _ -> acc
  in
  more lhs

and parse_expr_atom st =
  match bump st with
  | { kind = Int n; _ } -> IntLit n
  | { kind = Float s; _ } -> FloatLit s
  | { kind = Ident s; _ } ->
      if Option.is_some (accept st (function LParen -> true | _ -> false)) then begin
        let rec args acc =
          match peek st with
          | { kind = RParen; _ } ->
              ignore (bump st);
              List.rev acc
          | _ ->
              let arg = parse_expr st in
              begin match peek st with
              | { kind = Comma; _ } -> ignore (bump st); args (arg :: acc)
              | { kind = RParen; _ } -> ignore (bump st); List.rev (arg :: acc)
              | tok -> error tok.pos (Printf.sprintf "expected , or ), got %s" (string_of_token_kind tok.kind))
              end
        in
        CallE (s, args [])
      end else if Option.is_some (accept st (function LBracket -> true | _ -> false)) then begin
        st.idx <- st.idx - 1;
        Access (parse_access_after_base st s)
      end else NameRef s
  | { kind = Minus; _ } -> MulE (IntLit (-1), parse_expr_atom st)
  | { kind = LParen; _ } ->
      let e = parse_expr st in
      expect_token st RParen ")";
      e
  | tok -> error tok.pos (Printf.sprintf "unexpected token in expression: %s" (string_of_token_kind tok.kind))

let parse_string input =
  let st = make_stream (lex input) in
  parse_program st

let parse_file filename =
  let ic = open_in filename in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () ->
      let len = in_channel_length ic in
      let input = really_input_string ic len in
      parse_string input)
