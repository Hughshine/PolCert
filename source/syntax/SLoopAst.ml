type affine =
  | Int of int
  | Name of string
  | Add of affine * affine
  | Sub of affine * affine
  | Mul of affine * affine

type access = {
  base : string;
  indices : affine list;
}

type expr =
  | IntLit of int
  | FloatLit of string
  | NameRef of string
  | Access of access
  | AddE of expr * expr
  | SubE of expr * expr
  | MulE of expr * expr
  | DivE of expr * expr
  | LeE of expr * expr
  | EqE of expr * expr
  | AndE of expr * expr
  | CallE of string * expr list
  | CondE of expr * expr * expr

type test =
  | Le of affine * affine
  | Eq of affine * affine
  | And of test * test

type stmt =
  | Assign of access * expr
  | If of test * stmt list
  | For of string * affine * affine * affine option * stmt list

type program = {
  context : string list;
  body : stmt list;
}
