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
  | NameRef of string
  | Access of access
  | AddE of expr * expr
  | SubE of expr * expr
  | MulE of expr * expr

type test =
  | Le of affine * affine
  | Eq of affine * affine
  | And of test * test

type stmt =
  | Assign of access * expr
  | If of test * stmt list
  | For of string * affine * affine * stmt list

type program = {
  context : string list;
  body : stmt list;
}
