Require Import List.
Require Import ZArith.
Require Import String.
Require Import AST.
Require Import Result.
Require Import Extractor.
Require Import TPolIRs.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Module E := Extractor TPolIRs.
Module Loop := TPolIRs.Loop.
Module PolyLang := TPolIRs.PolyLang.
Module Instr := TPolIRs.Instr.

Definition vars1 : list (AST.ident * Instr.Ty.t) :=
  [(1%positive, tt)].

Definition vars2 : list (AST.ident * Instr.Ty.t) :=
  [(1%positive, tt); (2%positive, tt)].

Definition affine_instr (es: list Loop.expr) : Loop.stmt :=
  Loop.Instr Instr.dummy_instr es.

Definition nested_seq_stmt : Loop.stmt :=
  Loop.Loop (Loop.Constant 0) (Loop.Constant 4)
    (Loop.Loop (Loop.Constant 0) (Loop.Constant 8)
      (Loop.Seq
        (Loop.SCons
          (affine_instr [Loop.Var 1; Loop.Var 0])
          (Loop.SCons
            (affine_instr [Loop.Sum (Loop.Var 1) (Loop.Constant 1); Loop.Var 0])
            Loop.SNil)))).

Definition nested_seq_prog : Loop.t :=
  (nested_seq_stmt, [], vars2).

Definition affine_guard_stmt : Loop.stmt :=
  Loop.Loop (Loop.Constant 0) (Loop.Constant 8)
    (Loop.Guard
      (Loop.And
        (Loop.LE (Loop.Var 0) (Loop.Constant 6))
        (Loop.EQ
          (Loop.Sum (Loop.Var 0) (Loop.Constant 1))
          (Loop.Sum (Loop.Constant 1) (Loop.Var 0))))
      (affine_instr [Loop.Var 0])).

Definition affine_guard_prog : Loop.t :=
  (affine_guard_stmt, [], vars1).

Definition or_guard_prog : Loop.t :=
  (Loop.Guard
     (Loop.Or
       (Loop.LE (Loop.Constant 0) (Loop.Constant 1))
       (Loop.EQ (Loop.Constant 2) (Loop.Constant 2)))
     (affine_instr []),
   [], []).

Definition not_guard_prog : Loop.t :=
  (Loop.Guard
     (Loop.Not (Loop.LE (Loop.Constant 0) (Loop.Constant 1)))
     (affine_instr []),
   [], []).

Definition div_bound_prog : Loop.t :=
  (Loop.Loop (Loop.Constant 0) (Loop.Div (Loop.Constant 8) 2) (affine_instr []),
   [], []).

Definition max_instr_expr_prog : Loop.t :=
  (affine_instr [Loop.Max (Loop.Constant 0) (Loop.Constant 1)], [], []).

Example extractor_accepts_nested_seq_shape :
  match E.extractor nested_seq_prog with
  | Okk (pis, _, _) =>
      Datatypes.length pis = 2%nat /\
      map PolyLang.pi_depth pis = [2%nat; 2%nat] /\
      map (fun pi => Datatypes.length (PolyLang.pi_poly pi)) pis = [4%nat; 4%nat] /\
      map (fun pi => Datatypes.length (PolyLang.pi_schedule pi)) pis = [3%nat; 3%nat] /\
      map (fun pi => Datatypes.length (PolyLang.pi_transformation pi)) pis = [2%nat; 2%nat] /\
      map PolyLang.pi_waccess pis = [[]; []] /\
      map PolyLang.pi_raccess pis = [[]; []]
  | Err _ => False
  end.
Proof.
  vm_compute.
  repeat split.
Qed.

Example extract_stmt_translates_nested_seq :
  match E.extract_stmt nested_seq_stmt [] 0%nat 0%nat [] with
  | Okk pis =>
      Datatypes.length pis = 2%nat /\
      map PolyLang.pi_depth pis = [2%nat; 2%nat] /\
      map (fun pi => Datatypes.length (PolyLang.pi_poly pi)) pis = [4%nat; 4%nat]
  | Err _ => False
  end.
Proof.
  vm_compute.
  repeat split.
Qed.

Example extractor_accepts_affine_guard_shape :
  match E.extractor affine_guard_prog with
  | Okk (pis, _, _) =>
      Datatypes.length pis = 1%nat /\
      map PolyLang.pi_depth pis = [1%nat] /\
      map (fun pi => Datatypes.length (PolyLang.pi_schedule pi)) pis = [1%nat] /\
      map PolyLang.pi_waccess pis = [[]] /\
      map PolyLang.pi_raccess pis = [[]]
  | Err _ => False
  end.
Proof.
  vm_compute.
  repeat split.
Qed.

Example extractor_rejects_or_guard :
  E.extractor or_guard_prog = Err "Extractor rejected non-affine SCoP fragment".
Proof.
  vm_compute.
  reflexivity.
Qed.

Example extractor_rejects_not_guard :
  E.extractor not_guard_prog = Err "Extractor rejected non-affine SCoP fragment".
Proof.
  vm_compute.
  reflexivity.
Qed.

Example extractor_rejects_div_bound :
  E.extractor div_bound_prog = Err "Extractor rejected non-affine SCoP fragment".
Proof.
  vm_compute.
  reflexivity.
Qed.

Example extractor_rejects_non_affine_instr_expr :
  E.extractor max_instr_expr_prog = Err "Extractor rejected non-affine SCoP fragment".
Proof.
  vm_compute.
  reflexivity.
Qed.
