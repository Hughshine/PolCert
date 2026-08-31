Require Import List.
Require Import ZArith.
Require Import SInstr.
Require Import SPolIRs.
Require Import ExtractorFrontend.
Require Import Result.
Import List.ListNotations.
Open Scope Z_scope.

Module E := ExtractorFrontend SPolIRs.
Module Loop := SPolIRs.Loop.
Module PolyLang := SPolIRs.PolyLang.

Definition sample_instr : SInstr.t :=
  SInstr.SAssign
    (SInstr.AcArr 1%positive [SInstr.AeVar 0])
    (SInstr.ExAdd
       (SInstr.ExAccess (SInstr.AcArr 2%positive [SInstr.AeVar 0]))
       (SInstr.ExConst 1)).

Definition sample_stmt : Loop.stmt :=
  Loop.Loop (Loop.Constant 0) (Loop.Constant 4)
    (Loop.Instr sample_instr [Loop.Var 0]).

Definition sample_loop : Loop.t :=
  ((sample_stmt, []), [(1%positive, tt); (2%positive, tt)]).

Example sample_waccess_ok :
  SInstr.waccess sample_instr = Some [(1%positive, [([1%Z], 0%Z)])].
Proof. reflexivity. Qed.

Example sample_raccess_ok :
  SInstr.raccess sample_instr = Some [(2%positive, [([1%Z], 0%Z)])].
Proof. reflexivity. Qed.

Example sample_extractor_accepts :
  match E.extractor sample_loop with
  | Okk _ => true
  | Err _ => false
  end = true.
Proof. reflexivity. Qed.

Example sample_extracted_openscop :
  match E.extractor sample_loop with
  | Okk pol =>
      match PolyLang.to_openscop pol with
      | Some _ => true
      | None => false
      end
  | Err _ => false
  end = true.
Proof. reflexivity. Qed.
