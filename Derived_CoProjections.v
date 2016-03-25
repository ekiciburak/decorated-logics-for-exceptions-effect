(**************************************************************************)
(*  This is part of EXCEPTIONS, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Prerequistes Terms Decorations Axioms.
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
  Module Export Derived_CoProjectionsExp := Axioms.Make(M). 

 Definition permut {X Y} : term (X+Y) (Y+X) := copair coproj2 coproj1.
 Definition rcopair {X Y Z} (f: term X Y) (g: term X Z): term X (Y+Z) := copair g f o (@permut Z Y).

 Lemma is_permut X Y: EPURE (@permut X Y).
 Proof. edecorate. Qed.

Lemma is_rcopair: forall k X Y Z (f1: term Z X) (f2: term Z Y), PPG f2 -> is k f1 -> is k f2 -> is k (rcopair f1 f2). (* FIXED *)
Proof. intros k X Y Z f1 f2 H1 H2 H3. induction k; edecorate. Qed.

Lemma s_rcopair_eq: forall X Z Y (f1: term X Y) (f2: term X Z), PPG f2 -> rcopair f1 f2 o coproj1 == f1.
Proof.
    intros X Y' Y f1 f2 H0. unfold rcopair, permut. rewrite <- assoc.
    cut (copair coproj2 coproj1 o coproj1 == (@coproj2 Y' Y)).
      intro H1. rewrite H1.
      apply s_lcopair_eq; exact H0.
      (*1st cut*)
      apply wtos; [edecorate| edecorate| ]. apply w_lcopair_eq; edecorate.
Qed.

Lemma w_rcopair_eq: forall X Z Y (f1: term X Y) (f2: term X Z), PPG f2 -> rcopair f1 f2 o coproj2 ~ f2.
Proof.
    intros X Y' Y f1 f2 H. unfold rcopair, permut. rewrite <- assoc.
    rewrite s_lcopair_eq;[| edecorate]. rewrite w_lcopair_eq;[reflexivity| edecorate].
Qed.

Lemma lcopair_u: forall X Y Y' (f1 f2: term X (Y' + Y)),
  (f1 o coproj1 ~ f2 o coproj1) /\ (f1 o coproj2 == f2 o coproj2) -> f1 == f2.
Proof.
    intros X Y Y' f1 f2 (H0&H1). apply eeffect.
    (* f 1 ◦ [ ] ≡ f 2 ◦ [ ] *)
    cut((@coproj2 Y' Y) o (@empty Y) == (@empty (Y' + Y))).
      intro H2. rewrite <- H2.
      setoid_rewrite assoc. rewrite H1. reflexivity. 
      (* 1st cut *)
      setoid_rewrite s_empty; [reflexivity| edecorate].
    (* f 1 ∼ f 2 *)
    apply lcopair_ueq. exact H0. apply stow. exact H1.
Qed.

Lemma rcopair_u: forall X Y Y' (f1 f2: term X (Y' + Y)),
   (f1 o coproj1 == f2 o coproj1) /\ (f1 o coproj2 ~ f2 o coproj2) -> f1 == f2.
Proof.
     intros X Y Y' f1 f2 (H0&H1). apply eeffect.
     (* f 1 ◦ [ ] ≡ f 2 ◦ [ ] *)
     cut((@coproj1 Y' Y) o (@empty Y') == (@empty (Y' + Y))).
       intro H2. rewrite <- H2.
       setoid_rewrite assoc. rewrite H0. reflexivity.
       (* 1st cut *)
       setoid_rewrite s_empty; [reflexivity| edecorate].
     (* f 1 ∼ f 2 *)
     apply lcopair_ueq. apply stow. exact H0. exact H1.
Qed.

(* -------------------- End of Derived Pair Projections -------------------- *)

End Make.

