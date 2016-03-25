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
Require Prerequistes Terms Decorations Axioms Derived_CoProjections. 
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
  Module Export Derived_CoProductsExp := Derived_CoProjections.Make(M). 

Definition lcoprod {X1 Y1 X2 Y2} (f1: term X1 X2) (f2: term Y1 Y2) : term (X1 + Y1) (X2 + Y2) := copair (coproj1 o f1) (coproj2 o f2).

Definition rcoprod {X Y X' Y'} (f1: term X X') (f2: term Y Y') : term (X+Y) (X'+Y') := rcopair (coproj1 o f1) (coproj2 o f2).

Lemma is_lcoprod: forall k X' X Y' Y (f1: term X X') (f2: term Y Y'), PPG f1 -> is k f1 -> is k f2 -> is k (lcoprod f1 f2). (* FIXED *)
Proof. intros k X' X Y' Y f1 f2 H1 H2 H3. induction k; edecorate. Qed.

Lemma is_rcoprod: forall k X' X Y' Y (f1: term X X') (f2: term Y Y'), PPG f2 -> is k f1 -> is k f2 -> is k (rcoprod f1 f2). (* FIXED *)
Proof. intros k X' X Y' Y f1 g2 H1 H2 H3. induction k; edecorate. Qed.

Lemma w_lcoprod_eq: forall X1 X2 Y1 Y2 (f: term X1 X2) (g: term Y1 Y2), PPG f -> (lcoprod f g) o coproj1 ~ coproj1 o f.
Proof. intros X1 X2 Y1 Y2 f g H. apply w_lcopair_eq; edecorate. Qed.

Lemma s_lcoprod_eq: forall X1 X2 Y1 Y2 (f: term X1 X2) (g: term Y1 Y2), PPG f -> (lcoprod f g) o coproj2 == coproj2 o g.
Proof. intros X1 X2 Y1 Y2 f g H. apply s_lcopair_eq; edecorate. Qed.

Lemma s_rcoprod_eq: forall X1 X2 Y1 Y2 (f: term X1 X2) (g: term Y1 Y2), PPG g -> (rcoprod f g) o coproj1 == coproj1 o f.
Proof. intros X1 X2 Y1 Y2 f g H. apply s_rcopair_eq; edecorate. Qed.

Lemma w_rcoprod_eq: forall X1 X2 Y1 Y2 (f: term X1 X2) (g: term Y1 Y2), PPG g -> (rcoprod f g) o coproj2 ~ coproj2 o g.
Proof. intros X1 X2 Y1 Y2 f g H. apply w_rcopair_eq; edecorate. Qed.

Lemma lcoprod_u: forall X1 X2 Y1 Y2 (f1 f2: term (Y2 + Y1) (X2 + X1)), (f1 o coproj1 ~ f2 o coproj1) /\ (f1 o coproj2 == f2 o coproj2) -> f1 == f2.
Proof. intros X1 X2 Y1 Y2 f1 f2 (H0&H1). apply lcopair_u. split; [exact H0| exact H1]. Qed.

Lemma rcoprod_u: forall X1 X2 Y1 Y2 (f1 f2: term (Y2 + Y1) (X2 + X1)), (f1 o coproj1 == f2 o coproj1) /\ (f1 o coproj2 ~ f2 o coproj2) -> f1 == f2.
Proof. intros X1 X2 Y1 Y2 f1 f2 (H0&H1). apply rcopair_u. split; [exact H0| exact H1]. Qed.

End Make.

