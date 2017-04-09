(**************************************************************************)
(*  This is part of EXCEPTIONS, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Prerequistes Terms Decorations.
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
  Module Export AxiomsExp := Decorations.Make(M). 

 Reserved Notation "x == y" (at level 80).
 Reserved Notation "x ~ y" (at level 80).

 Definition pure_id X Y (x y: term X Y) := EPURE x /\ x = y.
 Definition idem    X Y (x y: term X Y) := x = y.
 Definition not_ (A:Prop) := A -> False.
 
 Inductive strong: forall X Y, relation (term X Y) := 
 | refl: forall X Y (f: term X Y), f == f
 | sym: forall X Y, Symmetric (@strong X Y)
 | trans: forall X Y, Transitive (@strong X Y)
 | replsubs: forall X Y Z, Proper (@strong X Y ==> @strong Y Z ==> @strong X Z) comp 
 | ids: forall X Y (f: term X Y), f o id == f
 | idt: forall X Y (f: term X Y), id o f == f
 | assoc: forall X Y Z T (f: term X Y) (g: term Y Z) (h: term Z T), f o (g o h) == (f o g) o h
 | wtos: forall  X Y (f g: term X Y), PPG f -> PPG g -> f ~ g -> f == g
 | s_lcopair_eq: forall X X' Y (f1: term Y X) (f2: term Y X'), PPG f1 -> (copair f1 f2) o in2 == f2
 | eeffect: forall X Y (f g: term Y X), (f o (@empty X) == g o (@empty X)) -> f ~ g -> f == g (* effect measure - Dumas et al.'12 *)
 | elocal_global: forall X (f g: term X Empty_set), (forall t: EName, f o tag t ~ g o tag t) -> f == g (* dual to observation *)
 | tcomp: forall X Y Z (f: Z -> Y) (g: Y -> X), tpure (compose g f) == tpure g o tpure f
 with weak: forall X Y, relation (term X Y) := 
 | wsym: forall X Y, Symmetric (@weak X Y)
 | wtrans: forall X Y, Transitive (@weak X Y)
 | wrepl : forall A B C, Proper (@idem C B ==> @weak B A ==> @weak C A) comp
 | pwsubs : forall A B C, Proper (@weak C B ==> @pure_id B A ==> @weak C A) comp
 | stow: forall  X Y (f g: term X Y), f == g -> f ~ g
 | w_lcopair_eq: forall X X' Y (f1: term Y X) (f2: term Y X'), PPG f1 -> (copair f1 f2) o in1 ~ f1  
 | w_empty: forall X (f: term X Empty_set), f ~ (@empty X)
 | w_downcast: forall X Y (f: term X Y), f ~ (@downcast X Y f)	
 | eax1: forall t: EName, untag t o tag t ~ (@id (Val t))
 | eax2: forall t1 t2: EName, t1 <> t2 -> untag t2 o tag t1 ~ (@empty (Val t2)) o tag t1
 | lcopair_ueq: forall  X X' Y (f g: term Y (X+X')), (f o in1 ~ g o in1) -> (f o in2 ~ g o in2) -> f ~ g
   where "x == y" := (strong x y)
   and "x ~ y" := (weak x y).

 Instance strong_is_equivalence X Y: Equivalence (@strong X Y).
 Proof. constructor; intro. apply refl. apply sym. apply trans. Qed.

 Instance weak_is_equivalence X Y: Equivalence (@weak X Y).
 Proof. constructor; intro. apply stow. apply refl. intros. apply wsym. assumption. apply wtrans. Qed.

 Instance strong_is_weak_equivalence: forall X Y, subrelation (@strong X Y) (@weak X Y).
 Proof. constructor. apply stow,sym. assumption. Qed.

 Lemma s_empty: forall X (f: term X Empty_set), (PPG f) -> f == (@empty X).
 Proof. intros X f H. apply wtos; [exact H| edecorate| apply w_empty]. Qed.

 Existing Instance wrepl.
 Existing Instance pwsubs.
 Existing Instance replsubs.

 Goal forall X Y Z (g: term Z Y) (f f': term Y X), f ~ f' -> g o f ~ g o f'.
 Proof. intros X Y Z g f f' H0. setoid_rewrite <- H0. reflexivity. Qed.

 Goal forall X Y Z (g: term Y X) (f f': term Z Y), f ~ f' -> EPURE g -> f o g ~ f' o g.
 Proof.  intros X Y Z g f f' H0 H1. apply pwsubs. exact H0. unfold pure_id. split. exact H1. reflexivity. Qed. 

 Reserved Notation "x *== y" (at level 80).

 Inductive pl_strong: forall X Y, relation (termpl X Y) := 
 | pl_refl: forall X Y (f: termpl X Y), f *== f 
 | pl_assoc: forall X Y Z T (f: termpl X Y) (g: termpl Y Z) (h: termpl Z T), f O (g O h) *== (f O g) O h
 | pl_ids: forall X Y (f: termpl X Y), f O pl_id  *== f
 | pl_idt: forall X Y (f: termpl X Y), pl_id O f  *== f
 | pl_s_empty: forall X (f: termpl X Empty_set), f  *== (@pl_empty X)  
 | pl_replsubs: forall X Y Z, Proper (@pl_strong X Y ==> @pl_strong Y Z  ==> @pl_strong X Z) (pl_comp) 
     (*for throw and try/catch*)
 | ppt : forall X Y e (a: termpl X Y), a O (@throw Y e)  *== (@throw X e)   
 | rcv : forall X Y e (u1 u2: termpl (Val e) Y), (@throw X e) O u1  *== (@throw X e) O u2 -> u1  *== u2 
 | try : forall X Y e (a1 a2: termpl X Y) (b: termpl X (Val e)), a1 *== a2 -> try_catch e a1 b  *== try_catch e a2 b (* FIXED *)
(* | try: forall X Y e, Proper (@pl_strong X Y  ==> @pl_strong X (Val e)  ==> @pl_strong X Y) (try_catch e) *)
 | try0: forall X Y e (u: termpl X Y) (b: termpl X (Val e)), PL_EPURE u -> try_catch e u b  *== u
 | try1: forall X Y e (u: termpl (Val e) Y) (b: termpl X (Val e)), PL_EPURE u ->
 		try_catch e ((@throw X e) O u) b  *== b O u
 | try2: forall X Y e f (u: termpl (Val f) X) (b: termpl Y (Val e)),  e <> f -> PL_EPURE u ->
 		try_catch e ((@throw Y f) O u) b  *== (@throw Y f) O u
 | pl_sym: forall X Y, Symmetric (@pl_strong X Y)
 | pl_trans: forall X Y, Transitive (@pl_strong X Y)
 | pl_tcomp: forall X Y Z (f: Z -> Y) (g: Y -> X), pl_tpure (compose g f) *== pl_tpure g O pl_tpure f
   where "x  *== y" := (pl_strong x y).

 Instance pl_strong_is_equivalence X Y: Equivalence (@pl_strong X Y).
 Proof. constructor; intro. apply pl_refl. apply pl_sym. apply pl_trans. Qed.


 Existing Instance pl_replsubs.
 (*Existing Instance try.*)

End Make.
