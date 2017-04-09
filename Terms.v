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
Require Prerequistes.

Module Make(Import M: Prerequistes.T).

(** the core language of exceptions (L_exc) *)
 Inductive term: Type -> Type -> Type :=  
  | comp:   forall {X Y Z: Type}, term X Y -> term Y Z -> term X Z
  | copair: forall {X Y Z: Type}, term Z X -> term Z Y -> term Z (X+Y) 
  | downcast: forall {X Y: Type} (f: term X Y), term X Y 
  | tpure:  forall {X Y: Type}, (X -> Y) -> term Y X
  | tag: forall t:EName, term Empty_set (Val t)	
  | untag: forall t:EName, term (Val t) Empty_set.

 Infix "o" := comp (at level 70).

 Definition id  {X: Type}       : term X X         := tpure id.
 Definition in1 {X Y}       : term (X+Y) X         := tpure inl.
 Definition in2 {X Y}       : term (X+Y) Y         := tpure inr.
 Definition emptyfun (X: Type) (e: Empty_set) : X  := match e with end.
 Definition empty X: (term X Empty_set)            := tpure (emptyfun X).

(** programmer's language *)
 Inductive termpl: Type -> Type -> Type := 
  | pl_tpure: forall {X Y: Type}, (X -> Y) -> termpl Y X 
  | pl_comp: forall {X Y Z: Type}, termpl X Y -> termpl Y Z -> termpl X Z 
  | throw: forall {X} (e: EName), termpl X (Val e)
  | try_catch: forall {X Y} (e: EName), termpl Y X -> termpl Y (Val e) -> termpl Y X.

 Notation "a 'O' b" := (pl_comp a b) (at level 70).

 Definition pl_empty X: termpl X Empty_set := pl_tpure (emptyfun X).
 Definition pl_id {X: Type} : termpl X X := pl_tpure (Datatypes.id).

(** translation from programmers' language into the core language *)
 Fixpoint translate X Y (t: termpl X Y): (term X Y) :=
  match t with
    | @pl_tpure X Y f      => tpure f
    | @pl_comp _ _ _ a b   => (translate _ _ a) o (translate _ _ b) 
    | @throw Y e           => (@empty Y) o (tag e)
    | @try_catch X Y e a b => downcast(copair (@id Y) ((@translate _ _ b) o untag e) o in1 o (@translate _ _ a))
  end.


End Make.

