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
Require Prerequistes Terms.
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
  Module Export DecorationsExp := Terms.Make(M). 

 Inductive kind := epure | ppg | ctc. 

 Inductive is: kind -> forall X Y, term X Y -> Prop :=
 | is_tpure: forall X Y (f: X -> Y), is epure (@tpure X Y f)
 | is_comp: forall k X Y Z (f: term X Y) (g: term Y Z), is k f -> is k g -> is k (f o g)
 | is_copair: forall k X Y Z (f: term Z X) (g: term Z Y), is ppg f -> is k f -> is k g -> is k (copair f g)  (* FIXED *)
 | is_downcast: forall X Y (f: term X Y), is ppg (@downcast X Y f)	
 | is_tag: forall t, is ppg (tag t)	
 | is_untag: forall t, is ctc (untag t)
 | is_epure_ppg: forall X Y (f: term X Y), is epure f -> is ppg f 
 | is_ppg_ctc: forall X Y  (f: term X Y), is ppg f -> is ctc f.

 Hint Constructors is.

 Ltac edecorate :=  solve[
                          repeat (apply is_comp || apply is_copair)
                            ||
		                 (apply is_tpure || apply is_downcast || apply is_tag || apply is_untag || assumption)
			    || 
                                 (apply is_epure_ppg)
			    || 
		                 (apply is_ppg_ctc)
                        ].

 Lemma is_coproj1 X Y: is epure (@coproj1 X Y).
 Proof. edecorate. Qed.

 Class EPURE {A B: Type} (f: term A B) := isp : is epure f.
 Hint Extern 0 (EPURE _) => edecorate : typeclass_instances.

 Class PPG {A B: Type} (f: term A B) := isthrw : is ppg f.
 Hint Extern 0 (PPG _) => edecorate : typeclass_instances.

 Class CTC {A B: Type} (f: term A B) := isctch : is ctc f.
 Hint Extern 0 (CTC _) => edecorate : typeclass_instances.


 Inductive kindpl := pl_epure | pl_ppg.

 Inductive is_pl: kindpl -> forall X Y, termpl X Y -> Prop :=
 | is_pl_tpure: forall X Y (f: X -> Y), is_pl pl_epure (@pl_tpure X Y f)
 | is_pl_comp: forall k X Y Z (f: termpl X Y) (g: termpl Y Z), is_pl k f -> is_pl k g -> is_pl k (f O g)
 | is_throw: forall X (e: EName), is_pl pl_ppg (@throw X e)
 | is_try_catch: forall X Y (e: EName) (a: termpl Y X) (b: termpl Y (Val e)), is_pl pl_ppg (@try_catch _ _ e a b)
 | is_pl_pure_ppg: forall X Y (f: termpl X Y), is_pl pl_epure f -> is_pl pl_ppg f.

 Hint Constructors is_pl.

 Ltac pl_edecorate :=  solve[
                          repeat (apply is_pl_comp)
                            ||
		                 (apply is_pl_tpure || apply is_throw || apply is_try_catch || apply is_pl_pure_ppg || assumption)
			    || 
                                 (apply is_pl_pure_ppg)
                        ].

 Class PL_EPURE {A B: Type} (f: termpl A B) := isplp : is_pl pl_epure f.
 Class PL_PPG {A B: Type} (f: termpl A B) := isplthrw : is_pl pl_ppg f.

End Make.
