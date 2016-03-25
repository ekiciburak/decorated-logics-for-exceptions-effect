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
Require Prerequistes Terms Decorations Axioms Derived_CoProjections Derived_CoProducts.
Set Implicit Arguments.

Module Make(Import M: Prerequistes.T).
  Module Export ProofsExp := Derived_CoProducts.Make(M).


 (** Annihilation tag untag **)
 Lemma atu: forall e: EName, (tag e) o (untag e) == (@id Empty_set).
 Proof.
    intro e.
    apply elocal_global.
    intro r. destruct(Exc_dec r e) as [Ha|Hb]. rewrite Ha.
    (* case e = r *) (* (1) *)
    rewrite idt. setoid_rewrite <- ids at 6. rewrite <- assoc. (* (1.1) *)
    apply wrepl; [reflexivity| apply eax1]. (* (1.2) *)
    (* case e <> r *) (* (2) *)
    cut(tag e o (@empty (Val e)) == (@id (Empty_set)));
      [ intro H0| setoid_rewrite s_empty; [reflexivity| edecorate| edecorate]].
    rewrite <- H0. setoid_rewrite <- assoc. (* (2.1) *)
    apply wrepl; [reflexivity| apply eax2; exact Hb]. (* (2.2) *)
Qed.

 (** Commutation untag untag **)
 Lemma cuu: forall (t s: EName) , s <> t -> 
    (rcoprod (untag t) id) o coproj2 o (untag s) == (lcoprod id (untag s)) o coproj1 o (untag t).
 Proof.
    intros. apply elocal_global. intro r.  
    (* r = t /\ r <> s *)
    destruct(Exc_dec r s). rewrite e. setoid_rewrite <- assoc at 4. rewrite (@eax2 s t); [| exact H].
      setoid_rewrite <- assoc at 4. setoid_rewrite assoc at 2.
      cut (coproj1 o (@empty (Val t)) == coproj2).
        intro H1. rewrite H1.
        rewrite assoc, s_lcoprod_eq; [| edecorate].
        setoid_rewrite <- assoc. rewrite eax1.
        setoid_rewrite ids. rewrite w_rcoprod_eq; [| edecorate].
        rewrite ids. reflexivity.
      (*1st cut*)
      setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
     destruct(Exc_dec r t). rewrite e. setoid_rewrite <- assoc. rewrite (@eax2 t s); [| auto].
       setoid_rewrite <- assoc. setoid_rewrite assoc at 2.
        cut (coproj2 o (@empty (Val s)) == coproj1).
          intro H1. rewrite H1.
          rewrite assoc, s_rcoprod_eq; [| edecorate].
          setoid_rewrite <- assoc. rewrite eax1.
          setoid_rewrite ids. rewrite w_lcoprod_eq; [| edecorate].
          rewrite ids. reflexivity.
      (*2nd cut*)
      setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
     setoid_rewrite <- assoc. rewrite (@eax2 r s); [| auto].
       setoid_rewrite <- assoc. setoid_rewrite assoc at 2.
        cut (coproj2 o (@empty (Val s)) == coproj1).
          intro H1. rewrite H1.
          rewrite assoc, s_rcoprod_eq; [| edecorate].
          setoid_rewrite <- assoc. 
          rewrite (@eax2 r t); [| auto].
          setoid_rewrite assoc at 3.
          cut (coproj1 o (@empty (Val t)) == coproj2).
            intro H2. rewrite H2.
            setoid_rewrite assoc at 2. rewrite s_lcoprod_eq; [| edecorate].
            setoid_rewrite <- assoc. rewrite eax2; [| auto].
            apply stow. setoid_rewrite assoc. apply replsubs; [| reflexivity].
            setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
          (*4th cut*)
          setoid_rewrite s_empty; [reflexivity| edecorate| edecorate]. 
        (*3rd cut*)
        setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
Qed.

(** PROVING AXIOMS OF PRGRAMMERS' LANGUAGE AFTER TRANSLATING THEM INTO THE CORE LANGUAGE **)
 Axiom mono: forall {X Y: Type} (f g: term Empty_set Y), PPG f /\ PPG g -> ((@empty X) o f == (@empty X) o g)-> f == g.


(** propagate **)
Lemma ppt: forall X Y (e: EName) (a: termpl Y X), PPG (translate _ _ a) ->
                 (@translate _ _ (a O (@throw X e))) == (@translate _ _ (@throw Y e)). 
 Proof.
    intros X Y e a H. simpl.
    rewrite assoc. apply replsubs; [| reflexivity]. apply s_empty; edecorate.
 Qed.


(** recover **)
 Lemma rcv: forall X Y (e: EName) (u1 u2: termpl (Val e) Y), 
               EPURE (translate _ _ u1) -> EPURE (translate _ _ u2) ->
              (@translate _ _ ((@throw X e) O u1)) == (@translate _ _ ((@throw X e) O u2)) -> 
              (@translate _ _ u1) == (@translate _ _ u2).
 Proof.
    intros X Y e u1 u2 H0 H1 H2. simpl in H2. setoid_rewrite <- assoc in H2.
      apply mono in H2; [| split; edecorate].
      apply wtos; [edecorate| edecorate| ].
        transitivity ((untag e o tag e) o (@translate _ _ u1)). setoid_rewrite <- idt at 1.
          apply pwsubs. apply wsym, eax1. unfold pure_id. 
            split; [exact H0| reflexivity].
        apply wsym.
        transitivity ((untag e o tag e) o (@translate _  _ u2)). setoid_rewrite <- idt at 1.
           apply pwsubs. apply wsym, eax1. unfold pure_id. 
            split; [exact H1| reflexivity].
      apply stow. setoid_rewrite <- assoc.
        apply replsubs; [reflexivity| apply sym; exact H2].
 Qed.

(** try **)
 Lemma try: forall X Y (e: EName) (a1 a2: termpl Y X) (b: termpl Y (Val e)),  
            PPG (translate _ _ a1) -> PPG (translate _ _ a2) ->  PPG (translate _ _ b) ->
            (translate _ _ a1) ==(translate _ _ a2) ->
            (@translate _ _ (try_catch e a1 b)) == (@translate _ _ (try_catch e a2 b)).
 Proof.
    intros X Y e a1 a2 b H0 H1 H2 H3. simpl.
      apply wtos; [edecorate| edecorate |].
       setoid_rewrite <- w_downcast. rewrite H3. reflexivity.
 Qed.

(** try0 **)
 Lemma try0: forall X Y (e: EName) (u: termpl Y X) (b: termpl Y (Val e)),  
             EPURE (translate _ _ u) -> PPG (translate _ _ b) ->
             (@translate _ _ (try_catch e u b)) == (@translate _ _ u).
 Proof.
    intros X Y e u b H0 H1. simpl.
      apply wtos; [edecorate |edecorate| ].
      rewrite <- w_downcast. 
        transitivity(id o (@translate _ _ u)). apply pwsubs; [| split; [exact H0| reflexivity]].
        apply w_lcopair_eq; edecorate.
      rewrite idt. reflexivity.
 Qed.

(** try1 **)
 Lemma try1: forall X Y (e: EName) (u: termpl (Val e) X) (b: termpl Y (Val e)),  
             EPURE (translate _ _ u) -> PPG (translate _ _ b) ->
             (@translate _ _ (try_catch e ((@throw Y e) O u) b)) == (@translate _ _ (b O u)).
 Proof.
    intros X Y e u b H0 H1. simpl.
      apply wtos; [edecorate |edecorate| ].
      rewrite <- w_downcast.
      do 2 setoid_rewrite assoc. setoid_rewrite <- assoc at 3.
      cut (coproj2 == coproj1 o (@empty Y)).
        intro H2. rewrite <- H2.
        rewrite s_lcopair_eq; [| edecorate].
        apply pwsubs; [| split; [exact H0| reflexivity]].
        rewrite <- assoc. rewrite eax1, ids. reflexivity.
      setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
 Qed.

 (** try2 **)
 Lemma try2: forall X Y e f (u: termpl (Val f) X) (b: termpl Y (Val e)),  e <> f -> 
                EPURE (translate _ _ u) ->  PPG (translate _ _ b) -> 
 		(@translate _ _ (try_catch e ((@throw Y f) O u) b))  == (@translate _ _ ((@throw Y f) O u)).
 Proof.
    intros X Y e f u b H0 H1 H2. simpl.
      apply wtos; [edecorate |edecorate| ].
      rewrite <- w_downcast.
      do 2 setoid_rewrite assoc. setoid_rewrite <- assoc at 3.
      cut (coproj2 == coproj1 o (@empty Y)).
        intro H3. rewrite <- H3.
        rewrite s_lcopair_eq; [| edecorate].
        apply pwsubs; [| split; [exact H1| reflexivity]].
        rewrite <- assoc. rewrite eax2; [| auto]. rewrite assoc.
        cut((translate Y (Val e) b o empty (Val e)) == empty Y).
          intro H4. rewrite H4. reflexivity.
        setoid_rewrite s_empty; [reflexivity| edecorate].
      setoid_rewrite s_empty; [reflexivity| edecorate| edecorate].
 Qed.


End Make.
