Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Lra.
Require Import util.


Lemma MVT_gen_ep (f : R -> R) (a b : R) (df : R -> R) :
  let a0 := Rmin a b in
  let b0 := Rmax a b in
  a <> b -> 
  (forall x, a0 < x < b0 -> is_derive f x (df x)) ->
  (forall x, a0 <= x <= b0 -> continuity_pt f x) ->
  exists c, a0 < c < b0 /\ f b - f a = df c * (b - a).
Proof.
  intros *.
  intros aneb isd ctp.

  assert (forall c : R, a0 < c < b0 -> derivable_pt id c) as Q. {
    intros c cr.
    apply derivable_pt_id. }
    
  assert (forall c : R, a0 < c < b0 -> derivable_pt f c) as P. {
    intros c cr.
    apply ex_derive_Reals_0.
    exists (df c).
    apply isd; assumption. }

  assert (forall x : R, a0 <= x <= b0 -> continuity_pt id x)
    as ctq; try (intros;
                 apply continuity_pt_id).

  destruct (Req_dec a0 b0) as [a0eqb0 | a0neb0].
  exfalso.
  apply aneb.
  unfold a0, b0, Rmin, Rmax in a0eqb0.
  destruct Rle_dec; auto.
  assert (a0 < b0) as a0ltb0. {
    unfold a0,b0, Rmin,Rmax.
    destruct Rle_dec; lra. }

  specialize (MVT _ _ _ _ Q P a0ltb0 ctq ctp) as [c [crng rest]].
  exists c.
  split; try assumption.
  specialize (derive_pt_id c) as dieq1.

  rewrite (pr_nu id c (Q c crng) (derivable_pt_id c)), dieq1 in rest.
  unfold a0,b0, Rmax, Rmin, id in *.
  autorewrite with null in rest.
  destruct Rle_dec.
  + rewrite rest.
    rewrite Derive_Reals.
    specialize (isd c crng).
    apply is_derive_unique in isd.
    rewrite isd.
    field.
    
  + setl (-(f a - f b)).
    setr (- (df c * (a - b))).
    apply Ropp_eq_compat.
    rewrite rest.
    rewrite Derive_Reals.
    specialize (isd c crng).
    apply is_derive_unique in isd.
    rewrite isd.
    field.
Qed.



From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Lemma incr_function_le_cont_ep (f : R -> R) (a b : Rbar) (df : R -> R) :
  (forall (x : R), Rbar_le a x -> Rbar_le x b -> continuous f x) ->
  (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> is_derive f x (df x)) ->
  (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> df x > 0) ->
  (forall (x y : R), Rbar_le a x -> x < y -> Rbar_le y b -> f x < f y).
Proof.
  move => Cf Df Hf x y Hax Hxy Hyb.
  apply Rminus_lt_0.
  assert (x <> y) as xney; try lra.
  assert (Rmin x y = x) as rmd. {
    unfold Rmin.
    destruct Rle_dec; lra. }
  assert (Rmax x y = y) as rxd. {
    unfold Rmax.
    destruct Rle_dec; lra. }

  assert (forall x0 : R, Rmin x y < x0 < Rmax x y ->
                         is_derive f x0 (df x0)) as cnd1. {
    rewrite rmd rxd.
    intros x0 [x0l x0u].
    apply Df.
    apply (Rbar_le_lt_trans _ x).
    assumption.
    assumption.
    apply (Rbar_lt_le_trans _ y).
    assumption.
    assumption. }
    
  assert (forall x0 : R, Rmin x y <= x0 <= Rmax x y -> continuity_pt f x0) as cnd2. {
    rewrite rmd rxd.
    intros x0 [x0l x0u].
    apply continuous_pt_impl_continuity_pt.
    apply Cf.
    apply (Rbar_le_trans _ x).
    assumption.
    assumption.
    apply (Rbar_le_trans _ y).
    assumption.
    assumption. }
    
  specialize (MVT_gen_ep f x y df xney cnd1 cnd2) as [c [crng dif]].
  rewrite dif.
  zltab.
  rewrite rmd rxd in crng.
  apply Rgt_lt.
  destruct crng as [cl cu].
  apply Hf.
  apply (Rbar_le_lt_trans _ x).
  assumption.
  assumption.
  apply (Rbar_lt_le_trans _ y).
  assumption.
  assumption.
Qed.


Lemma incr_function_le_ep (f : R -> R) (a b : Rbar) (df : R -> R) :
  (forall (x : R), Rbar_le a x -> Rbar_le x b -> is_derive f x (df x)) ->
  (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> df x > 0) ->
  (forall (x y : R), Rbar_le a x -> x < y -> Rbar_le y b -> f x < f y).
Proof.
  move => Df Hf x y Hax Hxy Hyb.
  apply Rminus_lt_0.
  assert (x <> y) as xney; try lra.
  assert (Rmin x y = x) as rmd. {
    unfold Rmin.
    destruct Rle_dec; lra. }
  assert (Rmax x y = y) as rxd. {
    unfold Rmax.
    destruct Rle_dec; lra. }

  assert (forall x0 : R, Rmin x y < x0 < Rmax x y ->
                         is_derive f x0 (df x0)) as cnd1. {
    rewrite rmd rxd.
    intros x0 [x0l x0u].
    apply Df.
    apply Rbar_lt_le.
    apply (Rbar_le_lt_trans _ x).
    assumption.
    assumption.
    apply Rbar_lt_le.
    apply (Rbar_lt_le_trans _ y).
    assumption.
    assumption. }
    
  assert (forall x0 : R, Rmin x y <= x0 <= Rmax x y -> continuity_pt f x0) as cnd2. {
    rewrite rmd rxd.
    intros x0 [x0l x0u].
    apply continuous_pt_impl_continuity_pt.
    apply (ex_derive_continuous f x0).
    exists (df x0).
    apply Df.
    apply (Rbar_le_trans _ x).
    assumption.
    assumption.
    apply (Rbar_le_trans _ y).
    assumption.
    assumption. }
    
  specialize (MVT_gen_ep f x y df xney cnd1 cnd2) as [c [crng dif]].
  rewrite dif.
  zltab.
  rewrite rmd rxd in crng.
  apply Rgt_lt.
  destruct crng as [cl cu].
  apply Hf.
  apply (Rbar_le_lt_trans _ x).
  assumption.
  assumption.
  apply (Rbar_lt_le_trans _ y).
  assumption.
  assumption.
Qed.



Lemma incr_function_le_ep_one_sided (f : R -> R) (a b : Rbar) (df : R -> R) :
  (forall (x : R), Rbar_le a x -> Rbar_lt x b -> is_derive f x (df x)) ->
  (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> df x > 0) ->
  (forall (x y : R), Rbar_le a x -> x < y -> Rbar_lt y b -> f x < f y).
Proof.
  move => Df Hf x y Hax Hxy Hyb.
  apply Rminus_lt_0.
  assert (x <> y) as xney; try lra.
  assert (Rmin x y = x) as rmd. {
    unfold Rmin.
    destruct Rle_dec; lra. }
  assert (Rmax x y = y) as rxd. {
    unfold Rmax.
    destruct Rle_dec; lra. }

  assert (forall x0 : R, Rmin x y < x0 < Rmax x y ->
                         is_derive f x0 (df x0)) as cnd1. {
    rewrite rmd rxd.
    intros x0 [x0l x0u].
    apply Df.
    apply Rbar_lt_le.
    apply (Rbar_le_lt_trans _ x).
    assumption.
    assumption.
    apply (Rbar_lt_le_trans _ y).
    assumption.
    apply Rbar_lt_le.
    assumption. }
    
  assert (forall x0 : R, Rmin x y <= x0 <= Rmax x y -> continuity_pt f x0) as cnd2. {
    rewrite rmd rxd.
    intros x0 [x0l x0u].
    apply continuous_pt_impl_continuity_pt.
    apply (ex_derive_continuous f x0).
    exists (df x0).
    apply Df.
    apply (Rbar_le_trans _ x).
    assumption.
    assumption.
    apply (Rbar_le_lt_trans _ y).
    assumption.
    assumption. }
    
  specialize (MVT_gen_ep f x y df xney cnd1 cnd2) as [c [crng dif]].
  rewrite dif.
  zltab.
  rewrite rmd rxd in crng.
  apply Rgt_lt.
  destruct crng as [cl cu].
  apply Hf.
  apply (Rbar_le_lt_trans _ x).
  assumption.
  assumption.
  apply (Rbar_lt_trans _ y).
  assumption.
  assumption.
Qed.
