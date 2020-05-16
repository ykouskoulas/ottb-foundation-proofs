(* begin hide *)
Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Lra.
Require Import FunctionalExtensionality.
Require Import util.
Require Import atan2.
Require Import ttyp.

Import Lra.
(* end hide *)

(* Coquelicot library continuity using balls is consistent with the
real library's delta-epsilon definition *)

(**
The turn is modeled as a circular arc. During the turn, path always
maintains a constant distance from the turn's center.
*)
Lemma turncenter : forall r θ₀ x₀ y₀, 0 <= r ->
    (magnitude (fun d => (Hxarc r θ₀ x₀ d) - (Tcx r θ₀ x₀))
               (fun d => (Hyarc r θ₀ y₀ d) - (Tcy r θ₀ y₀))) =
    (fun _ => r).
Proof.
  intros r θ₀ x₀ y₀ zler.
  unfold magnitude, comp, plus_fct.
  apply functional_extensionality.
  intros.
  unfold Hxarc, Hyarc, Tcy, Tcx.
  rewrite (cos_sin θ₀).
  rewrite (sin_cos θ₀).
  assert (((r * sin (x / r + θ₀) - r * - cos (PI / 2 + θ₀) + x₀ -
                           (x₀ + r * cos (PI / 2 + θ₀)))² +
           (- r * cos (x / r + θ₀) + r * sin (PI / 2 + θ₀) + y₀ -
                           (y₀ + r * sin (PI / 2 + θ₀)))²) =
          Rsqr r * ((sin (x / r + θ₀))² +
           (cos (x / r + θ₀))²)). unfold Rsqr.
  field.
  intros. rewrite H. clear H.
  rewrite sin2_cos2.
  assert (r² * 1 = r²). unfold Rsqr. field. rewrite H. clear H.
  apply sqrt_Rsqr. assumption.
Qed.

(** Derivatives and continuity for path H and components *)

Theorem Hxarc_deriv : forall (r θ₀ x₀ d :R),
    0 <> r ->
    is_derive (Hxarc r θ₀ x₀) d (Hxarc' r θ₀ d).
Proof.
  intros r θ₀ x₀ d zner. unfold Hxarc, Hxarc'.

  auto_derive. apply I.
  fieldrewrite (d* /r) (d/r).
  intro. subst. apply zner.  reflexivity.
  field.
  intro. subst. apply zner. reflexivity.
Qed.


Theorem Hyarc_deriv : forall  (r θ₀ y₀ d :R),
    0 <> r ->
    is_derive (Hyarc r θ₀ y₀) d (Hyarc' r θ₀ d).
Proof.
  intros r θ₀ y₀ d zner.
  unfold Hyarc, Hyarc'.

  auto_derive.  apply I.
  fieldrewrite (d* /r) (d/r).
  intro. subst. apply zner.  reflexivity.
  field.
  intro. subst. apply zner. reflexivity.
Qed.



Theorem Hxarc_cont : forall  (r θ₀ x₀ d :R),
    continuous (Hxarc r θ₀ x₀) d.
Proof.
  intros r θ₀ x₀ d.
  set (f := (Hxarc r θ₀ x₀)).
  assert (continuity_pt f d). unfold f, Hxarc. reg.
  apply continuity_pt_impl_continuous_pt. assumption.
Qed.

Theorem Hyarc_cont : forall (r θ₀ y₀ d :R),
    continuous (Hyarc r θ₀ y₀) d.
Proof.
  intros r θ₀ y₀ d.
  set (f := (Hyarc r θ₀ y₀)).
  assert (continuity_pt f d). unfold f, Hyarc. reg.
  apply continuity_pt_impl_continuous_pt. assumption.
Qed.

  

Theorem Hxlin_deriv : forall (θ₀ x₀ K d :R),
    is_derive (fun q => (Hxlin θ₀ x₀ (q - K))) d (Hxlin' θ₀ d).
Proof.
  intros θ₀ x₀ K d.
  unfold Hxlin, Hxlin'.
  auto_derive. apply I. field.
Qed.


Theorem Hylin_deriv : forall (θ₀ y₀ K d :R),
    is_derive (fun q => (Hylin θ₀ y₀ (q - K))) d (Hylin' θ₀ d).
Proof.
  intros θ₀ y₀ K d.
  unfold Hylin, Hylin'.
  auto_derive. apply I. field.
Qed.


Theorem Hxlin_cont : forall (θ₀ x₀ K d :R),
    continuous (fun q => (Hxlin θ₀ x₀ (q - K))) d.
Proof.
  intros θ₀ x₀ K d.
  set (f := (fun q => Hxlin θ₀ x₀ (q-K))).
  assert (continuity_pt f d). unfold f, Hxlin. reg.
  apply continuity_pt_impl_continuous_pt. assumption.
Qed.

Theorem Hylin_cont : forall (θ₀ y₀ K d :R),
    continuous (fun q => (Hylin θ₀ y₀ (q - K))) d.
Proof.
  intros θ₀ y₀ K d.
  set (f := (fun q => Hylin θ₀ y₀ (q-K))).
  assert (continuity_pt f d). unfold f, Hylin. reg.
  apply continuity_pt_impl_continuous_pt. assumption.
Qed.


Lemma Hx_cont : forall r θ₀ x₀ θc rtp (d:R), 
    continuous (Hx r θ₀ x₀ θc rtp) d.
Proof.
  intros.
  unfold Hx.

  change (continuous
            (extension_cont
               (Hxarc r θ₀ x₀)
               (fun q : R => Hxlin (θ₀ + θc)
                                   (Hxarc r θ₀ x₀ (r * θc))
                                   (q - r * θc))
               (r * θc))
            d).

  case_eq (Rle_dec d (r*θc)). intros.
  inversion r0.

  (* left case *)
  generalize (Hxarc_cont r θ₀ x₀ d) as iscontHxarc. intros.
  unfold continuous, extension_cont, locally, filterlim,
         filtermap, filter_le in *.
  intro P.
  specialize (iscontHxarc P).
  rewrite H.
  intro head.
  specialize (iscontHxarc head).
  inversion_clear head as [eps' Hxball].
  inversion_clear iscontHxarc as [del iscontHxarc'].
  set (m := ((r*θc)-d)/2).
  assert (0 < m) as zltxmt2. unfold m.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (r * θc - d). lra.
  set (zeta := (if Rle_dec del m then del
                else (mkposreal m zltxmt2))) in *.
  assert (zeta <= del) as zledel.
  unfold zeta; destruct (Rle_dec del m); simpl; try lra.
  (* apply Rnot_le_lt in n. left. assumption. *)
  assert (zeta <= m) as zlexmt2.
  unfold zeta; destruct (Rle_dec del m);
    try apply Rnot_le_lt in n; try assumption.
  simpl. right. reflexivity.
  assert (0 < zeta) as zltzeta.
  destruct (Rle_dec del m). destruct del. simpl. lra.
  destruct zeta. simpl. lra.
  exists zeta.
  intros.
  assert (ball d del y) as balltdely.
  assert (Rabs (y - d) < zeta). apply H1.
  assert (Rabs (y - d) < del). lra.
  apply H3.
  specialize (iscontHxarc' y balltdely).

  destruct (Rle_dec y (r * θc)). assumption.
  exfalso.
  apply Rnot_le_lt in n.

  destruct zeta. simpl in *. 
  assert (2*pos <=  (r * θc - d)).
  apply (Rmult_le_reg_l (1/2)). lra.
  setl pos. setr ((r * θc - d)/2). change (pos <= m).
  assumption.

  assert (y - d < pos).
  assert (Rabs (y - d) < pos). apply H1.
  unfold Rabs in H3. destruct (Rcase_abs (y - d)).
  lra. assumption.
  lra.

  (* center case  *)
  subst.
  apply extension_cont_continuous.
  apply Hxarc_cont; assumption.
  apply Hxlin_cont; assumption.
  unfold Hxarc, Hxlin.
  repeat rewrite rsinrr.
  setr (r * sin (θc + θ₀) - r * sin θ₀ + x₀). reflexivity.

  (* right case *)
  intros.
  assert ((r * θc) < d) as xltt.
  clear H.
  apply Rnot_le_lt in n. assumption.

  generalize (Hxlin_cont (θ₀+θc)
                         (Hxarc r θ₀ x₀ (r * θc)) (r*θc) d)
    as iscontHxlin.
  intros.
  unfold continuous, extension_cont, locally, filterlim,
         filtermap, filter_le in *.
  intro P.
  specialize (iscontHxlin P).
  rewrite H.
  intro head.
  specialize (iscontHxlin head).
  inversion_clear head as [eps' Hxball].
  inversion_clear iscontHxlin as [del iscontHxlin'].

  set (m := (d-(r*θc))/2).
  assert (0 < m) as zltxmt2. unfold m.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (d - r * θc). lra.
  set (zeta := (if Rle_dec del m then del
                else (mkposreal m zltxmt2))) in *.
  assert (zeta <= del) as zledel.
  unfold zeta; destruct (Rle_dec del m); simpl; try lra.
  (* apply Rnot_le_lt in n0. left. assumption. *)
  assert (zeta <= m) as zlexmt2.
  unfold zeta; destruct (Rle_dec del m);
    try apply Rnot_le_lt in n; try assumption.
  simpl. right. reflexivity.
  assert (0 < zeta) as zltzeta.
  destruct (Rle_dec del m). destruct del. simpl. lra.
  destruct zeta. simpl. lra.
  exists zeta.
  intros.
  assert (ball d del y) as balltdely.
  assert (Rabs (y - d) < zeta). apply H0.
  assert (Rabs (y - d) < del). lra.
  apply H2.
  specialize (iscontHxlin' y balltdely).

  destruct (Rle_dec y (r * θc)).
  inversion_clear r0.
  (****)
  exfalso.
  clear Hxball iscontHxlin'.
  assert (d - y < zeta).
  assert (Rabs (y - d) < zeta). apply H0.
  unfold Rabs in H2.
  destruct (Rcase_abs (y - d)); lra.
  assert (2*zeta<= d - (r * θc)). 
  apply (Rmult_le_reg_l (1/2)). lra.
  setl zeta. setr ((d - r * θc)/2). change (zeta <= m).
  assumption.
  lra.

  subst. unfold Hxarc in *.
  unfold Hxlin in iscontHxlin'.
  fieldrewrite (r * sin (r * θc / r + θ₀) - r * sin θ₀ + x₀)
               ((r * θc - r * θc) * cos (θ₀ + θc) +
                (r * sin (r * θc / r + θ₀) - r * sin θ₀ + x₀)).
  assumption.
  assumption.
Qed.


Lemma Hy_cont : forall r θ₀ y₀ θc rtp (d:R), 
    continuous (Hy r θ₀ y₀ θc rtp) d.
Proof.
  intros.
  unfold Hy.

  change (continuous
            (extension_cont
               (Hyarc r θ₀ y₀)
               (fun q : R => Hylin (θ₀ + θc)
                                   (Hyarc r θ₀ y₀ (r * θc))
                                   (q - r * θc))
               (r * θc))
            d).

  case_eq (Rle_dec d (r*θc)). intros.
  inversion r0.

  (* left case *)
  generalize (Hyarc_cont r θ₀ y₀ d) as iscontHyarc. intros.
  unfold continuous, extension_cont, locally, filterlim,
         filtermap, filter_le in *.
  intro P.
  specialize (iscontHyarc P).
  rewrite H.
  intro head.
  specialize (iscontHyarc head).
  inversion_clear head as [eps' Hyball].
  inversion_clear iscontHyarc as [del iscontHyarc'].
  set (m := ((r*θc)-d)/2).
  assert (0 < m) as zltxmt2. unfold m.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (r * θc - d). lra.
  set (zeta := (if Rle_dec del m then del
                else (mkposreal m zltxmt2))) in *.
  assert (zeta <= del) as zledel.
  unfold zeta; destruct (Rle_dec del m); simpl; try lra.
  (* apply Rnot_le_lt in n. left. assumption. *)
  assert (zeta <= m) as zlexmt2.
  unfold zeta; destruct (Rle_dec del m);
    try apply Rnot_le_lt in n; try assumption.
  simpl. right. reflexivity.
  assert (0 < zeta) as zltzeta.
  destruct (Rle_dec del m). destruct del. simpl. lra.
  destruct zeta. simpl. lra.
  exists zeta.
  intros.
  assert (ball d del y) as balltdely.
  assert (Rabs (y - d) < zeta). apply H1.
  assert (Rabs (y - d) < del). lra.
  apply H3.
  specialize (iscontHyarc' y balltdely).

  destruct (Rle_dec y (r * θc)). assumption.
  exfalso.
  apply Rnot_le_lt in n.

  destruct zeta. simpl in *. 
  assert (2*pos <=  (r * θc - d)).
  apply (Rmult_le_reg_l (1/2)). lra.
  setl pos. setr ((r * θc - d)/2). change (pos <= m).
  assumption.

  assert (y - d < pos).
  assert (Rabs (y - d) < pos). apply H1.
  unfold Rabs in H3. destruct (Rcase_abs (y - d)).
  lra. assumption.
  lra.

  (* center case  *)
  subst.
  apply extension_cont_continuous.
  apply Hyarc_cont; assumption.
  apply Hylin_cont; assumption.
  unfold Hyarc, Hylin.
  repeat rewrite rcosrrn.
  setr (- r * cos (θc + θ₀) + r * cos θ₀ + y₀). reflexivity.

  (* right case *)
  intros.
  assert ((r * θc) < d) as xltt.
  clear H.
  apply Rnot_le_lt in n. assumption.

  generalize (Hylin_cont (θ₀+θc)
                         (Hyarc r θ₀ y₀ (r * θc)) (r*θc) d)
    as iscontHylin.
  intros.
  unfold continuous, extension_cont, locally, filterlim,
         filtermap, filter_le in *.
  intro P.
  specialize (iscontHylin P).
  rewrite H.
  intro head.
  specialize (iscontHylin head).
  inversion_clear head as [eps' Hyball].
  inversion_clear iscontHylin as [del iscontHylin'].

  set (m := (d-(r*θc))/2).
  assert (0 < m) as zltxmt2. unfold m.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (d - r * θc). lra.
  set (zeta := (if Rle_dec del m then del
                else (mkposreal m zltxmt2))) in *.
  assert (zeta <= del) as zledel.
  unfold zeta; destruct (Rle_dec del m); simpl; try lra.
  (* apply Rnot_le_lt in n0. left. assumption. *)
  assert (zeta <= m) as zlexmt2.
  unfold zeta; destruct (Rle_dec del m);
    try apply Rnot_le_lt in n; try assumption.
  simpl. right. reflexivity.
  assert (0 < zeta) as zltzeta.
  destruct (Rle_dec del m). destruct del. simpl. lra.
  destruct zeta. simpl. lra.
  exists zeta.
  intros.
  assert (ball d del y) as balltdely.
  assert (Rabs (y - d) < zeta). apply H0.
  assert (Rabs (y - d) < del). lra.
  apply H2.
  specialize (iscontHylin' y balltdely).

  destruct (Rle_dec y (r * θc)).
  inversion_clear r0.
  (****)
  exfalso.
  clear Hyball iscontHylin'.
  assert (d - y < zeta).
  assert (Rabs (y - d) < zeta). apply H0.
  unfold Rabs in H2.
  destruct (Rcase_abs (y - d)); lra.
  assert (2*zeta<= d - (r * θc)). 
  apply (Rmult_le_reg_l (1/2)). lra.
  setl zeta. setr ((d - r * θc)/2). change (zeta <= m).
  assumption.
  lra.

  subst. unfold Hyarc in *.
  unfold Hylin in iscontHylin'.
  fieldrewrite (- r * cos (r * θc / r + θ₀) + r * cos θ₀ + y₀)
               ((r * θc - r * θc) * sin (θ₀ + θc) +
                    (- r * cos (r * θc / r + θ₀) + r * cos θ₀ + y₀)).
  assumption.
  assumption.
Qed.


Lemma Hx_deriv: forall r θ₀ x₀ θc rtp (d:R),
    is_derive (Hx r θ₀ x₀ θc rtp) d (Hx' r θ₀ θc rtp d).
Proof.
  intros. unfold Hx, Hx'.
  addzner.

  change (is_derive
            (extension_cont
               (Hxarc r θ₀ x₀)
               (fun q : R => Hxlin (θ₀ + θc)
                                   (Hxarc r θ₀ x₀ (r * θc))
                                   (q - r * θc))
               (r * θc)) d
            ((extension_cont
               (Hxarc' r θ₀)
               (Hxlin' (θ₀ + θc))
               (r * θc)) d)).

  generalize (Hxarc_deriv r θ₀ x₀ d zner) as isderivHxarc.
  intros. inversion_clear isderivHxarc as [linarc isderiveHxarc].
  generalize (Hxlin_deriv (θ₀ + θc) (Hxarc r θ₀ x₀ (r * θc))
                          (r*θc) d) as isderivHxlin.
  intros. inversion_clear isderivHxlin as [linlin isderiveHxlin].

  split.

  (* is linear *)
  case_eq (Rle_dec d (r * θc)); intros;
    unfold extension_cont; rewrite H; assumption.

  (* derivatives *)
  intro x1.
  set (x := (r * θc)) in *.
  case_eq (Rle_dec d x); case_eq (Rle_dec x1 x).
  2: {
  (*==*)
  intros nx1lex x1lex_dec tlex tlex_dec ifltx1.
  assert (x < x1) as xltx1.
  apply Rnot_le_lt. assumption.
  exfalso. clear isderiveHxarc isderiveHxlin linarc linlin zner nx1lex x1lex_dec.
  unfold is_filter_lim, locally in ifltx1.
  specialize (ifltx1 (fun y => x < y)). simpl in ifltx1.
  assert (exists eps : posreal, forall y : R, ball x1 eps y -> x < y).
  assert (0 < (x1-x)/2) as zltx1mx.
  Rmult 2. lra. setl 0. setr (x1 - x). lra.
  exists (mkposreal ((x1-x)/2) zltx1mx).
  simpl. intros y ballx1.
  intros.
  assert (Rabs (y - x1) < (x1-x)/2) as ballx1c.
  apply ballx1.
  unfold Rabs in ballx1c. destruct (Rcase_abs (y - x1)).
  assert ( 2* x1 - 2 * y < x1 - x).
  Rmult (1/2). lra. setl (x1-y). setr ((x1-x)/2).
  lra. lra.
  assert ( 2 * y - 2* x1 < x1 - x).
  Rmult (1/2). lra. setl (y - x1). setr ((x1-x)/2).
  lra. lra.
  specialize (ifltx1 H). clear H.
  inversion_clear ifltx1 as [eps ifltx1'].
  specialize (ifltx1' d (ball_center d eps)).
  lra.
  }
  2 : {
  (*==*)
  intros x1lex x1lex_dec ntlex tlex_dec ifltx1.
  assert (x < d) as xltt.
  apply Rnot_le_lt. assumption.
  inversion_clear x1lex as [x1ltx | x1eqx].
  exfalso. clear isderiveHxarc isderiveHxlin linarc linlin zner.
  clear x1lex_dec x1lex ntlex tlex_dec. simpl in x1.
  
  unfold is_filter_lim, locally in ifltx1.
  specialize (ifltx1 (fun p => p < x)). simpl in ifltx1.
  assert (exists eps : posreal, forall y : R, ball x1 eps y -> y < x).
  assert (0 < (x - x1)/2) as zltxmx1.
  Rmult 2. lra. setl 0. setr (x - x1). lra.
  exists (mkposreal ((x - x1)/2) zltxmx1).
  simpl. intros y ballx1.
  intros.
  assert (Rabs (y - x1) < (x - x1)/2) as ballx1c.
  apply ballx1.
  unfold Rabs in ballx1c. destruct (Rcase_abs (y - x1)).
  assert ( 2* x1 - 2 * y < x - x1 ).
  Rmult (1/2). lra. setl (x1-y). setr ((x - x1)/2).
  lra. lra.
  assert ( 2 * y - 2* x1 < x - x1 ).
  Rmult (1/2). lra. setl (y - x1). setr ((x - x1)/2).
  lra. lra.
  specialize (ifltx1 H). clear H.
  inversion_clear ifltx1 as [eps ifltx1'].
  specialize (ifltx1' d (ball_center d eps)).
  lra.

  exfalso.
  subst.
  clear isderiveHxarc isderiveHxlin linarc linlin zner.
  clear x1lex_dec x1lex ntlex tlex_dec .
  unfold is_filter_lim, locally in ifltx1.
  specialize (ifltx1 (fun p => p < d)). simpl in ifltx1.
  assert (exists eps : posreal, forall y : R, ball x eps y -> y < d).
  assert (0 < (d - x)/2) as zltxmx1.
  Rmult 2. lra. setl 0. setr (d - x). lra.
  exists (mkposreal ((d - x)/2) zltxmx1).
  simpl. intros y ballx1.
  assert (Rabs (y - x) < (d - x)/2) as ballx1c.
  apply ballx1.
  unfold Rabs in ballx1c. destruct (Rcase_abs (y - x)).
  assert ( 2* x - 2 * y < d - x ).
  Rmult (1/2). lra. setl (x-y). setr ((d - x)/2).
  lra. lra.
  assert ( 2 * y - 2* x < d - x).
  Rmult (1/2). lra. setl (y - x). setr ((d - x)/2).
  lra. lra.
  specialize (ifltx1 H). clear H.
  inversion_clear ifltx1 as [eps ifltx1'].
  specialize (ifltx1' d (ball_center d eps)).
  lra.
  }
  intros x1lex x1lex_dec tlex tlex_dec.
  inversion_clear tlex as [tltx | teqx].

  (* left case *)
  clear linlin isderiveHxlin.
  unfold is_domin.
  intros ifl eps.
  specialize (isderiveHxarc x1 ifl eps).
  unfold locally, extension_cont.
  inversion_clear isderiveHxarc as [eps0 isderivHxarc''].
  set (zeta := Rmin eps0 ((x-d)/2)).
  assert (0<zeta) as zltzeta.
  unfold zeta, Rmin.
  destruct (Rle_dec eps0 ((x - d) / 2)).
  destruct eps0. simpl. lra.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (x - d). lra.
  exists (mkposreal zeta zltzeta).
  simpl. intros.
  
  rewrite tlex_dec, x1lex_dec. 
  destruct (Rle_dec y x).
  assert (ball d eps0 y) as balleps.
  assert (Rabs (y - d) < zeta) as ballzetac. apply H.
  unfold zeta,Rmin in ballzetac.
  destruct (Rle_dec eps0 ((x-d)/2)). apply ballzetac.
  apply Rnot_le_lt in n.
  assert (Rabs (y - d) < eps0) as ballepsc. lra.
  apply ballepsc.
  specialize (isderivHxarc'' y balleps).
  assumption.

  exfalso.
  apply Rnot_le_lt in n.
  assert (Rabs (y - d) < zeta) as ballzetac. apply H.
  unfold zeta,Rmin in ballzetac.
  destruct (Rle_dec eps0 ((x-d)/2)).

  assert (y - d < eps0) as ymtlteps0.
  unfold Rabs in ballzetac.
  destruct (Rcase_abs (y - d)).
  lra. assumption. clear ballzetac.

  assert (2*eps0 <= x - d).
  apply (Rmult_le_reg_l (1/2)). lra.
  setl eps0. setr ((x-d)/2).
  assumption. lra.

  apply Rnot_le_lt in n0.
  assert (y - d < (x-d)/2) as ymtltxmt2.
  unfold Rabs in ballzetac.
  destruct (Rcase_abs (y - d)).
  lra. assumption. clear ballzetac.

  assert (2*y-2*d < x - d).
  apply (Rmult_lt_reg_l (1/2)). lra.
  setl (y-d). setr ((x-d)/2).
  assumption. clear ymtltxmt2.
  lra.

  
  (* center case  *)
  symmetry in teqx.
  subst. 
  apply extension_cont_is_derive.


  unfold extension_cont, is_derive, locally, filterdiff,
         locally, is_domin in *.
  rewrite tlex_dec in *.
  split. assumption.
  intros x0 ifl eps.
  specialize (isderiveHxarc x0 ifl eps).
  inversion_clear isderiveHxarc as [eps0 isderivHxarc''].
  exists eps0.
  intros y ballteps0.
  specialize (isderivHxarc'' y ballteps0).
  assumption.

  unfold extension_cont, is_derive, locally, filterdiff, is_filter_lim,
  locally, is_domin in *.
  rewrite tlex_dec in *.
  change (is_derive
    (fun q : R => Hxlin (θ₀ + θc) (Hxarc r θ₀ x₀ x) (q - r * θc)) x
    (Hxarc' r θ₀ x)).

  assert ((Hxarc' r θ₀ x) =
          (Hxlin' (θ₀ + θc) x)).
  unfold Hxarc', Hxlin'.
  unfold x.
  fieldrewrite (r * θc / r + θ₀) (θ₀ + θc).
  intro. subst. apply zner. reflexivity.
  reflexivity.
  rewrite H.
  apply Hxlin_deriv.

  (* values match at join point *)
  unfold Hxarc, Hxlin. unfold x.
  fieldrewrite (r*θc/r) θc.
  intro. subst. apply zner.  reflexivity.
  setr(r * sin (θc + θ₀) - r * sin θ₀ + x₀).
  reflexivity.

  (* right case *)
  intros nx1lex x1lex_dec ntlex tlex_dec ifl.
  assert (x < d) as xltt.
  clear tlex_dec.
  apply Rnot_le_lt in ntlex. assumption.

  assert (x < x1) as xltx1.
  clear x1lex_dec.
  apply Rnot_le_lt in nx1lex. assumption.

  clear linarc isderiveHxarc.
  unfold is_domin.
  intros eps.
  specialize (isderiveHxlin x1 ifl eps).
  unfold locally, extension_cont.
  inversion_clear isderiveHxlin as [eps0 isderivHxlin''].
  set (zeta := Rmin eps0 ((d-x)/2)).
  assert (0<zeta) as zltzeta.
  unfold zeta, Rmin.
  destruct (Rle_dec eps0 ((d-x) / 2)).
  destruct eps0. simpl. lra.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (d-x). lra.
  exists (mkposreal zeta zltzeta).
  simpl. intros.

  rewrite tlex_dec, x1lex_dec.
  destruct (Rle_dec y x).

  exfalso.
  assert (Rabs (y - d) < zeta) as ballzetac. apply H.
  unfold zeta,Rmin in ballzetac.
  destruct (Rle_dec eps0 ((d-x)/2)).

  unfold Rabs in ballzetac.
  destruct (Rcase_abs (y - d)).
  assert (d - y < eps0) as ymtlteps0.
  lra. clear ballzetac.

  assert (2*eps0 <= d-x).
  apply (Rmult_le_reg_l (1/2)). lra.
  setl eps0. setr ((d-x) / 2). assumption.
  unfold x in *. lra.
  unfold x in *. lra.

  apply Rnot_le_lt in n.
  unfold Rabs in ballzetac.
  destruct (Rcase_abs (y - d)).
  assert (d - y < (d - x)/2) as ymtltxmt2.
  lra. 

  assert (2*d - 2*y < d - x).
  apply (Rmult_lt_reg_l (1/2)). lra.
  setl (d-y). setr ((d - x) / 2).
  assumption. clear ymtltxmt2.
  unfold x in *.
  lra.
  unfold x in *. lra.

  assert (ball d eps0 y) as ballteps0.
  unfold zeta, Rmin in H.
  destruct (Rle_dec eps0 ((d-x)/2)).
  assumption.
  assert (Rabs (y - d) < eps0).
  apply Rnot_le_lt in n.
  apply Rnot_le_lt in n0.
  apply (Rlt_trans _ ((d-x)/2)); assumption.
  assumption.

  apply isderivHxlin''. assumption.
Qed.


Lemma Hy_deriv: forall r θ₀ y₀ θc rtp (d:R),
    is_derive (Hy r θ₀ y₀ θc rtp) d (Hy' r θ₀ θc rtp d).
Proof.
  intros.
  addzner.
  unfold Hy, Hy'.

  change (is_derive
            (extension_cont
               (Hyarc r θ₀ y₀)
               (fun q : R => Hylin (θ₀ + θc)
                                   (Hyarc r θ₀ y₀ (r * θc))
                                   (q - r * θc))
               (r * θc)) d
            ((extension_cont
               (Hyarc' r θ₀)
               (Hylin' (θ₀ + θc))
               (r * θc)) d)).

  generalize (Hyarc_deriv r θ₀ y₀ d zner) as isderivHyarc.
  intros. inversion_clear isderivHyarc as [linarc isderiveHyarc].
  generalize (Hylin_deriv (θ₀ + θc) (Hyarc r θ₀ y₀ (r * θc))
                          (r*θc) d) as isderivHylin.
  intros. inversion_clear isderivHylin as [linlin isderiveHylin].

  split.

  (* is linear *)
  case_eq (Rle_dec d (r * θc)); intros;
    unfold extension_cont; rewrite H; assumption.

  (* derivatives *)
  intro x1.
  set (x := (r * θc)) in *.
  case_eq (Rle_dec d x); case_eq (Rle_dec x1 x).
  2 : {
  (*==*)
  intros nx1lex x1lex_dec tlex tlex_dec ifltx1.
  assert (x < x1) as xltx1.
  apply Rnot_le_lt. assumption.
  exfalso. clear isderiveHyarc isderiveHylin linarc linlin zner nx1lex x1lex_dec.
  unfold is_filter_lim, locally in ifltx1.
  specialize (ifltx1 (fun y => x < y)). simpl in ifltx1.
  assert (exists eps : posreal, forall y : R, ball x1 eps y -> x < y).
  assert (0 < (x1-x)/2) as zltx1mx.
  Rmult 2. lra. setl 0. setr (x1 - x). lra.
  exists (mkposreal ((x1-x)/2) zltx1mx).
  simpl. intros y ballx1.
  intros.
  assert (Rabs (y - x1) < (x1-x)/2) as ballx1c.
  apply ballx1.
  unfold Rabs in ballx1c. destruct (Rcase_abs (y - x1)).
  assert ( 2* x1 - 2 * y < x1 - x).
  Rmult (1/2). lra. setl (x1-y). setr ((x1-x)/2).
  lra. lra.
  assert ( 2 * y - 2* x1 < x1 - x).
  Rmult (1/2). lra. setl (y - x1). setr ((x1-x)/2).
  lra. lra.
  specialize (ifltx1 H). clear H.
  inversion_clear ifltx1 as [eps ifltx1'].
  specialize (ifltx1' d (ball_center d eps)).
  lra.
  }
  2 : {
  (*==*)
  intros x1lex x1lex_dec ntlex tlex_dec ifltx1.
  assert (x < d) as xltt.
  apply Rnot_le_lt. assumption.
  inversion_clear x1lex as [x1ltx | x1eqx].
  exfalso. clear isderiveHyarc isderiveHylin linarc linlin zner.
  clear x1lex_dec x1lex ntlex tlex_dec. simpl in x1.
  
  unfold is_filter_lim, locally in ifltx1.
  specialize (ifltx1 (fun p => p < x)). simpl in ifltx1.
  assert (exists eps : posreal, forall y : R, ball x1 eps y -> y < x).
  assert (0 < (x - x1)/2) as zltxmx1.
  Rmult 2. lra. setl 0. setr (x - x1). lra.
  exists (mkposreal ((x - x1)/2) zltxmx1).
  simpl. intros y ballx1.
  intros.
  assert (Rabs (y - x1) < (x - x1)/2) as ballx1c.
  apply ballx1.
  unfold Rabs in ballx1c. destruct (Rcase_abs (y - x1)).
  assert ( 2* x1 - 2 * y < x - x1 ).
  Rmult (1/2). lra. setl (x1-y). setr ((x - x1)/2).
  lra. lra.
  assert ( 2 * y - 2* x1 < x - x1 ).
  Rmult (1/2). lra. setl (y - x1). setr ((x - x1)/2).
  lra. lra.
  specialize (ifltx1 H). clear H.
  inversion_clear ifltx1 as [eps ifltx1'].
  specialize (ifltx1' d (ball_center d eps)).
  lra.

  exfalso.
  subst.
  clear isderiveHyarc isderiveHylin linarc linlin zner.
  clear x1lex_dec x1lex ntlex tlex_dec .
  unfold is_filter_lim, locally in ifltx1.
  specialize (ifltx1 (fun p => p < d)). simpl in ifltx1.
  assert (exists eps : posreal, forall y : R, ball x eps y -> y < d).
  assert (0 < (d - x)/2) as zltxmx1.
  Rmult 2. lra. setl 0. setr (d - x). lra.
  exists (mkposreal ((d - x)/2) zltxmx1).
  simpl. intros y ballx1.
  assert (Rabs (y - x) < (d - x)/2) as ballx1c.
  apply ballx1.
  unfold Rabs in ballx1c. destruct (Rcase_abs (y - x)).
  assert ( 2* x - 2 * y < d - x ).
  Rmult (1/2). lra. setl (x-y). setr ((d - x)/2).
  lra. lra.
  assert ( 2 * y - 2* x < d - x).
  Rmult (1/2). lra. setl (y - x). setr ((d - x)/2).
  lra. lra.
  specialize (ifltx1 H). clear H.
  inversion_clear ifltx1 as [eps ifltx1'].
  specialize (ifltx1' d (ball_center d eps)).
  lra.
  }
  intros x1lex x1lex_dec tlex tlex_dec.
  inversion_clear tlex as [tltx | teqx].

  (* left case *)
  clear linlin isderiveHylin.
  unfold is_domin.
  intros ifl eps.
  specialize (isderiveHyarc x1 ifl eps).
  unfold locally, extension_cont.
  inversion_clear isderiveHyarc as [eps0 isderivHyarc''].
  set (zeta := Rmin eps0 ((x-d)/2)).
  assert (0<zeta) as zltzeta.
  unfold zeta, Rmin.
  destruct (Rle_dec eps0 ((x - d) / 2)).
  destruct eps0. simpl. lra.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (x - d). lra.
  exists (mkposreal zeta zltzeta).
  simpl. intros.
  
  rewrite tlex_dec, x1lex_dec. 
  destruct (Rle_dec y x).
  assert (ball d eps0 y) as balleps.
  assert (Rabs (y - d) < zeta) as ballzetac. apply H.
  unfold zeta,Rmin in ballzetac.
  destruct (Rle_dec eps0 ((x-d)/2)). apply ballzetac.
  apply Rnot_le_lt in n.
  assert (Rabs (y - d) < eps0) as ballepsc. lra.
  apply ballepsc.
  specialize (isderivHyarc'' y balleps).
  assumption.

  exfalso.
  apply Rnot_le_lt in n.
  assert (Rabs (y - d) < zeta) as ballzetac. apply H.
  unfold zeta,Rmin in ballzetac.
  destruct (Rle_dec eps0 ((x-d)/2)).

  assert (y - d < eps0) as ymtlteps0.
  unfold Rabs in ballzetac.
  destruct (Rcase_abs (y - d)).
  lra. assumption. clear ballzetac.

  assert (2*eps0 <= x - d).
  apply (Rmult_le_reg_l (1/2)). lra.
  setl eps0. setr ((x-d)/2).
  assumption. lra.

  apply Rnot_le_lt in n0.
  assert (y - d < (x-d)/2) as ymtltxmt2.
  unfold Rabs in ballzetac.
  destruct (Rcase_abs (y - d)).
  lra. assumption. clear ballzetac.

  assert (2*y-2*d < x - d).
  apply (Rmult_lt_reg_l (1/2)). lra.
  setl (y-d). setr ((x-d)/2).
  assumption. clear ymtltxmt2.
  lra.

  
  (* center case  *)
  symmetry in teqx.
  subst. 
  apply extension_cont_is_derive.


  unfold extension_cont, is_derive, locally, filterdiff,
         locally, is_domin in *.
  rewrite tlex_dec in *.
  split. assumption.
  intros x0 ifl eps.
  specialize (isderiveHyarc x0 ifl eps).
  inversion_clear isderiveHyarc as [eps0 isderivHyarc''].
  exists eps0.
  intros y ballteps0.
  specialize (isderivHyarc'' y ballteps0).
  assumption.

  unfold extension_cont, is_derive, locally, filterdiff, is_filter_lim,
  locally, is_domin in *.
  rewrite tlex_dec in *.
  change (is_derive
    (fun q : R => Hylin (θ₀ + θc) (Hyarc r θ₀ y₀ x) (q - r * θc)) x
    (Hyarc' r θ₀ x)).

  assert ((Hyarc' r θ₀ x) =
          (Hylin' (θ₀ + θc) x)).
  unfold Hyarc', Hylin'.
  unfold x.
  fieldrewrite (r * θc / r + θ₀) (θ₀ + θc).
  intro. subst. apply zner.  reflexivity.
  reflexivity.
  rewrite H.
  apply Hylin_deriv.

  (* values match at join point *)
  unfold Hyarc, Hylin. unfold x.
  fieldrewrite (r*θc/r) θc.
  intro. subst. apply zner.  reflexivity.
  setr(- r * cos (θc + θ₀) + r * cos θ₀ + y₀).
  reflexivity.

  (* right case *)
  intros nx1lex x1lex_dec ntlex tlex_dec ifl.
  assert (x < d) as xltt.
  clear tlex_dec.
  apply Rnot_le_lt in ntlex. assumption.

  assert (x < x1) as xltx1.
  clear x1lex_dec.
  apply Rnot_le_lt in nx1lex. assumption.

  clear linarc isderiveHyarc.
  unfold is_domin.
  intros eps.
  specialize (isderiveHylin x1 ifl eps).
  unfold locally, extension_cont.
  inversion_clear isderiveHylin as [eps0 isderivHylin''].
  set (zeta := Rmin eps0 ((d-x)/2)).
  assert (0<zeta) as zltzeta.
  unfold zeta, Rmin.
  destruct (Rle_dec eps0 ((d-x) / 2)).
  destruct eps0. simpl. lra.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (d-x). lra.
  exists (mkposreal zeta zltzeta).
  simpl. intros.

  rewrite tlex_dec, x1lex_dec.
  destruct (Rle_dec y x).

  exfalso.
  assert (Rabs (y - d) < zeta) as ballzetac. apply H.
  unfold zeta,Rmin in ballzetac.
  destruct (Rle_dec eps0 ((d-x)/2)).

  unfold Rabs in ballzetac.
  destruct (Rcase_abs (y - d)).
  assert (d - y < eps0) as ymtlteps0.
  lra. clear ballzetac.

  assert (2*eps0 <= d-x).
  apply (Rmult_le_reg_l (1/2)). lra.
  setl eps0. setr ((d-x) / 2). assumption.
  unfold x in *. lra.
  unfold x in *. lra.

  apply Rnot_le_lt in n.
  unfold Rabs in ballzetac.
  destruct (Rcase_abs (y - d)).
  assert (d - y < (d - x)/2) as ymtltxmt2.
  lra. 

  assert (2*d - 2*y < d - x).
  apply (Rmult_lt_reg_l (1/2)). lra.
  setl (d-y). setr ((d - x) / 2).
  assumption. clear ymtltxmt2.
  unfold x in *.
  lra.
  unfold x in *. lra.

  assert (ball d eps0 y) as ballteps0.
  unfold zeta, Rmin in H.
  destruct (Rle_dec eps0 ((d-x)/2)).
  assumption.
  assert (Rabs (y - d) < eps0).
  apply Rnot_le_lt in n.
  apply Rnot_le_lt in n0.
  apply (Rlt_trans _ ((d-x)/2)); assumption.
  assumption.

  apply isderivHylin''. assumption.
Qed.


Theorem Hxarc'_cont : forall  (r θ₀ d :R),
    continuous (Hxarc' r θ₀) d.
Proof.
  intros.
  set (f := (Hxarc' r θ₀)).
  assert (continuity_pt f d). unfold f, Hxarc'. reg.
  apply continuity_pt_impl_continuous_pt. assumption.
Qed.

Theorem Hyarc'_cont : forall (r θ₀ d :R),
    continuous (Hyarc' r θ₀) d.
Proof.
  intros.
  set (f := (Hyarc' r θ₀)).
  assert (continuity_pt f d). unfold f, Hyarc'. reg.
  apply continuity_pt_impl_continuous_pt. assumption.
Qed.

Theorem Hxlin'_cont : forall (θ₀ K d :R),
    continuous (Hxlin' θ₀) d.
Proof.
  intros.
  set (f := (Hxlin' θ₀)).
  assert (continuity_pt f d). unfold f, Hxlin'. reg.
  apply continuity_pt_impl_continuous_pt. assumption.
Qed.

Theorem Hylin'_cont : forall (θ₀ K d :R),
    continuous (Hylin' θ₀) d.
Proof.
  intros.
  set (f := (Hylin' θ₀)).
  assert (continuity_pt f d). unfold f, Hylin'. reg.
  apply continuity_pt_impl_continuous_pt. assumption.
Qed.


Lemma Hx'_cont : forall r θ₀ θc (zltr : 0<r) rtp (d:R), 
    continuous (Hx' r θ₀ θc rtp) d.
Proof.
  intros.
  unfold Hx'.

  change (continuous
            (extension_cont
               (Hxarc' r θ₀)
               (Hxlin' (θ₀ + θc))
               (r * θc))
            d).

  case_eq (Rle_dec d (r*θc)). intros.
  inversion r0.

  (* left case *)
  generalize (Hxarc'_cont r θ₀ d) as iscontHx'arc. intros.
  unfold continuous, extension_cont, locally, filterlim,
         filtermap, filter_le in *.
  intro P.
  specialize (iscontHx'arc P).
  rewrite H.
  intro head.
  specialize (iscontHx'arc head).
  inversion_clear head as [eps' Hxball].
  inversion_clear iscontHx'arc as [del iscontHx'arc'].
  set (m := ((r*θc)-d)/2).
  assert (0 < m) as zltxmt2. unfold m.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (r * θc - d). lra.
  set (zeta := (if Rle_dec del m then del
                else (mkposreal m zltxmt2))) in *.
  assert (zeta <= del) as zledel.
  unfold zeta; destruct (Rle_dec del m); simpl; try lra.
  (* apply Rnot_le_lt in n. left. assumption. *)
  assert (zeta <= m) as zlexmt2.
  unfold zeta; destruct (Rle_dec del m);
    try apply Rnot_le_lt in n; try assumption.
  simpl. right. reflexivity.
  assert (0 < zeta) as zltzeta.
  destruct (Rle_dec del m). destruct del. simpl. lra.
  destruct zeta. simpl. lra.
  exists zeta.
  intros.
  assert (ball d del y) as balltdely.
  assert (Rabs (y - d) < zeta). apply H1.
  assert (Rabs (y - d) < del). lra.
  apply H3.
  specialize (iscontHx'arc' y balltdely).

  destruct (Rle_dec y (r * θc)). assumption.
  exfalso.
  apply Rnot_le_lt in n.

  destruct zeta. simpl in *. 
  assert (2*pos <=  (r * θc - d)).
  apply (Rmult_le_reg_l (1/2)). lra.
  setl pos. setr ((r * θc - d)/2). change (pos <= m).
  assumption.

  assert (y - d < pos).
  assert (Rabs (y - d) < pos). apply H1.
  unfold Rabs in H3. destruct (Rcase_abs (y - d)).
  lra. assumption.
  lra.

  (* center case  *)
  subst.
  apply extension_cont_continuous.
  apply Hxarc'_cont; assumption.
  apply Hxlin'_cont; assumption.
  unfold Hxarc', Hxlin'.
  fieldrewrite (r * θc / r) (θc). intro. lra.
  fieldrewrite (θc + θ₀) (θ₀ + θc). reflexivity.

  (* right case *)
  intros.
  assert ((r * θc) < d) as xltt.
  clear H.
  apply Rnot_le_lt in n. assumption.

  generalize (Hxlin'_cont (θ₀+θc) (r*θc) d)
    as iscontHx'lin.
  intros.
  unfold continuous, extension_cont, locally, filterlim,
         filtermap, filter_le in *.
  intro P.
  specialize (iscontHx'lin P).
  rewrite H.
  intro head.
  specialize (iscontHx'lin head).
  inversion_clear head as [eps' Hxball].
  inversion_clear iscontHx'lin as [del iscontHx'lin'].

  set (m := (d-(r*θc))/2).
  assert (0 < m) as zltxmt2. unfold m.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (d - r * θc). lra.
  set (zeta := (if Rle_dec del m then del
                else (mkposreal m zltxmt2))) in *.
  assert (zeta <= del) as zledel.
  unfold zeta; destruct (Rle_dec del m); simpl; try lra.
  (* apply Rnot_le_lt in n0. left. assumption. *)
  assert (zeta <= m) as zlexmt2.
  unfold zeta; destruct (Rle_dec del m);
    try apply Rnot_le_lt in n; try assumption.
  simpl. right. reflexivity.
  assert (0 < zeta) as zltzeta.
  destruct (Rle_dec del m). destruct del. simpl. lra.
  destruct zeta. simpl. lra.
  exists zeta.
  intros.
  assert (ball d del y) as balltdely.
  assert (Rabs (y - d) < zeta). apply H0.
  assert (Rabs (y - d) < del). lra.
  apply H2.
  specialize (iscontHx'lin' y balltdely).

  destruct (Rle_dec y (r * θc)).
  inversion_clear r0.
  (****)
  exfalso.
  clear Hxball iscontHx'lin'.
  assert (d - y < zeta).
  assert (Rabs (y - d) < zeta). apply H0.
  unfold Rabs in H2.
  destruct (Rcase_abs (y - d)); lra.
  assert (2*zeta<= d - (r * θc)). 
  apply (Rmult_le_reg_l (1/2)). lra.
  setl zeta. setr ((d - r * θc)/2). change (zeta <= m).
  assumption.
  lra.

  subst. unfold Hxarc' in *.
  unfold Hxlin' in iscontHx'lin'.
  fieldrewrite (r * θc / r + θ₀) (θ₀ + θc).
  intro. lra.
  assumption.
  assumption.
Qed.

Lemma Hy'_cont : forall r θ₀ θc (zltr : 0<r) rtp (d:R), 
    continuous (Hy' r θ₀ θc rtp) d.
Proof.
  intros.
  unfold Hy'.

  change (continuous
            (extension_cont
               (Hyarc' r θ₀)
               (Hylin' (θ₀ + θc))
               (r * θc))
            d).

  case_eq (Rle_dec d (r*θc)). intros.
  inversion r0.

  (* left case *)
  generalize (Hyarc'_cont r θ₀ d) as iscontHy'arc. intros.
  unfold continuous, extension_cont, locally, filterlim,
         filtermap, filter_le in *.
  intro P.
  specialize (iscontHy'arc P).
  rewrite H.
  intro head.
  specialize (iscontHy'arc head).
  inversion_clear head as [eps' Hxball].
  inversion_clear iscontHy'arc as [del iscontHy'arc'].
  set (m := ((r*θc)-d)/2).
  assert (0 < m) as zltxmt2. unfold m.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (r * θc - d). lra.
  set (zeta := (if Rle_dec del m then del
                else (mkposreal m zltxmt2))) in *.
  assert (zeta <= del) as zledel.
  unfold zeta; destruct (Rle_dec del m); simpl; try lra.
  (* apply Rnot_le_lt in n. left. assumption. *)
  assert (zeta <= m) as zlexmt2.
  unfold zeta; destruct (Rle_dec del m);
    try apply Rnot_le_lt in n; try assumption.
  simpl. right. reflexivity.
  assert (0 < zeta) as zltzeta.
  destruct (Rle_dec del m). destruct del. simpl. lra.
  destruct zeta. simpl. lra.
  exists zeta.
  intros.
  assert (ball d del y) as balltdely.
  assert (Rabs (y - d) < zeta). apply H1.
  assert (Rabs (y - d) < del). lra.
  apply H3.
  specialize (iscontHy'arc' y balltdely).

  destruct (Rle_dec y (r * θc)). assumption.
  exfalso.
  apply Rnot_le_lt in n.

  destruct zeta. simpl in *. 
  assert (2*pos <=  (r * θc - d)).
  apply (Rmult_le_reg_l (1/2)). lra.
  setl pos. setr ((r * θc - d)/2). change (pos <= m).
  assumption.

  assert (y - d < pos).
  assert (Rabs (y - d) < pos). apply H1.
  unfold Rabs in H3. destruct (Rcase_abs (y - d)).
  lra. assumption.
  lra.

  (* center case  *)
  subst.
  apply extension_cont_continuous.
  apply Hyarc'_cont; assumption.
  apply Hylin'_cont; assumption.
  unfold Hyarc', Hylin'.
  fieldrewrite (r * θc / r) (θc). intro. lra.
  fieldrewrite (θc + θ₀) (θ₀ + θc). reflexivity.

  (* right case *)
  intros.
  assert ((r * θc) < d) as xltt.
  clear H.
  apply Rnot_le_lt in n. assumption.

  generalize (Hylin'_cont (θ₀+θc) (r*θc) d)
    as iscontHy'lin.
  intros.
  unfold continuous, extension_cont, locally, filterlim,
         filtermap, filter_le in *.
  intro P.
  specialize (iscontHy'lin P).
  rewrite H.
  intro head.
  specialize (iscontHy'lin head).
  inversion_clear head as [eps' Hxball].
  inversion_clear iscontHy'lin as [del iscontHy'lin'].

  set (m := (d-(r*θc))/2).
  assert (0 < m) as zltxmt2. unfold m.
  apply (Rmult_lt_reg_l 2). lra.
  setl 0. setr (d - r * θc). lra.
  set (zeta := (if Rle_dec del m then del
                else (mkposreal m zltxmt2))) in *.
  assert (zeta <= del) as zledel.
  unfold zeta; destruct (Rle_dec del m); simpl; try lra.
  (* apply Rnot_le_lt in n0. left. assumption. *)
  assert (zeta <= m) as zlexmt2.
  unfold zeta; destruct (Rle_dec del m);
    try apply Rnot_le_lt in n; try assumption.
  simpl. right. reflexivity.
  assert (0 < zeta) as zltzeta.
  destruct (Rle_dec del m). destruct del. simpl. lra.
  destruct zeta. simpl. lra.
  exists zeta.
  intros.
  assert (ball d del y) as balltdely.
  assert (Rabs (y - d) < zeta). apply H0.
  assert (Rabs (y - d) < del). lra.
  apply H2.
  specialize (iscontHy'lin' y balltdely).

  destruct (Rle_dec y (r * θc)).
  inversion_clear r0.
  (****)
  exfalso.
  clear Hxball iscontHy'lin'.
  assert (d - y < zeta).
  assert (Rabs (y - d) < zeta). apply H0.
  unfold Rabs in H2.
  destruct (Rcase_abs (y - d)); lra.
  assert (2*zeta<= d - (r * θc)). 
  apply (Rmult_le_reg_l (1/2)). lra.
  setl zeta. setr ((d - r * θc)/2). change (zeta <= m).
  assumption.
  lra.

  subst. unfold Hyarc' in *.
  unfold Hxlin' in iscontHy'lin'.
  fieldrewrite (r * θc / r + θ₀) (θ₀ + θc).
  intro. lra.
  assumption.
  assumption.
Qed.


(**
Trajectories J are parameterized by time, defined in terms of path H
and the relationship between speed and distance.
*)
Definition Jx r θ₀ x₀ θc rtp s t := Hx r θ₀ x₀ θc rtp (RInt s 0 t).
Definition Jy r θ₀ y₀ θc rtp s t := Hy r θ₀ y₀ θc rtp (RInt s 0 t).

Definition Jx' r θ₀ θc rtp s t := (s t)*(Hx' r θ₀ θc rtp (RInt s 0 t)).
Definition Jy' r θ₀ θc rtp s t := (s t)*(Hy' r θ₀ θc rtp (RInt s 0 t)).

(** Derivatives and continuity for trajectory J and components *)

Lemma Jx_cont : forall r θ₀ x₀ θc (s d:R->R) (zner : 0<>r) rtp (t:R)
    (conts : forall q, continuous s q)
    (isRInts : forall q, is_RInt s 0 q (d q)),
    continuous (Jx r θ₀ x₀ θc rtp s) t.
Proof.
  intros. unfold Jx.
  assert (d = RInt s 0) as ddef.
  apply functional_extensionality.
  intros. symmetry.
  apply is_RInt_unique. apply isRInts.

  (* assert (s = Derive d) as sdef. *)
  (* apply functional_extensionality. *)
  (* intros. symmetry. *)
  (* rewrite ddef. *)
  (* apply Derive_RInt. *)
  (* exists (mkposreal r zltr). *)
  (* intros. *)
  (* exists (d y). *)
  (* apply (isRInts y). *)
  (* apply conts. *)

  apply continuous_comp.
  rewrite <- ddef.
  apply (continuous_RInt_1 s 0 t d).
  assert (0 < 1) as zlt1. lra.
  exists (mkposreal 1 zlt1).
  intros.
  apply isRInts.
  apply Hx_cont.
Qed.

Lemma Jy_cont : forall r θ₀ y₀ θc (s d:R->R) (zner : 0<>r) rtp (t:R)
    (conts : forall q, continuous s q)
    (isRInts : forall q, is_RInt s 0 q (d q)),
    continuous (Jy r θ₀ y₀ θc rtp s) t.
Proof.
  intros. unfold Jy.
  assert (d = RInt s 0) as ddef.
  apply functional_extensionality.
  intros. symmetry.
  apply is_RInt_unique. apply isRInts.

  (* assert (s = Derive d) as sdef. *)
  (* apply functional_extensionality. *)
  (* intros. symmetry. *)
  (* rewrite ddef. *)
  (* apply Derive_RInt. *)
  (* exists (mkposreal r zltr). *)
  (* intros. *)
  (* exists (d y). *)
  (* apply (isRInts y). *)
  (* apply conts. *)

  apply continuous_comp.
  rewrite <- ddef.
  apply (continuous_RInt_1 s 0 t d).
  assert (0 < 1) as zlt1. lra.
  exists (mkposreal 1 zlt1).
  intros.
  apply isRInts.
  apply Hy_cont.
Qed.

Lemma Jx_deriv : forall r θ₀ x₀ θc (s d:R->R) (zner : 0<>r) rtp (t:R)
    (conts : forall q, continuous s q)
    (isRInts : forall q, is_RInt s 0 q (d q)),
    is_derive (Jx r θ₀ x₀ θc rtp s) t (Jx' r θ₀ θc rtp s t).
Proof.
  intros.
  unfold Jx,Jx'.

  assert (d = RInt s 0) as ddef.
  apply functional_extensionality.
  intros. symmetry.
  apply is_RInt_unique. apply isRInts.

  (* assert (s = Derive d) as sdef. *)
  (* apply functional_extensionality. *)
  (* intros. symmetry. *)
  (* rewrite ddef. *)
  (* apply Derive_RInt. *)
  (* exists (mkposreal r zltr). *)
  (* intros. *)
  (* exists (d y). *)
  (* apply (isRInts y). *)
  (* apply conts. *)


  change (is_derive (fun t0 : R =>
                       (Hx r θ₀ x₀ θc rtp) ((RInt s 0) t0)) t
                    (scal (s t) (Hx' r θ₀ θc rtp (RInt s 0 t)))).
  apply (is_derive_comp (Hx r θ₀ x₀ θc rtp)).
  apply Hx_deriv.

  rewrite <- ddef.
  apply (is_derive_RInt s d 0 t).
  assert (0 < 1) as zlt1. lra.
  exists (mkposreal 1 zlt1).
  intros. apply isRInts. apply conts.
Qed.

Lemma Jy_deriv : forall r θ₀ y₀ θc (s d:R->R) (zner : 0<>r) rtp (t:R)
    (conts : forall q, continuous s q)
    (isRInts : forall q, is_RInt s 0 q (d q)),
    is_derive (Jy r θ₀ y₀ θc rtp s) t (Jy' r θ₀ θc rtp s t).
Proof.
  intros.
  unfold Jy,Jy'.

  assert (d = RInt s 0) as ddef.
  apply functional_extensionality.
  intros. symmetry.
  apply is_RInt_unique. apply isRInts.

  (* assert (s = Derive d) as sdef. *)
  (* apply functional_extensionality. *)
  (* intros. symmetry. *)
  (* rewrite ddef. *)
  (* apply Derive_RInt. *)
  (* exists (mkposreal r zltr). *)
  (* intros. *)
  (* exists (d y). *)
  (* apply (isRInts y). *)
  (* apply conts. *)


  change (is_derive (fun t0 : R =>
                       (Hy r θ₀ y₀ θc rtp) ((RInt s 0) t0)) t
                    (scal (s t) (Hy' r θ₀ θc rtp (RInt s 0 t)))).
  apply (is_derive_comp (Hy r θ₀ y₀ θc rtp)).
  apply Hy_deriv.

  rewrite <- ddef.
  apply (is_derive_RInt s d 0 t).
  assert (0 < 1) as zlt1. lra.
  exists (mkposreal 1 zlt1).
  intros. apply isRInts. apply conts.
Qed.

(* begin hide *)

Lemma d_RInt_helper : forall s d r θ₀ θc rtp t 
    (spos : forall q, 0 <= s q)
    (conts : forall q, continuous s q)
    (isRInts : forall q, is_RInt s 0 q (d q)),
  s t = sqrt ((s t * Hx' r θ₀ θc rtp (d t))² + (s t * Hy' r θ₀ θc rtp (d t))²).
Proof.
  intros.
  unfold Hx',Hy', extension_cont.
  destruct (Rle_dec (d t) (r*θc)).

  unfold Hxarc', Hyarc'.
  unfold Rsqr.
  fieldrewrite (s t * cos (d t / r + θ₀) * (s t * cos (d t / r + θ₀)) +
                s t * sin (d t / r + θ₀) * (s t * sin (d t / r + θ₀)))
               (s t * s t * ((sin (d t / r + θ₀) * sin (d t / r + θ₀)) +
                             (cos (d t / r + θ₀) * cos (d t / r + θ₀))
                             )).
  change (s t = sqrt ((s t)² *
                      ((sin (d t / r + θ₀))² + (cos (d t / r + θ₀))²))).
  rewrite sin2_cos2.
  fieldrewrite ((s t)² * 1) ((s t)²).
  rewrite sqrt_Rsqr. reflexivity. apply spos.

  unfold Hxlin', Hylin'.
  unfold Rsqr.
  fieldrewrite (s t * cos (θ₀+θc) * (s t * cos (θ₀+θc)) +
                s t * sin (θ₀+θc) * (s t * sin (θ₀+θc)))
               (s t * s t * ((sin (θ₀+θc) * sin (θ₀+θc)) +
                             (cos (θ₀+θc) * cos (θ₀+θc))
                             )).
  change (s t = sqrt ((s t)² *
                      ((sin (θ₀+θc))² + (cos (θ₀+θc))²))).
  rewrite sin2_cos2.
  fieldrewrite ((s t)² * 1) ((s t)²).
  rewrite sqrt_Rsqr. reflexivity. apply spos.
Qed.
(* end hide *)

(*
Our trajectory has the following properties: x(t) continuous, y(t)
continuous, x'(t) exists and is integrable, y'(t) exists and is
integrable, s is continuous and non-negative

int_0^t sqrt ( (dx/dt)^2 + (dy/dt)^2) dt = distance
                                         = RInt_0^t s q dq
 *)
(** This is an unsurprising property: the path integral of any such
parameterized path results in the path length in the trajectory at
that time. *)

Lemma J_d_equiv : forall r θ₀ x₀ y₀ θc (s d:R->R) (zner : 0<>r) rtp (t:R)
    (zles : forall q, 0 <= s q)
    (conts : forall q, continuous s q)
    (isRInts : forall q, is_RInt s 0 q (d q)),
    is_RInt (magnitude (Derive (Jx r θ₀ x₀ θc rtp s))
                       (Derive (Jy r θ₀ y₀ θc rtp s))) 0 t
            (d t).
Proof.
  intros.
  assert (Derive (Jy r θ₀ y₀ θc rtp s) = (Jy' r θ₀ θc rtp s)) as DJy.
  apply functional_extensionality. intros.
  apply (is_derive_unique (Jy r θ₀ y₀ θc rtp s)).
  apply (Jy_deriv _ _ _ _ _ d); assumption.

  assert (Derive (Jx r θ₀ x₀ θc rtp s) = (Jx' r θ₀ θc rtp s)) as DJx.
  apply functional_extensionality. intros.
  apply (is_derive_unique (Jx r θ₀ x₀ θc rtp s)).
  apply (Jx_deriv _ _ _ _ _ d); assumption.

  rewrite DJy, DJx.
  apply (is_RInt_ext s); [
    intros; apply d_RInt_helper; try assumption |
    apply isRInts].
  intros. apply (RInt_correct s).
  exists (d q). apply isRInts.
Qed.

(**
For every point in the trajectory there is a point 
in the distance-parameterized path.
*)
Lemma J_H_equiv : forall r θ₀ x₀ θc rtp (s :R->R) (t:R),
    exists d, Jx r θ₀ x₀ θc rtp s t = Hx r θ₀ x₀ θc rtp d /\
              Jy r θ₀ x₀ θc rtp s t = Hy r θ₀ x₀ θc rtp d.
Proof.
  intros. exists (RInt s 0 t). unfold Jx,Jy. split; reflexivity.
Qed.

(**
Properties about time and distance for speed functions that are
non-negative or positive.
*)

Lemma snneg_d_nondecreasing : forall (s d:R->R) (t₁ t₂:R)
    (zles : forall q, 0 <= s q)
    (conts : forall q, continuous s q)
    (isRInts : forall q, is_RInt s 0 q (d q))
    (tordering : 0 <= t₁ < t₂),
  d t₁ <= d t₂.
Proof.
  intros. inversion_clear tordering as [zlet1 t1ltt2].
  assert (d = RInt s 0) as ddef.
  apply functional_extensionality.
  intros. symmetry.
  apply is_RInt_unique. apply isRInts.

  assert (s = Derive d) as sdef.
  apply functional_extensionality.
  intros. symmetry.
  rewrite ddef.
  apply Derive_RInt.
  assert (0 < 1) as zlt1. lra.
  exists (mkposreal 1 zlt1).
  intros.
  exists (d y).
  apply (isRInts y).
  apply conts.

  rewrite ddef.

  assert (ex_RInt s 0 t₁) as zt1nneg.
  exists (d t₁). apply isRInts.
  assert (forall x : R, 0 < x < t₁ -> 0 <= s x) as snneg.
  intros. apply zles.
  generalize (RInt_ge_0 s 0 t₁ zlet1 zt1nneg snneg) as RInt0t1nneg.
  intros.

  assert (ex_RInt s t₁ t₂) as t1t2nneg.
  exists (minus (d t₂) (d t₁)).
  inversion_clear zlet1 as [zltt1 | zeqt1].
  apply (is_RInt_Chasles_2 s 0 t₁ t₂ (d t₂) (d t₁)). split; lra.
  apply isRInts. apply isRInts.

  rewrite ddef. rewrite <- zeqt1.
  rewrite RInt_point. unfold minus, plus, zero, opp. simpl.
  fieldrewrite (RInt s 0 t₂ + - 0) (RInt s 0 t₂).
  apply (RInt_correct s).
  exists (d t₂). apply isRInts.

  assert (t₁ <= t₂) as t1let2. lra.
  assert (forall x : R, t₁ < x < t₂ -> 0 <= s x) as snneg12.
  intros. apply zles.
  generalize (RInt_ge_0 s t₁ t₂ t1let2 t1t2nneg snneg12) as RIntt1t2nneg. intros.

  rewrite <- (RInt_Chasles s 0 t₁ t₂); auto.
  unfold plus. simpl.
  lra.
Qed.

Lemma spos_d_increasing : forall (s d:R->R) (t₁ t₂:R)
    (zlts : forall q, 0 < s q)
    (conts : forall q, continuous s q)
    (isRInts : forall q, is_RInt s 0 q (d q))
    (tordering : 0 <= t₁ < t₂),
  d t₁ < d t₂.
Proof.
  intros. inversion_clear tordering as [zlet1 t1ltt2].
  assert (d = RInt s 0) as ddef.
  apply functional_extensionality.
  intros. symmetry.
  apply is_RInt_unique. apply isRInts.

  assert (s = Derive d) as sdef.
  apply functional_extensionality.
  intros. symmetry.
  rewrite ddef.
  apply Derive_RInt.
  assert (0 < 1) as zlt1. lra.
  exists (mkposreal 1 zlt1).
  intros.
  exists (d y).
  apply (isRInts y).
  apply conts.

  rewrite ddef.

  assert (ex_RInt s 0 t₁) as zt1nneg.
  exists (d t₁). apply isRInts.

  assert (forall x : R, 0 < x < t₁ -> 0 < s x) as spos.
  intros. apply zlts.
  assert (forall x : R, 0 <= x <= t₁ -> continuous s x) as conts2.
  intros. apply conts.
  inversion_clear zlet1 as [zltt1 | zeqt1].
  generalize (RInt_gt_0 s 0 t₁ zltt1 spos conts2) as RInt0t1pos.
  intros.

  assert (ex_RInt s t₁ t₂) as t1t2nneg.
  exists (minus (d t₂) (d t₁)).
  apply (is_RInt_Chasles_2 s 0 t₁ t₂ (d t₂) (d t₁)). split; assumption.
  apply isRInts. apply isRInts.
  
  assert (t₁ <= t₂) as t1let2. lra.
  assert (forall x : R, t₁ < x < t₂ -> 0 < s x) as spos12.
  intros. apply zlts.
  assert (forall x : R, t₁ <= x <= t₂ -> continuous s x) as conts3.
  intros. apply conts.

  rewrite <- (RInt_Chasles s 0 t₁ t₂); auto.
  unfold plus. simpl.
  apply (Rplus_lt_reg_l (- RInt s 0 t₁)).
  setl 0. setr (RInt s t₁ t₂).
  apply (RInt_gt_0 s t₁ t₂ t1ltt2 spos12 conts3).

  rewrite <- zeqt1.
  rewrite RInt_point. unfold minus, plus, zero, opp. simpl.
  assert (forall x : R, 0 <= x <= t₂ -> continuous s x) as conts3.
  intros. apply conts.
  assert (forall x : R, 0 < x < t₂ -> 0 < s x) as spos02.
  intros. apply zlts.
  assert (0 < t₂) as zltt2. lra.
  apply (RInt_gt_0 s 0 t₂ zltt2 spos02 conts3).
Qed.

(**
The lengths of paths and path components, showing distance parameterization.
*)
Lemma H_arclen : forall r θ₀ x₀ y₀ a b
                        (zner : 0 <> r),
    is_RInt (magnitude (Derive (Hxarc r θ₀ x₀))
                       (Derive (Hyarc r θ₀ y₀))) a b
            (b - a).
Proof.
  intros.
  assert (Derive (Hxarc r θ₀ x₀) = Hxarc' r θ₀) as deriveHx.
  apply functional_extensionality. intro q.
  rewrite (is_derive_unique (Hxarc r θ₀ x₀) q  (Hxarc' r θ₀ q)
                            (Hxarc_deriv r θ₀ x₀ q zner)). reflexivity.
  assert (Derive (Hyarc r θ₀ y₀) = Hyarc' r θ₀) as deriveHy.
  apply functional_extensionality. intro q.
  rewrite (is_derive_unique (Hyarc r θ₀ y₀) q  (Hyarc' r θ₀ q)
                            (Hyarc_deriv r θ₀ y₀ q zner)); reflexivity.
  rewrite deriveHx, deriveHy.
  unfold Hxarc', Hyarc', magnitude, comp, plus_fct.
  assert ( (fun _ => 1) = (fun x : R => sqrt ((cos (x / r + θ₀))² + (sin (x / r + θ₀))²))) as constf.
  apply functional_extensionality. intro q.
  fieldrewrite ((cos (q / r + θ₀))² + (sin (q / r + θ₀))²)
               ((sin (q / r + θ₀))² + (cos (q / r + θ₀))²).
  rewrite sin2_cos2. symmetry. apply sqrt_1.
  apply (is_RInt_ext (fun _ => 1)).
  intros.
  change (1 = (fun x : R => sqrt ((cos (x / r + θ₀))² + (sin (x / r + θ₀))²)) x).
  rewrite <- constf. reflexivity.
  generalize (is_RInt_const a b 1) as RIntconst.
  intros. unfold scal in RIntconst. simpl in RIntconst.
  unfold mult in RIntconst. simpl in RIntconst.
  fieldrewrite (b-a) ((b-a)*1).
  assumption.
Qed.

Lemma H_linlen' : forall θ₀ x₀ y₀ a b K,
    is_RInt (magnitude (Derive (fun q => (Hxlin θ₀ x₀ (q - K))))
                       (Derive (fun q => (Hylin θ₀ y₀ (q - K))))) a b
            (b - a).
Proof.
  intros.
  assert (Derive (fun q => (Hxlin θ₀ x₀ (q-K))) = (fun q => (Hxlin' θ₀ (q-K)))) as deriveHx.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (fun q => (Hxlin θ₀ x₀ (q-K))) q  (Hxlin' θ₀ q)
                          (Hxlin_deriv θ₀ x₀ K q)).
  assert (Derive (fun q => (Hylin θ₀ y₀ (q-K))) = (fun q => (Hylin' θ₀ (q-K)))) as deriveHy.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (fun q => (Hylin θ₀ y₀ (q-K))) q  (Hylin' θ₀ q)
                          (Hylin_deriv θ₀ y₀ K q)).
  rewrite deriveHx, deriveHy.
  unfold Hxlin', Hylin', magnitude, comp, plus_fct.
  assert ( (fun _ => 1) = (fun x : R => sqrt ((cos θ₀)² + (sin θ₀)²))) as constf.
  apply functional_extensionality. intro q.
  fieldrewrite ((cos (θ₀))² + (sin (θ₀))²)
               ((sin (θ₀))² + (cos (θ₀))²).
  rewrite sin2_cos2. symmetry. apply sqrt_1.
  apply (is_RInt_ext (fun _ => 1)).
  intros.
  change (1 = (fun x : R => sqrt ((cos (θ₀))² +
                                  (sin (θ₀))²)) x).
  rewrite <- constf. reflexivity.
  generalize (is_RInt_const a b 1) as RIntconst.
  intros. unfold scal in RIntconst. simpl in RIntconst.
  unfold mult in RIntconst. simpl in RIntconst.
  fieldrewrite (b-a) ((b-a)*1).
  assumption.
Qed.


Lemma H_linlen : forall θ₀ x₀ y₀ a b,
    is_RInt (magnitude (Derive (Hxlin θ₀ x₀))
                       (Derive (Hylin θ₀ y₀))) a b
            (b - a).
Proof.
  intros.
  assert (Derive (Hxlin θ₀ x₀) = (Hxlin' θ₀)) as deriveHx.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (Hxlin θ₀ x₀) q  (Hxlin' θ₀ q)).
  assert ((fun q : R_AbsRing => Hxlin θ₀ x₀ (q - 0)) = Hxlin θ₀ x₀) as subzero.
  apply functional_extensionality. intros. fieldrewrite (x - 0) x. reflexivity.
  rewrite <- subzero.
  apply (Hxlin_deriv θ₀ x₀ 0 q).
  
  assert (Derive (Hylin θ₀ y₀) = (Hylin' θ₀)) as deriveHy.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (Hylin θ₀ y₀) q  (Hylin' θ₀ q)).
  assert ((fun q : R_AbsRing => Hylin θ₀ y₀ (q - 0)) = Hylin θ₀ y₀) as subzero.
  apply functional_extensionality. intros. fieldrewrite (x - 0) x. reflexivity.
  rewrite <- subzero.
  apply (Hylin_deriv θ₀ y₀ 0 q).
  rewrite deriveHx, deriveHy.
  unfold Hxlin', Hylin', magnitude, comp, plus_fct.
  assert ( (fun _ => 1) = (fun x : R => sqrt ((cos θ₀)² + (sin θ₀)²))) as constf.
  apply functional_extensionality. intro q.
  fieldrewrite ((cos (θ₀))² + (sin (θ₀))²)
               ((sin (θ₀))² + (cos (θ₀))²).
  rewrite sin2_cos2. symmetry. apply sqrt_1.
  apply (is_RInt_ext (fun _ => 1)).
  intros.
  change (1 = (fun x : R => sqrt ((cos (θ₀))² +
                                  (sin (θ₀))²)) x).
  rewrite <- constf. reflexivity.
  generalize (is_RInt_const a b 1) as RIntconst.
  intros. unfold scal in RIntconst. simpl in RIntconst.
  unfold mult in RIntconst. simpl in RIntconst.
  fieldrewrite (b-a) ((b-a)*1).
  assumption.
Qed.

(* begin hide *)

Lemma H_len_0 : forall r θ₀ θc x₀ y₀ d
    (blertc : 0 <= d <= (r*θc))
    rtp,
    is_RInt (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                       (Derive (Hy r θ₀ y₀ θc rtp))) 0 d
            d.
Proof.
  intros.

  addzner.
  inversion_clear blertc as [zled dlertc].
  inversion_clear zled as [zltd | zeqd].
  assert (Derive (Hx r θ₀ x₀ θc rtp) = (Hx' r θ₀ θc rtp)) as deriveHx.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (Hx r θ₀ x₀ θc rtp) q  (Hx' r θ₀ θc rtp q)
                          (Hx_deriv r θ₀ x₀ θc rtp q)).
  assert (Derive (Hy r θ₀ y₀ θc rtp) = (Hy' r θ₀ θc rtp)) as deriveHy.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (Hy r θ₀ y₀ θc rtp) q  (Hy' r θ₀ θc rtp q)
                          (Hy_deriv r θ₀ y₀ θc rtp q)).
  rewrite deriveHx, deriveHy. clear deriveHx deriveHy.
  assert (forall q, Rmin 0 d < q < Rmax 0 d ->
                    (magnitude (Derive (Hxarc r θ₀ x₀)) (Derive (Hyarc r θ₀ y₀))) q = 
                    (magnitude (Hx' r θ₀ θc rtp) (Hy' r θ₀ θc rtp)) q) as Harcpart.
  intros. unfold magnitude, comp, plus_fct, Hx', Hy', extension_cont.
  unfold Rmin, Rmax in H. destruct (Rle_dec 0 d). clear r0.
  destruct (Rle_dec q (r*θc)).

  rewrite (is_derive_unique _ _ _ (Hyarc_deriv r θ₀ y₀ q zner)).
  rewrite (is_derive_unique _ _ _ (Hxarc_deriv r θ₀ x₀ q zner)).
  reflexivity.

  exfalso.
  apply n. inversion_clear H. clear n. lra.
  exfalso. apply n. left. assumption. 
  apply (is_RInt_ext _ _ _ _ d Harcpart).
  assert (d=(d - 0)) as deqd. field. rewrite deqd at 2.

  apply (H_arclen _ θ₀ x₀ y₀ 0 d zner).

  subst.
  assert (0 = zero) as zeqz. unfold zero. simpl. reflexivity.
  rewrite zeqz at 3.
  apply (is_RInt_point (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                                  (Derive (Hy r θ₀ y₀ θc rtp))) 0).
Qed.


Lemma H_len_d : forall r θ₀ θc x₀ y₀ d
    (blertc : 0 <= (r*θc) < d)
    rtp,
    is_RInt (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                       (Derive (Hy r θ₀ y₀ θc rtp))) 0 d
            d.
Proof.
  intros.

  addzner.
  set (g := (r*θc)).
  set (e := minus d g).
  assert (d = plus g e) as ddef. unfold minus, plus, opp. simpl.
  unfold e,g, minus, plus, opp. simpl. field.
  rewrite ddef at 2.

  apply (is_RInt_Chasles (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                                    (Derive (Hy r θ₀ y₀ θc rtp))) 0 g d).
  apply H_len_0. unfold g. inversion_clear blertc as [zlertc rtcltd].
  split. assumption. right. reflexivity.
  (**************************)
  assert (Derive (Hx r θ₀ x₀ θc rtp) = (Hx' r θ₀ θc rtp)) as deriveHx.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (Hx r θ₀ x₀ θc rtp) q  (Hx' r θ₀ θc rtp q)
                          (Hx_deriv r θ₀ x₀ θc rtp q)).
  assert (Derive (Hy r θ₀ y₀ θc rtp) = (Hy' r θ₀ θc rtp)) as deriveHy.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (Hy r θ₀ y₀ θc rtp) q  (Hy' r θ₀ θc rtp q)
                          (Hy_deriv r θ₀ y₀ θc rtp q)).
  rewrite deriveHx, deriveHy. clear deriveHx deriveHy.

  assert (forall q, Rmin g d < q < Rmax g d ->
                    (magnitude (Derive (Hxlin (θ₀+θc) x₀))
                               (Derive (Hylin (θ₀+θc) y₀))) q = 
                    (magnitude (Hx' r θ₀ θc rtp) (Hy' r θ₀ θc rtp)) q) as Hlinpart.
  intros. unfold magnitude, comp, plus_fct, Hx', Hy', extension_cont.
  unfold Rmin, Rmax in H. destruct (Rle_dec g d). clear r0.
  destruct (Rle_dec q (r*θc)).

  exfalso.
  inversion_clear H. unfold g in *. lra.
  assert (Derive (Hxlin (θ₀+θc) x₀) = (Hxlin' (θ₀+θc))) as deriveHx.
  apply functional_extensionality. intro s.
  rewrite <- (is_derive_unique (fun q => Hxlin (θ₀+θc) x₀ (q-0)) s  (Hxlin' (θ₀+θc) s)
                               (Hxlin_deriv (θ₀+θc) x₀ 0 s)).
  assert ((fun q0 : R_AbsRing => Hxlin (θ₀ + θc) x₀ (q0 - 0)) =
          (Hxlin (θ₀ + θc) x₀)) as subzero.
  apply functional_extensionality. intros.
  fieldrewrite (x - 0) x. reflexivity.
  rewrite subzero. reflexivity.
  rewrite deriveHx.
  
  assert (Derive (Hylin (θ₀+θc) y₀) = (Hylin' (θ₀+θc))) as deriveHy.
  apply functional_extensionality. intro s.
  rewrite <- (is_derive_unique (fun q => Hylin (θ₀+θc) y₀ (q-0)) s
                               (Hylin' (θ₀+θc) s)
                               (Hylin_deriv (θ₀+θc) y₀ 0 s)).
  assert ((fun q0 : R_AbsRing => Hylin (θ₀ + θc) y₀ (q0 - 0)) =
          (Hylin (θ₀ + θc) y₀)) as subzero.
  apply functional_extensionality. intros.
  fieldrewrite (x - 0) x. reflexivity.
  rewrite subzero. reflexivity.
  rewrite deriveHy. reflexivity.

  exfalso.
  inversion_clear blertc as [zlertc rtcltd].
  inversion_clear H as [dltq qltg].
  unfold g in *. lra.

  apply (is_RInt_ext _ _ _ _ e Hlinpart).

  unfold e. clear ddef e.
  inversion_clear blertc as [zlertc rtcltd].
  inversion_clear zlertc.
  apply (is_RInt_Chasles_2 (magnitude (Derive (Hxlin (θ₀+θc) x₀)) (Derive (Hylin (θ₀+θc) y₀))) 0).
  unfold g. split; assumption.

  assert (d = d-0) as ddef. field.
  rewrite ddef at 2.
  apply (H_linlen (θ₀+θc) x₀ y₀ 0 d).

  assert (g = g-0) as gdef. field.
  rewrite gdef at 2.
  apply (H_linlen (θ₀+θc) x₀ y₀ 0 g).

  unfold g in *.
  rewrite <- H in *. clear H. unfold minus, plus, opp. simpl.
  fieldrewrite (d + - 0) (d - 0).
  apply (H_linlen (θ₀+θc) x₀ y₀ 0 d).
Qed.

Lemma H_len : forall r θ₀ θc x₀ y₀ d
    (zled : 0 <= d)
    (zlertc : 0 <= (r*θc))
    rtp,
    is_RInt (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                       (Derive (Hy r θ₀ y₀ θc rtp))) 0 d
            d.
Proof.
  intros.

  addzner.
  destruct (Rle_dec d (r*θc)).
  apply H_len_0. split; assumption.
  apply Rnot_le_lt in n.
  apply H_len_d. split; lra.
Qed.
(* end hide *)



Lemma H_d_equiv : forall r θ₀ x₀ y₀ θc (s d:R->R)
    (zner : 0<>r) rtp (zlertc : 0<=r*θc) (t:R)
    (zlet : 0 <= t)
    (zles : forall q, 0 <= s q)
    (conts : forall q, continuous s q)
    (isRInts : forall q, is_RInt s 0 q (d q)),
    is_RInt (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                       (Derive (Hy r θ₀ y₀ θc rtp))) (d 0) (d t)
            (d t).
Proof.
  intros.

  assert (d = RInt s 0) as ddef.
  apply functional_extensionality.
  intros. symmetry.
  apply is_RInt_unique. apply isRInts.

  assert (s = Derive d) as sdef.
  apply functional_extensionality.
  intros. symmetry.
  rewrite ddef.
  apply Derive_RInt.
  assert (0 < 1) as zlt1. lra.
  exists (mkposreal 1 zlt1).
  intros.
  exists (d y).
  apply (isRInts y).
  apply conts.

  assert (d 0 = 0) as d0eq0.
  rewrite ddef.
  apply is_RInt_unique.
  assert (0 = zero) as zeqz. unfold zero. simpl.
  reflexivity. rewrite zeqz at 3.
  apply (is_RInt_point s).
  rewrite d0eq0.
  assert (0 <= d t) as zledt.
  rewrite ddef.
  apply RInt_ge_0. assumption.
  exists (d t). apply isRInts.
  intros. apply zles.
  apply (H_len r θ₀ θc x₀ y₀ (d t) zledt zlertc rtp ).
Qed.


(* The lengths of paths, in terms of path integrals. The path integral
from 0 d has length d. Why do we need these integrals?  These are for
situations where we don't know d, and want to calculate it in terms of
other parameters of our problem. The assumptions constrain r and
thetac to be the same sign. Left turns are represented when both of
these terms are positive, and right turns when they are negative. *)

(** Express the length of the circular part of the path in terms of r
and theta. There are various expressions we can use for theta,
depending on what parameters we have available. *)

(** Theta in terms of d. But if we have d, we don't need to use this
expression to calculate d. This just emphasizes that theta is d/r. *)
Lemma H_len_0_1 : forall r θ₀ θc x₀ y₀ d
    (blertc : 0 <= d <= (r*θc))
    rtp,
    is_RInt (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                       (Derive (Hy r θ₀ y₀ θc rtp))) 0 d
            (r*(d/r)).
Proof.
  intros.

  addzner.
  fieldrewrite (r*(d/r)) d.
  intro. subst. apply zner. reflexivity.
  inversion_clear blertc.
  apply H_len; (assumption || lra).
Qed.



(** The length of the circular part of the path when the turn is less
than or equal to 180 degrees. Theta in terms of arcsin of final
position and initial positions. *)
Lemma H_len_0_2 : forall r θ₀ θc x₀ y₀ d
    (tcorder : -PI <= θc <= PI)
    (blertc : 0 <= d <= (r*θc))
    rtp,
    is_RInt (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                       (Derive (Hy r θ₀ y₀ θc rtp))) 0 d
            (r * 2 * asin (TI_map (1 / (2*r) * sqrt (((Hx r θ₀ x₀ θc rtp d) - x₀)² +
                                             ((Hy r θ₀ y₀ θc rtp d) - y₀)²)
            ))).
Proof.
  intros.

  addzner.
  unfold Hx at 2. unfold Hy at 2.
  unfold extension_cont.
  destruct (Rle_dec d (r * θc)).
  2: {
       exfalso.
       apply Rnot_le_lt in n.
       inversion_clear blertc.
       lra.
       }
  inversion_clear blertc as [zled dlertc].
  inversion_clear zled as [zltd | zeqd].

  assert (Derive (Hx r θ₀ x₀ θc rtp) = (Hx' r θ₀ θc rtp)) as deriveHx.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (Hx r θ₀ x₀ θc rtp) q  (Hx' r θ₀ θc rtp q)
                          (Hx_deriv r θ₀ x₀ θc rtp q)).
  assert (Derive (Hy r θ₀ y₀ θc rtp) = (Hy' r θ₀ θc rtp)) as deriveHy.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (Hy r θ₀ y₀ θc rtp) q  (Hy' r θ₀ θc rtp q)
                          (Hy_deriv r θ₀ y₀ θc rtp q)).
  rewrite deriveHx, deriveHy. clear deriveHx deriveHy.
  assert (forall q, Rmin 0 d < q < Rmax 0 d ->
                    (magnitude (Derive (Hxarc r θ₀ x₀))
                               (Derive (Hyarc r θ₀ y₀))) q =
                    (magnitude (Hx' r θ₀ θc rtp) (Hy' r θ₀ θc rtp)) q) as Harcpart.
  intros. unfold magnitude, comp, plus_fct, Hx', Hy', extension_cont.
  unfold Rmin, Rmax in H. destruct (Rle_dec 0 d). clear r0.
  destruct (Rle_dec q (r*θc)).

  rewrite (is_derive_unique _ _ _ (Hyarc_deriv r θ₀ y₀ q zner)).
  rewrite (is_derive_unique _ _ _ (Hxarc_deriv r θ₀ x₀ q zner)).
  reflexivity.

  exfalso.
  apply n. inversion_clear H. clear n. lra.
  exfalso. apply n. left. assumption.

  apply (is_RInt_ext _ _ _ _ _ Harcpart). clear Harcpart.

  apply (RInt_unique _ _ _ d).
  apply (Rmult_eq_reg_l (1/(r*2))).
  setl (d/(2*r)). intro. subst. apply zner. reflexivity.
  setr (asin (TI_map ( 1 / (2*r) * sqrt ((Hxarc r θ₀ x₀ d - x₀)² +
                                 (Hyarc r θ₀ y₀ d - y₀)²)))).
  intro. subst. apply zner. reflexivity.
  assert (sin (d / (2 * r)) = 1 / (2*r) * (sqrt ((Hxarc r θ₀ x₀ d - x₀)² +
                                                 (Hyarc r θ₀ y₀ d - y₀)²) ))
    as applyinverse.
  2 : {
        generalize (SIN_bound (d / (2 * r))) as sinbounds. intros.
        rewrite <- applyinverse.
        rewrite asin_sin_id_0. reflexivity.
        clear applyinverse sinbounds.
        inversion_clear tcorder.
        destruct (Rle_dec 0 r).
        inversion_clear r1.
        generalize PI_RGT_0. intros.
        split.
        apply (Rmult_le_reg_l (2 * r)).
        lra.
        setl (-PI * r). setr d.
        intro. apply zner. auto.
        setl (- (PI * r)).
        apply (Rle_trans _ 0). left.
        apply (Ropp_lt_gt_0_contravar (PI * r)).
        apply Rlt_gt.
        apply Rgt_lt in H2.
        apply Rmult_lt_0_compat; try assumption.
        left. assumption.

        apply (Rmult_le_reg_l (2 * r)).
        lra.
        setl d. intro. apply zner. symmetry. assumption.
        setr (PI*r).
        apply (Rle_trans _ (r * θc)). assumption.
        setr (r * PI).
        apply Rmult_le_compat_l. left. assumption. assumption.

        exfalso. subst. apply zner. reflexivity.

        apply Rnot_le_lt in n.
        split.
        apply (Rmult_le_reg_l 2). lra.
        setl (-PI). setr (d / r).
        intro. subst. lra.
        apply (Rle_trans _ θc). assumption.
        generalize (Rinv_lt_0_compat _ n) as divrneg. intro.
        setl (/r * (r * θc)). intro. subst. lra.
        setr (/r * d). intro. subst. lra.
        apply (Rmult_le_compat_neg_l (/r)). left. assumption.
        assumption.
        apply (Rle_trans _ 0).
        apply (Rmult_le_reg_l 2). lra.
        setr (/ r * 0). intro. subst. lra.
        setl (/ r * d). intro. subst. lra.
        generalize (Rinv_lt_0_compat _ n) as divrneg. intro.
        apply (Rmult_le_compat_neg_l (/r)). left. assumption.
        left. assumption.
        left. apply PI2_RGT_0.
        }
      
  unfold Hxarc,Hyarc.
  unfold Rsqr.
  fieldrewrite
    ((r * sin (d / r + θ₀) - r * sin θ₀ + x₀ - x₀) *
     (r * sin (d / r + θ₀) - r * sin θ₀ + x₀ - x₀) +
     (- r * cos (d / r + θ₀) + r * cos θ₀ + y₀ - y₀) *
     (- r * cos (d / r + θ₀) + r * cos θ₀ + y₀ - y₀))
    ((r * sin (d / r + θ₀) * r * sin (d / r + θ₀) -
      2 * r * sin (d / r + θ₀)* r * sin θ₀ + r * sin θ₀ *r * sin θ₀ ) +
     (r * cos (d / r + θ₀)* r * cos (d / r + θ₀) -
      2 * r * cos θ₀ * r * cos (d / r + θ₀) + r * cos θ₀ * r * cos θ₀)).
  assert
    ((r * sin (d / r + θ₀) * r * sin (d / r + θ₀) -
      2 * r * sin (d / r + θ₀) * r * sin θ₀ +
      r * sin θ₀ * r * sin θ₀ +
      (r * cos (d / r + θ₀) * r * cos (d / r + θ₀) -
       2 * r * cos θ₀ * r * cos (d / r + θ₀) +
       r * cos θ₀ * r * cos θ₀))=
     (r²*(((sin (d / r + θ₀))² + (cos (d / r + θ₀))²) +
          ((sin θ₀)² + (cos θ₀)²)) -
      2*r²* (cos (d / r + θ₀) * cos θ₀ + sin (d / r + θ₀) * sin θ₀)))
    as intoRsqr.
  unfold Rsqr. field.
  rewrite intoRsqr. clear intoRsqr.
  repeat rewrite sin2_cos2.
  rewrite <- cos_minus.
  fieldrewrite (d / r + θ₀ - θ₀) (d / r). intro. subst. apply zner. reflexivity.
  fieldrewrite (r² * (1 + 1) - 2 * r² * cos (d / r))
               (2*r²* (1 - cos (d / r))).
  fieldrewrite (d / r) (2 * (d / (2*r))).
  intro. subst. apply zner. reflexivity.
  rewrite cos_2a_sin.
  assert (2 * r² * (1 - (1 - 2 * sin (d / (2 * r)) * sin (d / (2 * r)))) =
          (2 * r * sin (d / (2 * r)))²) as sinRsqr.
  unfold Rsqr; field.
  rewrite sinRsqr. clear sinRsqr.
  
  generalize (total_order_T 0 r) as order0r. intros.
  inversion_clear order0r as [zger | zltr].
  inversion_clear zger as [zltr | zeqr].
  2 : { exfalso. subst. apply zner. reflexivity. }

  assert (0 < d / (2*r) <= PI) as d2rorder.
  split. 
  apply (Rmult_lt_reg_l (2*r)). lra.
  setl 0. setr d. intro. subst. lra.
  assumption.
  apply (Rmult_le_reg_l (2*r)). lra.
  setl d. intro. subst. lra.
  apply (Rle_trans _ (r * θc)). assumption.
  setr (r *(2*PI)).
  apply Rmult_le_compat_l. left. assumption.
  inversion_clear tcorder. lra.

  inversion_clear d2rorder as [zltd2r d2rlePI].
  inversion_clear d2rlePI as [d2rltPI | d2reqPI].
  2 : {
        rewrite d2reqPI.
        rewrite sin_PI.
        fieldrewrite (2 * r * 0) 0.
        rewrite (sqrt_Rsqr 0). field. intro. subst. lra.
        right. reflexivity.
        }

  generalize (sin_gt_0 (d / (2 * r)) zltd2r d2rltPI) as sinnonneg. intro.
  rewrite sqrt_Rsqr.
  setr (sin (d / (2 * r))). intro. subst. lra. reflexivity.

  apply Rmult_le_pos.
  apply Rmult_le_pos.
  left. lra. left. assumption. left. assumption.


  assert (-PI <= d / (2*r) < 0) as d2rorder.
  split.
  setl (/ r * (r * - PI)). intro. subst. lra.
  setr (/ r * (d / 2)). intro. subst. lra.
  apply Rgt_lt in zltr.
  generalize (Rinv_lt_0_compat r zltr) as divrneg. intro.
  apply (Rmult_le_compat_neg_l (/r)). left. assumption.
  apply (Rmult_le_reg_l 2). lra. setl d.
  apply (Rle_trans _ (r * θc)). assumption.
  setr (r * (-2 * PI)).
  apply Rmult_le_compat_neg_l. left. assumption.
  
  generalize (PI_RGT_0). intro.
  apply (Rle_trans _ (-PI)). lra.
  inversion_clear tcorder. assumption.
  setl ((/ r) * (/ 2 * d)). intro. subst. lra.
  setr (/r * 0). intro. subst. lra.
  apply Rgt_lt.
  generalize (Rinv_lt_0_compat r zltr) as divrneg. intro.
  apply Rmult_lt_gt_compat_neg_l. assumption. lra.

  inversion_clear d2rorder as [_PIled2r d2rlt0].
  inversion_clear _PIled2r as [_PIltd2r | _PIeqd2r].
  2 : {
        rewrite <- _PIeqd2r.
        rewrite sin_antisym.
        rewrite sin_PI.
        fieldrewrite (2 * r * -0) 0.
        rewrite (sqrt_Rsqr 0). field. intro. subst. lra.
        right. reflexivity.
        }

  assert (d / (2 * r) + 2*PI < 2*PI) as d2r'lt2PI.
  assert (2*PI = 0 + 2*PI). field. rewrite H at 2.
  apply Rplus_lt_compat_r. assumption.
  assert (PI < d / (2 * r) + 2*PI) as PIltd2r'.
  assert (PI = -PI + 2*PI). field. rewrite H at 1.
  apply Rplus_lt_compat_r. assumption.
  rewrite <- (sin_period _ 1).
  assert (2 * INR 1 * PI = 2*PI). unfold INR. field.
  rewrite H. clear H.
  generalize (sin_lt_0 (d / (2 * r) + 2 * PI) PIltd2r' d2r'lt2PI)
    as sinnonpos. intro.
  rewrite sqrt_Rsqr.
  setr (sin (d / (2 * r) + 2 * PI)). intro. subst. lra. reflexivity.

  setr (2 * (r * sin (d / (2 * r) + 2 * PI))).
  apply Rmult_le_pos. left. lra.
  setl (r * 0). left.
  apply Rgt_lt.
  apply Rmult_lt_gt_compat_neg_l. assumption. assumption.

  intro.
  assert (/ (r * 2) = 0).
  apply (Rmult_eq_reg_l 1). setl (1 / (r * 2)). intro. subst.
  apply zner. reflexivity. setr 0. assumption. intro.
  lra.
  generalize H0.
  apply Rinv_neq_0_compat.
  intro.
  apply zner.
  assert (0 = 0 * 2). field. rewrite H2 in H1. clear H2.
  symmetry.
  apply (Rmult_eq_reg_r 2). assumption. intro. lra.

  assert (d = d - 0). field. rewrite H at 2.
  apply (H_arclen r θ₀ x₀ y₀ 0 d zner).

  subst. unfold Hxarc, Hyarc.
  fieldrewrite (0 / r + θ₀) θ₀. intro. subst. apply zner. reflexivity.
  fieldrewrite (r * sin θ₀ - r * sin θ₀ + x₀ - x₀) 0.
  fieldrewrite (- r * cos θ₀ + r * cos θ₀ + y₀ - y₀) 0.
  assert (sqrt (0² + 0²) = 0).
  unfold Rsqr.
  fieldrewrite (0 * 0 + 0 * 0) 0.
  apply sqrt_0. rewrite H.
  fieldrewrite (1 / (2 * r) * 0) 0. intro. subst. apply zner. reflexivity.
  unfold asin.
  destruct (pre_asin (TI_map 0)).
  inversion a.
  rewrite TI_Map_equiv_int in H1.
  generalize (sin_0) as sin0. intro.
  rewrite <- sin0 in H1.
  assert (x = 0).

  inversion_clear H0.
  apply Rle_antisym.
  apply (sin_incr_0 x 0). setl (- PI / 2). assumption. assumption.
  generalize PI_RGT_0. intro. left. lra.
  generalize PI_RGT_0. intro. left. lra. right. assumption.

  apply (sin_incr_0 0 x). left.
  apply _PI2_RLT_0.
  generalize PI_RGT_0. intro.
  lra.
  setl (- PI / 2). assumption. assumption.
  right. symmetry. assumption.
  rewrite H2.
  assert (r * 2 * 0 =  zero). unfold zero. simpl. field. rewrite H3.
  apply (is_RInt_point
           (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                      (Derive (Hy r θ₀ y₀ θc rtp)))).
  split; lra.
Qed.

(** Relationship between distance and angle *)
Lemma dbound_angle : forall d r
            (zner : 0 <> r)
            (zledlerPI : 0 <= d <= Rabs r * PI),
            -PI <= d / r <= PI.
Proof.
  intros.
  inversion_clear zledlerPI as [zled dlerPI].
  destruct (Rle_dec 0 r).
  inversion_clear r0.
  split.
  apply (Rmult_le_reg_l r). assumption.
  setl (-r*PI). setr d. intro. subst. lra.
  apply (Rle_trans _ 0).
  setl (- (r * PI)). setr (-0).
  apply Ropp_le_contravar.
  generalize PI_RGT_0. intro.
  apply Rgt_lt in H0.
  left. setl (0*0).
  apply Rmult_le_0_lt_compat; try (right; reflexivity); try assumption.
  assumption.
  apply (Rmult_le_reg_l r). assumption.
  setl d. intro; subst; lra.
  rewrite (Rabs_pos_eq r) in dlerPI.
  assumption. left. assumption.

  exfalso. subst. apply zner. reflexivity.

  apply Rnot_le_lt in n.
  rewrite (Rabs_left r) in dlerPI.
  inversion_clear dlerPI as [dltrPI | deqrPI].

  split.
  assert (/ r < 0) as rinvlt0.
  apply Rinv_lt_0_compat; assumption.
  setl (/r * (- r * PI)). intro; subst; apply zner; reflexivity.
  setr (/r * d). intro; subst; apply zner; reflexivity.
  left.
  apply Rmult_lt_gt_compat_neg_l. assumption. assumption.

  apply (Rle_trans _ 0).
  setl (/ r * d). intro; subst; apply zner; reflexivity.
  setr (/ r * 0). intro; subst; apply zner; reflexivity.
  inversion_clear zled as [zltd | zeqd].
  left.
  apply Rmult_lt_gt_compat_neg_l. 
  assert (/ r < 0) as rinvlt0.
  apply Rinv_lt_0_compat; assumption. assumption.
  assumption.
  subst. right. reflexivity. left.
  apply PI_RGT_0.

  subst.
  split.
  setr (-PI). intro; subst; apply zner; reflexivity.
  right. reflexivity.
  setl (-PI). intro; subst; apply zner; reflexivity.
  left.
  generalize PI_RGT_0; intro.
  apply pos_opp_lt; assumption. assumption.
Qed.

(** Path distance during turn when turn is less than or equal to 180 degrees *)

(** The length of the circular part of the path when the turn is less
than or equal to 180 degrees. Theta in terms of arcsin of final position and
initial positions. *)
Lemma H_len_0_3 : forall r θ₀ θc x₀ y₀ d
    (blertc : 0 <= d <= (r*θc))
    (drange : 0 <= d <= Rabs r*PI)
    rtp,
    is_RInt (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                       (Derive (Hy r θ₀ y₀ θc rtp))) 0 d
            (r * 2 * asin (TI_map (1 / (2*r) * sqrt (((Hx r θ₀ x₀ θc rtp d) - x₀)² +
                                                     ((Hy r θ₀ y₀ θc rtp d) - y₀)²)
            ))).
Proof.
  intros.

  addzner.
  unfold Hx at 2. unfold Hy at 2.
  unfold extension_cont.
  destruct (Rle_dec d (r * θc)).
  2: {
       exfalso.
       apply Rnot_le_lt in n.
       inversion_clear blertc.
       lra.
       }
  inversion_clear blertc as [zled dlertc].
  inversion_clear zled as [zltd | zeqd].

  assert (Derive (Hx r θ₀ x₀ θc rtp) = (Hx' r θ₀ θc rtp)) as deriveHx.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (Hx r θ₀ x₀ θc rtp) q  (Hx' r θ₀ θc rtp q)
                          (Hx_deriv r θ₀ x₀ θc rtp q)).
  assert (Derive (Hy r θ₀ y₀ θc rtp) = (Hy' r θ₀ θc rtp)) as deriveHy.
  apply functional_extensionality. intro q.
  apply (is_derive_unique (Hy r θ₀ y₀ θc rtp) q  (Hy' r θ₀ θc rtp q)
                          (Hy_deriv r θ₀ y₀ θc rtp q)).
  rewrite deriveHx, deriveHy. clear deriveHx deriveHy.
  assert (forall q, Rmin 0 d < q < Rmax 0 d ->
                    (magnitude (Derive (Hxarc r θ₀ x₀))
                               (Derive (Hyarc r θ₀ y₀))) q =
                    (magnitude (Hx' r θ₀ θc rtp) (Hy' r θ₀ θc rtp)) q) as Harcpart.
  intros. unfold magnitude, comp, plus_fct, Hx', Hy', extension_cont.
  unfold Rmin, Rmax in H. destruct (Rle_dec 0 d). clear r0.
  destruct (Rle_dec q (r*θc)).

  rewrite (is_derive_unique _ _ _ (Hyarc_deriv r θ₀ y₀ q zner)).
  rewrite (is_derive_unique _ _ _ (Hxarc_deriv r θ₀ x₀ q zner)).
  reflexivity.

  exfalso.
  apply n. inversion_clear H. clear n. lra.
  exfalso. apply n. left. assumption.

  apply (is_RInt_ext _ _ _ _ _ Harcpart). clear Harcpart.

  apply (RInt_unique _ _ _ d).
  apply (Rmult_eq_reg_l (1/(r*2))).
  setl (d/(2*r)). intro. subst. apply zner. reflexivity.
  setr (asin (TI_map ( 1 / (2*r) * sqrt ((Hxarc r θ₀ x₀ d - x₀)² +
                                 (Hyarc r θ₀ y₀ d - y₀)²)))).
  intro. subst. apply zner. reflexivity.
  assert (sin (d / (2 * r)) = 1 / (2*r) * (sqrt ((Hxarc r θ₀ x₀ d - x₀)² +
                                                 (Hyarc r θ₀ y₀ d - y₀)²) ))
    as applyinverse.

  2 : {
        (* generalize (SIN_bound (d / (2 * r))) as sinbounds. intros. *)
        rewrite <- applyinverse.
        rewrite asin_sin_id_0. reflexivity.
        clear applyinverse (* sinbounds *).
        generalize (dbound_angle d r zner drange) as drrange; intro.
        inversion_clear drrange as [zledr drlerPI].
        split.
        apply (Rmult_le_reg_l 2). lra.
        setl (-PI). setr (d/r). intro; subst; apply zner; reflexivity.
        assumption.
        apply (Rmult_le_reg_l 2). lra.
        setr (PI). setl (d/r). intro; subst; apply zner; reflexivity.
        assumption.
        }
      
  unfold Hxarc,Hyarc.
  unfold Rsqr.
  fieldrewrite
    ((r * sin (d / r + θ₀) - r * sin θ₀ + x₀ - x₀) *
     (r * sin (d / r + θ₀) - r * sin θ₀ + x₀ - x₀) +
     (- r * cos (d / r + θ₀) + r * cos θ₀ + y₀ - y₀) *
     (- r * cos (d / r + θ₀) + r * cos θ₀ + y₀ - y₀))
    ((r * sin (d / r + θ₀) * r * sin (d / r + θ₀) -
      2 * r * sin (d / r + θ₀)* r * sin θ₀ + r * sin θ₀ *r * sin θ₀ ) +
     (r * cos (d / r + θ₀)* r * cos (d / r + θ₀) -
      2 * r * cos θ₀ * r * cos (d / r + θ₀) + r * cos θ₀ * r * cos θ₀)).
  assert
    ((r * sin (d / r + θ₀) * r * sin (d / r + θ₀) -
      2 * r * sin (d / r + θ₀) * r * sin θ₀ +
      r * sin θ₀ * r * sin θ₀ +
      (r * cos (d / r + θ₀) * r * cos (d / r + θ₀) -
       2 * r * cos θ₀ * r * cos (d / r + θ₀) +
       r * cos θ₀ * r * cos θ₀))=
     (r²*(((sin (d / r + θ₀))² + (cos (d / r + θ₀))²) +
          ((sin θ₀)² + (cos θ₀)²)) -
      2*r²* (cos (d / r + θ₀) * cos θ₀ + sin (d / r + θ₀) * sin θ₀)))
    as intoRsqr.
  unfold Rsqr. field.
  rewrite intoRsqr. clear intoRsqr.
  repeat rewrite sin2_cos2.
  rewrite <- cos_minus.
  fieldrewrite (d / r + θ₀ - θ₀) (d / r). intro. subst. apply zner. reflexivity.
  fieldrewrite (r² * (1 + 1) - 2 * r² * cos (d / r))
               (2*r²* (1 - cos (d / r))).
  fieldrewrite (d / r) (2 * (d / (2*r))).
  intro. subst. apply zner. reflexivity.
  rewrite cos_2a_sin.
  assert (2 * r² * (1 - (1 - 2 * sin (d / (2 * r)) * sin (d / (2 * r)))) =
          (2 * r * sin (d / (2 * r)))²) as sinRsqr.
  unfold Rsqr; field.
  rewrite sinRsqr. clear sinRsqr.
  
  generalize (total_order_T 0 r) as order0r. intros.
  inversion_clear order0r as [zger | zltr].
  inversion_clear zger as [zltr | zeqr].
  2 : { exfalso. subst. apply zner. reflexivity. }

  assert (0 < d / (2*r) <= PI) as d2rorder.
  rewrite (Rabs_pos_eq r) in drange.
  inversion_clear drange as [zled dlerPI].

  split.
  apply (Rmult_lt_reg_l (2*r)). lra.
  setl 0. setr d. intro. subst. lra.
  assumption.
  apply (Rmult_le_reg_l (2*r)). lra.
  setl d. intro. subst. lra.
  apply (Rle_trans _ (r * PI)). assumption.
  setr (r *(2*PI)).
  apply Rmult_le_compat_l. left. assumption.
  generalize (PI_RGT_0); intro.
  left. lra. left. assumption.

  inversion_clear d2rorder as [zltd2r d2rlePI].
  inversion_clear d2rlePI as [d2rltPI | d2reqPI].
  2 : {
        rewrite d2reqPI.
        rewrite sin_PI.
        fieldrewrite (2 * r * 0) 0.
        rewrite (sqrt_Rsqr 0). field. intro. subst. lra.
        right. reflexivity.
        }

  generalize (sin_gt_0 (d / (2 * r)) zltd2r d2rltPI) as sinnonneg. intro.
  rewrite sqrt_Rsqr.
  setr (sin (d / (2 * r))). intro. subst. lra. reflexivity.

  apply Rmult_le_pos.
  apply Rmult_le_pos.
  left. lra. left. assumption. left. assumption.


  assert (-PI <= d / (2*r) < 0) as d2rorder.
  rewrite (Rabs_left r) in drange.
  inversion_clear drange as [zled dlemrPI].

  split.
  generalize (Rinv_lt_0_compat r zltr) as divrneg. intro.
  setl (/ r * (-r *PI)). intro; subst; apply zner; reflexivity.
  setr (/ r * (/ 2 * d)). intro; subst; apply zner; reflexivity.
  apply (Rmult_le_compat_neg_l (/r)). left. assumption.
  apply (Rmult_le_reg_l 2). lra. setl d.
  apply (Rle_trans _ (-r * PI)). assumption.
  assert (-r*PI > 0) as mrPIgt0.
  apply Rlt_gt.
  apply Rmult_lt_0_compat.
  apply Ropp_0_gt_lt_contravar. assumption.
  apply (PI_RGT_0).
  assert (1*(- r * PI) = (- r * PI)). field.
  rewrite <- H at 1.
  apply Rmult_le_compat_r. left. assumption.
  left. lra.

  generalize (Rinv_lt_0_compat r zltr) as divrneg. intro.
  setl (/r * (/2 * d)). intro; subst; apply zner; lra.
  setr (/r * 0). intro; subst; apply zner; lra.
  apply (Rmult_lt_gt_compat_neg_l (/r)). assumption.
  apply (Rmult_lt_reg_l 2). lra. setl 0. setr d.
  assumption. assumption.

  inversion_clear d2rorder as [_PIled2r d2rlt0].
  inversion_clear _PIled2r as [_PIltd2r | _PIeqd2r].
  2 : {
        rewrite <- _PIeqd2r.
        rewrite sin_antisym.
        rewrite sin_PI.
        fieldrewrite (2 * r * -0) 0.
        rewrite (sqrt_Rsqr 0). field. intro. subst. lra.
        right. reflexivity.
        }

  assert (d / (2 * r) + 2*PI < 2*PI) as d2r'lt2PI.
  assert (2*PI = 0 + 2*PI). field. rewrite H at 2.
  apply Rplus_lt_compat_r. assumption.
  assert (PI < d / (2 * r) + 2*PI) as PIltd2r'.
  assert (PI = -PI + 2*PI). field. rewrite H at 1.
  apply Rplus_lt_compat_r. assumption.
  rewrite <- (sin_period _ 1).
  assert (2 * INR 1 * PI = 2*PI). unfold INR. field.
  rewrite H. clear H.
  generalize (sin_lt_0 (d / (2 * r) + 2 * PI) PIltd2r' d2r'lt2PI)
    as sinnonpos. intro.
  rewrite sqrt_Rsqr.
  setr (sin (d / (2 * r) + 2 * PI)). intro. subst. lra. reflexivity.

  setr (2 * (r * sin (d / (2 * r) + 2 * PI))).
  apply Rmult_le_pos. left. lra.
  setl (r * 0). left.
  apply Rgt_lt.
  apply Rmult_lt_gt_compat_neg_l. assumption. assumption.

  intro.
  assert (/ (r * 2) = 0).
  apply (Rmult_eq_reg_l 1). setl (1 / (r * 2)). intro. subst.
  apply zner. reflexivity. setr 0. assumption. intro.
  lra.
  generalize H0.
  apply Rinv_neq_0_compat.
  intro.
  apply zner.
  assert (0 = 0 * 2). field. rewrite H2 in H1. clear H2.
  symmetry.
  apply (Rmult_eq_reg_r 2). assumption. intro. lra.

  assert (d = d - 0). field. rewrite H at 2.
  apply (H_arclen r θ₀ x₀ y₀ 0 d zner).

  subst. unfold Hxarc, Hyarc.
  fieldrewrite (0 / r + θ₀) θ₀. intro. subst. apply zner. reflexivity.
  fieldrewrite (r * sin θ₀ - r * sin θ₀ + x₀ - x₀) 0.
  fieldrewrite (- r * cos θ₀ + r * cos θ₀ + y₀ - y₀) 0.
  assert (sqrt (0² + 0²) = 0).
  unfold Rsqr.
  fieldrewrite (0 * 0 + 0 * 0) 0.
  apply sqrt_0. rewrite H.
  fieldrewrite (1 / (2 * r) * 0) 0. intro. subst. apply zner. reflexivity.
  unfold asin.
  destruct (pre_asin (TI_map 0)).
  inversion a.
  rewrite TI_Map_equiv_int in H1.
  generalize (sin_0) as sin0. intro.
  rewrite <- sin0 in H1.
  assert (x = 0).

  inversion_clear H0.
  apply Rle_antisym.
  apply (sin_incr_0 x 0). setl (- PI / 2). assumption. assumption.
  generalize PI_RGT_0. intro. left. lra.
  generalize PI_RGT_0. intro. left. lra. right. assumption.

  apply (sin_incr_0 0 x). left.
  apply _PI2_RLT_0.
  generalize PI_RGT_0. intro.
  lra.
  setl (- PI / 2). assumption. assumption.
  right. symmetry. assumption.
  rewrite H2.
  assert (r * 2 * 0 =  zero). unfold zero. simpl. field. rewrite H3.
  apply (is_RInt_point
           (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                      (Derive (Hy r θ₀ y₀ θc rtp)))).
  split; lra.
Qed.
(* The length of the circular part of the path when the turn is less
than or equal to 180 degrees. Theta in terms of arcsin of final position and
initial positions. *)

(** Path distance during turn when turn is between 180 degrees and 360
degrees. Theta is expressed as the arcsin of the position that we
reach during the turn when we have traveled the distance equal to the
distance traveled between the present position and the point at which
we had turned 180 degrees. The parameters available to us during a
problem do not make this expression easy to compute. *)
Lemma H_len_0_4 : forall r θ₀ θc x₀ y₀ d
    (blertc : 0 <= d <= (r*θc))
    (drange : Rabs r*PI <= d <= 2 * Rabs r*PI)
    rtp,
    is_RInt (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                       (Derive (Hy r θ₀ y₀ θc rtp))) 0 d
            ((Rabs r * PI) +
             (r * 2 * asin (TI_map (1 / (2*r) *
                                    sqrt (((Hx r θ₀ x₀ θc rtp (d - Rabs r * PI)) - x₀)² +
                                          ((Hy r θ₀ y₀ θc rtp (d - Rabs r * PI)) - y₀)²)
            )))).
Proof.
  intros.

  addzner.
  assert (0 < Rabs r * PI) as zltrPI.
  apply Rmult_lt_0_compat.
  destruct (Rle_dec 0 r) as [zler | znler].
  apply Rabs_pos_lt.
  intro; subst; apply zner; reflexivity.
  apply Rnot_le_gt in znler.
  rewrite Rabs_left.
  apply Ropp_0_gt_lt_contravar.
  assumption. assumption.
  apply PI_RGT_0.
  
  apply (is_RInt_Chasles (magnitude (Derive (Hx r θ₀ x₀ θc rtp)) (Derive (Hy r θ₀ y₀ θc rtp))) _
                         (Rabs r * PI)).
  apply H_len_0.
  inversion_clear drange as [zlerPI rPIled].
  split. left. assumption.
  apply (Rle_trans _ d); try assumption.
  inversion blertc; assumption.

  set (dS := (magnitude (Derive (Hx r θ₀ x₀ θc rtp)) (Derive (Hy r θ₀ y₀ θc rtp)))).
  set (V := (r * 2 *
     asin
       (TI_map
          (1 / (2 * r) *
           sqrt ((Hx r θ₀ x₀ θc rtp (d - Rabs r * PI) - x₀)² + (Hy r θ₀ y₀ θc rtp (d - Rabs r * PI) - y₀)²))))).

  assert (is_RInt (fun q => dS (Rabs r * PI + (q + - Rabs r * PI)))
                  (Rabs r * PI) d V) as cov.
  2 : {
        assert ((fun q : R => dS (Rabs r * PI + (q + - Rabs r * PI))) = dS) as dscov.
        apply functional_extensionality.
        intros.
        assert ((Rabs r * PI + (x + - Rabs r * PI)) = x) as xcov.
        field. rewrite xcov. reflexivity.
        rewrite dscov in cov.
        assumption.
        }
      change (is_RInt (fun q : R => dS (Rabs r * PI + (fun u => u + - Rabs r * PI) q))
                      (Rabs r * PI) d V).
        set (g := (fun u : R => u + - Rabs r * PI)).
        change (is_RInt (fun q => (fun w => dS (Rabs r * PI + w)) (g q))
                        (Rabs r * PI) d V).
        set (dS' := (fun w : R => dS (Rabs r * PI + w))).
        unfold g.
        assert ((fun q : R => dS' (q + - Rabs r * PI))
                = (fun q : R => scal 1 (dS' (1 * q + - Rabs r * PI)))) as mult1eq.
        apply functional_extensionality. intros.
        unfold scal. simpl. unfold mult. simpl. 

        fieldrewrite (x + - Rabs r * PI) (1 * x + - Rabs r * PI).
        field. rewrite mult1eq.
        apply (is_RInt_comp_lin dS' 1 (-Rabs r *PI) (Rabs r * PI) d V).
        fieldrewrite (1 * (Rabs r * PI) + - Rabs r * PI) 0.
        fieldrewrite (1 * d + - Rabs r * PI) (d - Rabs r * PI).
        clear mult1eq.

        unfold dS', dS.
        
        assert (Derive (Hx r θ₀ x₀ θc rtp) = (Hx' r θ₀ θc rtp)) as deriveHx.
        apply functional_extensionality. intro q.
        apply (is_derive_unique (Hx r θ₀ x₀ θc rtp) q  (Hx' r θ₀ θc rtp q)
                                (Hx_deriv r θ₀ x₀ θc rtp q)).
        assert (Derive (Hy r θ₀ y₀ θc rtp) = (Hy' r θ₀ θc rtp)) as deriveHy.
        apply functional_extensionality. intro q.
        apply (is_derive_unique (Hy r θ₀ y₀ θc rtp) q  (Hy' r θ₀ θc rtp q)
                                (Hy_deriv r θ₀ y₀ θc rtp q)).
        rewrite deriveHx, deriveHy. clear deriveHx deriveHy.


        assert (forall q, Rmin 0 (d - Rabs r * PI) < q < Rmax 0 (d - Rabs r * PI) ->
                          (magnitude (Derive (Hxarc r θ₀ x₀))
                                     (Derive (Hyarc r θ₀ y₀))) q =
                          (fun w : R => magnitude (Hx' r θ₀ θc rtp) (Hy' r θ₀ θc rtp) (Rabs r * PI + w))
                            (* (magnitude (Hx' r θ₀ θc rtp) (Hy' r θ₀ θc rtp)) *)
                            q) as Harcpart.
        intros. unfold magnitude, comp, plus_fct, Hx', Hy', extension_cont.
        unfold Rmin, Rmax in H. destruct (Rle_dec 0 (d - Rabs r *PI)). clear r0.
        destruct (Rle_dec (Rabs r * PI + q) (r*θc)).
        
        rewrite (is_derive_unique _ _ _ (Hyarc_deriv r θ₀ y₀ q zner)).
        rewrite (is_derive_unique _ _ _ (Hxarc_deriv r θ₀ x₀ q zner)).
        unfold Hxarc' at 2. unfold Hyarc' at 2.
        destruct (Rle_dec 0 r). 

        rewrite (Rabs_pos_eq r).
        fieldrewrite ((r * PI + q) / r + θ₀) ((q / r + θ₀) + PI).
        intro. subst. apply zner. reflexivity.
        
        rewrite (neg_sin (q / r + θ₀)).
        rewrite (neg_cos (q / r + θ₀)).
        rewrite <- Rsqr_neg.
        rewrite <- Rsqr_neg.
        unfold Hxarc', Hyarc'. reflexivity. assumption.

        apply Rnot_le_gt in n. apply Rgt_lt in n.
        rewrite (Rabs_left r).
        fieldrewrite ((- r * PI + q) / r + θ₀) (- (- (q / r + θ₀) + PI)).
        intro. subst. apply zner. reflexivity.

        rewrite sin_neg.
        rewrite neg_sin.
        rewrite sin_neg.

        rewrite cos_neg.
        rewrite neg_cos.
        rewrite cos_neg.
        repeat rewrite <- Rsqr_neg.
        unfold Hxarc', Hyarc'. reflexivity. assumption.

        exfalso.
        apply n.
        inversion_clear H. clear n.
        inversion_clear blertc.
        apply (Rle_trans _ d). left. lra. assumption.
        
        exfalso. apply n. inversion_clear drange.
        lra.

        apply (is_RInt_ext _ _ _ _ V Harcpart). clear Harcpart.
(********)
        assert (forall q, Rmin 0 (d - Rabs r * PI) < q < Rmax 0 (d - Rabs r * PI) ->
                          (magnitude (Hx' r θ₀ θc rtp) (Hy' r θ₀ θc rtp)) q =
                          (magnitude (Derive (Hxarc r θ₀ x₀))
                                     (Derive (Hyarc r θ₀ y₀))) q
                          )
          as Harcpart.
        intros. unfold magnitude, comp, plus_fct, Hx', Hy', extension_cont.
        unfold Rmin, Rmax in H. destruct (Rle_dec 0 (d - Rabs r * PI)). clear r0.
        destruct (Rle_dec q (r*θc)).
        
        rewrite (is_derive_unique _ _ _ (Hyarc_deriv r θ₀ y₀ q zner)).
        rewrite (is_derive_unique _ _ _ (Hxarc_deriv r θ₀ x₀ q zner)).
        reflexivity.


        exfalso.
        apply n.
        inversion_clear H. clear n.
        inversion_clear blertc.
        apply (Rle_trans _ (d - Rabs r * PI)).
        left. assumption.
        apply (Rle_trans _ d).
        apply (Rplus_le_reg_l (-d)).
        setr 0.
        setl (- (Rabs r * PI)). left.
        apply Ropp_lt_gt_0_contravar.
        apply Rlt_gt.
        generalize PI_RGT_0; intro.
        assert (0 < Rabs r).
        apply Rabs_pos_lt.
        intro; subst; apply zner. reflexivity.
        apply Rgt_lt in H3.
        apply Rmult_lt_0_compat; assumption.
        assumption.
        
        exfalso. apply n. inversion_clear drange.
        lra.

        
        apply (is_RInt_ext _ _ _ _ V Harcpart). clear Harcpart.

        assert (Derive (Hx r θ₀ x₀ θc rtp) = (Hx' r θ₀ θc rtp)) as deriveHx.
        apply functional_extensionality. intro q.
        apply (is_derive_unique (Hx r θ₀ x₀ θc rtp) q  (Hx' r θ₀ θc rtp q)
                                (Hx_deriv r θ₀ x₀ θc rtp q)).
        assert (Derive (Hy r θ₀ y₀ θc rtp) = (Hy' r θ₀ θc rtp)) as deriveHy.
        apply functional_extensionality. intro q.
        apply (is_derive_unique (Hy r θ₀ y₀ θc rtp) q  (Hy' r θ₀ θc rtp q)
                                (Hy_deriv r θ₀ y₀ θc rtp q)).
        rewrite <- deriveHx, <- deriveHy. clear deriveHx deriveHy.
        apply H_len_0_3; try assumption.

        split.

        inversion_clear drange.
        lra.
        apply (Rle_trans _ d).
        apply (Rplus_le_reg_l (-d)).
        setr 0.
        setl (- (Rabs r * PI)). left.
        apply Ropp_lt_gt_0_contravar.
        apply Rlt_gt.
        generalize PI_RGT_0; intro.
        assert (0 < Rabs r).
        apply Rabs_pos_lt.
        intro; subst; apply zner. reflexivity.
        apply Rgt_lt in H.
        apply Rmult_lt_0_compat; assumption.
        inversion_clear blertc.
        assumption.

        split.

        inversion_clear drange.
        lra.
        apply (Rplus_le_reg_l (Rabs r * PI)).
        setr (2 * Rabs r * PI).
        setl (d).
        inversion_clear drange. assumption.
Qed.



(** Path distance during turn when turn is between 180 degrees and 360
degrees. Theta is expressed as the arcsin of the present position and
the point at which we had turned 180 degrees. This may be easier to
compute. *)
Lemma H_len_0_5 : forall r θ₀ θc x₀ y₀ d
    (blertc : 0 <= d <= (r*θc))
    (drange : Rabs r*PI <= d <= 2 * Rabs r*PI)
    rtp,
    is_RInt (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                       (Derive (Hy r θ₀ y₀ θc rtp))) 0 d
            ((Rabs r * PI) +
             (r * 2 * asin (TI_map (1 / (2*r) *
                                    sqrt (((Hx r θ₀ x₀ θc rtp d) -
                                           (Hx r θ₀ x₀ θc rtp (Rabs r * PI)))² +
                                          ((Hy r θ₀ y₀ θc rtp d) -
                                           (Hy r θ₀ y₀ θc rtp (Rabs r * PI)))²)
            )))).
Proof.
  intros.

  addzner.
  generalize (H_len_0_4 r θ₀ θc x₀ y₀ d blertc drange rtp).
  intro.
  assert (((Hx r θ₀ x₀ θc rtp d - Hx r θ₀ x₀ θc rtp (Rabs r * PI))² +
          (Hy r θ₀ y₀ θc rtp d - Hy r θ₀ y₀ θc rtp (Rabs r * PI))²) =
          ((Hx r θ₀ x₀ θc rtp (d - Rabs r * PI) - x₀)² +
           (Hy r θ₀ y₀ θc rtp (d - Rabs r * PI) - y₀)²)).
  clear H.
  (*****)
  unfold Hx,Hy,extension_cont.
  destruct (Rle_dec d (r * θc)).
  destruct (Rle_dec (Rabs r * PI) (r * θc)).
  destruct (Rle_dec (d - Rabs r * PI) (r * θc)).
  unfold Hxarc,Hyarc.
  destruct (Rle_dec 0 r).
  assert (r <> 0) as rne0. intro; subst; apply zner; reflexivity.
  rewrite (Rabs_pos_eq r).
  fieldrewrite (r * PI / r) PI; try assumption.
  fieldrewrite ((d - r * PI)/r) (d/r - PI); try assumption.
  fieldrewrite (r * sin (d / r + θ₀) - r * sin θ₀ + x₀ - (r * sin (PI + θ₀) - r * sin θ₀ + x₀))
               (r * sin (d / r + θ₀) - r * sin (PI + θ₀)).
  fieldrewrite (- r * cos (d / r + θ₀) + r * cos θ₀ + y₀ - (- r * cos (PI + θ₀) + r * cos θ₀ + y₀))
               (- r * cos (d / r + θ₀) + r * cos (PI + θ₀)).
  fieldrewrite (r * sin (d / r - PI + θ₀) - r * sin θ₀ + x₀ - x₀)
               (r * sin (d / r - PI + θ₀) - r * sin θ₀).
  fieldrewrite (- r * cos (d / r - PI + θ₀) + r * cos θ₀ + y₀ - y₀)
               (- r * cos (d / r - PI + θ₀) + r * cos θ₀).
  fieldrewrite (d / r - PI + θ₀) (- ((- d/r - θ₀) + PI)).
  assumption.
  rewrite sin_neg.
  rewrite cos_neg.
  fieldrewrite (PI + θ₀) (θ₀ + PI).
  repeat rewrite neg_sin.
  repeat rewrite neg_cos.
  fieldrewrite (r * sin (d / r + θ₀) - r * - sin θ₀) (r * sin (d / r + θ₀) + r * sin θ₀).
  fieldrewrite (- r * cos (d / r + θ₀) + r * - cos θ₀) (- (r * cos (d / r + θ₀) + r *  cos θ₀)).
  fieldrewrite (- d / r - θ₀) (- (d / r + θ₀)). assumption.
  rewrite sin_neg.
  rewrite cos_neg.
  fieldrewrite (r * - - - sin (d / r + θ₀) - r * sin θ₀) (- (r * sin (d / r + θ₀) + r * sin θ₀)).
  fieldrewrite (- r * - cos (d / r + θ₀) + r * cos θ₀) (r * cos (d / r + θ₀) + r * cos θ₀).
  repeat rewrite <- Rsqr_neg. reflexivity. assumption.

  apply Rnot_le_lt in n.
  assert (r <> 0) as rne0. intro; subst; apply zner; reflexivity.
  repeat rewrite Rabs_left.
  fieldrewrite (- r * PI / r) (- PI); try assumption.
  fieldrewrite ((d - - r * PI)/r) (d/r + PI); try assumption.
  fieldrewrite (r * sin (d / r + θ₀) - r * sin θ₀ + x₀ - (r * sin (- PI + θ₀) - r * sin θ₀ + x₀))
               (r * sin (d / r + θ₀) - r * sin (- PI + θ₀)).
  fieldrewrite (- r * cos (d / r + θ₀) + r * cos θ₀ + y₀ - (- r * cos (- PI + θ₀) + r * cos θ₀ + y₀))
               (- r * cos (d / r + θ₀) + r * cos (- PI + θ₀)).
  fieldrewrite (r * sin (d / r + PI + θ₀) - r * sin θ₀ + x₀ - x₀)
               (r * sin (d / r + PI + θ₀) - r * sin θ₀).
  fieldrewrite (- r * cos (d / r + PI + θ₀) + r * cos θ₀ + y₀ - y₀)
               (- r * cos (d / r + PI + θ₀) + r * cos θ₀).
  fieldrewrite (d / r + PI + θ₀) ((d/r + θ₀) + PI). 
  assumption.
  fieldrewrite (- PI + θ₀) (- (- θ₀ + PI)).
  rewrite sin_neg.
  rewrite cos_neg.
  repeat rewrite neg_sin.
  repeat rewrite neg_cos.
  fieldrewrite (r * sin (d / r + θ₀) - r * - - sin (- θ₀)) (r * sin (d / r + θ₀) - r * sin (- θ₀)).
  fieldrewrite (- r * cos (d / r + θ₀) + r * - cos (- θ₀)) (- (r * cos (d / r + θ₀) + r *  cos (- θ₀))).
  rewrite sin_neg.
  rewrite cos_neg.
  fieldrewrite (r * sin (d / r + θ₀) - r * - sin θ₀) (r * sin (d / r + θ₀) + r * sin θ₀).
  fieldrewrite (r * - sin (d / r + θ₀) - r * sin θ₀) (- ( r * sin (d / r + θ₀) + r * sin θ₀)).
  fieldrewrite (- r * - cos (d / r + θ₀) + r * cos θ₀) (r * cos (d / r + θ₀) + r * cos θ₀).
  repeat rewrite <- Rsqr_neg. reflexivity. assumption.

  exfalso.
  apply n.
  inversion_clear drange.
  inversion_clear blertc.
  apply (Rle_trans _ d).

  assert (0 < Rabs r * PI) as zltrPI.
  apply Rmult_lt_0_compat.
  destruct (Rle_dec 0 r) as [zler | znler].
  apply Rabs_pos_lt.
  intro; subst; apply zner; reflexivity.
  apply Rnot_le_gt in znler.
  rewrite Rabs_left.
  apply Ropp_0_gt_lt_contravar.
  assumption. assumption.
  apply PI_RGT_0.
  lra.
  assumption.
  
  exfalso.
  apply n.
  inversion_clear blertc.
  inversion_clear drange.
  lra.

  exfalso.
  apply n.
  inversion_clear blertc.
  assumption.

  (*****)
  rewrite H0. assumption.
Qed.

(** Path distance during the straight segment. Distance is expressed as
a function of the present position and the point at which we stopped
turning and started a straight path. *)
Lemma H_len_d_1 : forall r θ₀ θc x₀ y₀ d
    (blertc : 0 <= (r*θc) < d)
    rtp,
    is_RInt (magnitude (Derive (Hx r θ₀ x₀ θc rtp))
                       (Derive (Hy r θ₀ y₀ θc rtp))) 0 d
            (r*θc +
             sqrt (Rsqr (Hx r θ₀ x₀ θc rtp d - Hx r θ₀ x₀ θc rtp (r*θc)) +
                   Rsqr (Hy r θ₀ y₀ θc rtp d - Hy r θ₀ y₀ θc rtp (r*θc)))).
Proof.
  intros.

  addzner.
  inversion_clear blertc as [zlertc rtcltd].
  assert (0 <= d) as zled. lra.
  apply (RInt_unique _ _ _ d).
  unfold Hx, Hy, extension_cont.
  destruct (Rle_dec d (r * θc)).
  exfalso. lra.
  apply Rnot_le_lt in n.
  destruct (Rle_dec (r * θc) (r * θc)). clear r0.
  unfold Hxarc, Hyarc, Hxlin, Hylin.
  fieldrewrite ((d - r * θc) * cos (θ₀ + θc) +
                (r * sin (r * θc / r + θ₀) - r * sin θ₀ + x₀) -
                (r * sin (r * θc / r + θ₀) - r * sin θ₀ + x₀))
               ((d - r * θc) * cos (θ₀ + θc)).
  fieldrewrite ((d - r * θc) * sin (θ₀ + θc) +
                (- r * cos (r * θc / r + θ₀) + r * cos θ₀ + y₀) -
                (- r * cos (r * θc / r + θ₀) + r * cos θ₀ + y₀))
               ((d - r * θc) * sin (θ₀ + θc)).
  unfold Rsqr.
  fieldrewrite ((d - r * θc) * cos (θ₀ + θc) * ((d - r * θc) * cos (θ₀ + θc)) +
                (d - r * θc) * sin (θ₀ + θc) * ((d - r * θc) * sin (θ₀ + θc)))
               ((d - r * θc) * (d - r * θc) * (sin (θ₀ + θc) * sin (θ₀ + θc)+
                                               cos (θ₀ + θc) * cos (θ₀ + θc))).
  change (d = r * θc + sqrt ((d - r * θc)² * ((sin(θ₀ + θc))²+(cos (θ₀ + θc))²))).
  rewrite sin2_cos2.
  fieldrewrite ((d - r * θc)² * 1) ((d - r * θc)²).
  rewrite sqrt_Rsqr. field. left. lra.
  exfalso.  apply n0. right. reflexivity.
  apply (H_len r θ₀ θc x₀ y₀ d zled zlertc ).
Qed.

