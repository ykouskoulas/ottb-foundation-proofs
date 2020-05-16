(* begin hide *)
Require Import Reals.
Require Import Ranalysis5.
Require Import FunctionalExtensionality.
Require Import Coquelicot.Coquelicot.
Require Import Omega.
Require Import Lra.
Require Import Lia.
Require Import atan2.
Require Import ttyp.
Require Import util.

Import Lra.
Open Scope R_scope.
Set Bullet Behavior "Strict Subproofs".

(* end hide *)
(* begin hide *)

Lemma straightcond : forall r x y,
    straight r 0 0 0 x y -> (2 * r * y < x² + y²).
Proof.
  intros *. intro phase.
  unfold straight, Tcy, Tcx in phase.
  rewrite Rplus_0_r, sin_PI2, cos_PI2, Rmult_0_r,
  Rplus_0_l, Rplus_0_l, Rminus_0_r, Rmult_1_r in phase.
  rewrite Rsqr_minus in phase.
  apply (Rplus_lt_compat_r (-r²)) in phase.
  apply Rminus_gt_0_lt.
  setl (r² + - r²). setr (x² + (y² + r² - 2 * y * r) + - r²).
  assumption.
Qed.


Lemma theta1_req0_thetamax (x y : R) (xne0 : x <> 0) (yne0 : y <> 0):
  2*atan((x - sqrt(x^2 - (2*0 - y)*y))/(2*0-y)) = atan2 y x.
Proof.
  rewrite atan_atan2_id.
  assert (x ^ 2 - (2 * 0 - y) * y =  (x^2 + y^2)) as P0. { field. }
  rewrite P0.
  assert (2*0 - y = -y) as P1. { field. }
  rewrite P1.
  assert (((x - sqrt (x ^ 2 + y ^ 2)) / - y) ^ 2 =
          (x ^ 2 - 2 * x * sqrt(x ^ 2 + y ^ 2) + (sqrt (x ^ 2 + y ^ 2))^2)
            /(y^2)) as P2. { field; auto. }
  rewrite P2.
  rewrite <- (Rsqr_pow2 (sqrt (x ^2 + y^2))).
  rewrite Rsqr_sqrt.
  - assert ((1 - (x ^ 2 - 2 * x * sqrt (x ^ 2 + y ^ 2) + (x ^ 2 + y ^ 2))
                   / y ^ 2) =
            (x / y) * (2 * ((x - sqrt (x ^ 2 + y ^ 2)) / - y))) as P3.
    { field; auto. }
    rewrite P3.
    rewrite atan2_cancel_id; auto.
    intro.
    apply Rmult_integral in H.
    destruct H; [lra |].
    apply (Rmult_eq_compat_r (-y)) in H.
    rewrite Rmult_0_l in H.
    assert ((x - sqrt (x ^ 2 + y ^ 2)) / - y * - y =
            x - sqrt (x ^ 2 + y ^ 2)) as P4. { field; auto. }
    rewrite P4 in H.
    apply Rminus_diag_uniq_sym in H.
    apply sqrt_lem_0 in H.
    rewrite <-(Rplus_0_r) in H at 1.
    assert (x * x = x ^ 2) as P5; [field| rewrite P5 in H]. 
    apply Rplus_eq_reg_l in H.
    specialize (pow2_gt_0 _ yne0) as P6.
    lra.
    specialize (pow2_ge_0 y) as P5.
    specialize (pow2_ge_0 x) as P6.
    lra.
    rewrite <- H.
    apply sqrt_pos.
    assert ((2 * ((x - sqrt (x ^ 2 + y ^ 2)) / - y)) =
            ((2 * ((sqrt (x ^ 2 + y ^ 2) - x)) * (/ y)))) as P4.
    { field; auto. }
    rewrite P4.
    rewrite sign_mult.
    assert (sign (2 * (sqrt (x ^ 2 + y ^ 2) - x)) = 1) as P5.
    rewrite sign_mult.
    rewrite sign_eq_1;[|lra].
    rewrite Rmult_1_l.
    apply sign_eq_1.
    apply Rlt_Rminus.
    destruct (total_order_T x 0).
    destruct s.
    specialize (sqrt_pos (x ^ 2 + y ^ 2)) as P5.
    lra.
    exfalso; auto.
    apply Rsqr_incrst_0.
    rewrite Rsqr_sqrt.
    rewrite Rsqr_pow2.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_lt_compat_l.
    destruct (pow2_ge_0 y); auto.
    exfalso.
    specialize (pow_nonzero _ 2 yne0) as P5.
    apply P5; auto.
    specialize (pow2_ge_0 x) as P5.
    specialize (pow2_ge_0 y) as P6.
    lra.
    lra.
    apply sqrt_pos.
    rewrite P5.
    destruct (total_order_T y 0).
    destruct s.
    rewrite (sign_eq_m1 _ r).
    specialize (Rinv_lt_0_compat _ r) as P6.
    rewrite (sign_eq_m1 _ P6).
    field.
    exfalso.
    apply yne0.
    assumption.
    apply Rgt_lt in r.
    rewrite (sign_eq_1 _ r).
    specialize (Rinv_0_lt_compat _ r) as P6.
    rewrite (sign_eq_1 _ P6).
    field.
  - specialize (pow2_ge_0 x) as P3.
    specialize (pow2_ge_0 y) as P4.
    lra.
Qed.





Lemma straight_not_stationary :
  forall (x₀ y₀ x₁ y₁ θ₀ r : R)
         (phase : straight r θ₀ x₀ y₀ x₁ y₁),
    x₁- x₀ <> 0 \/ y₁ - y₀ <> 0.
Proof.
  intros.
  unfold straight, Tcy, Tcx in phase.
  rewrite <- cos_sin in phase.
  assert (cos (PI / 2 + θ₀) = - - cos (PI / 2 + θ₀)) as ident. field.
  rewrite ident in phase. clear ident.
  rewrite <- sin_cos in phase.
  assert ((x₁ - (x₀ + r * - sin θ₀))² + (y₁ - (y₀ + r * cos θ₀))² =
          ((x₁ - x₀)² + r² * ((sin θ₀)² +(cos θ₀)²) + (y₁ - y₀)² +
           2*(x₁ - x₀)*(r * sin θ₀) - 2 * (y₁ - y₀) * (r * cos θ₀))) as ident.
  unfold Rsqr. field. rewrite ident in phase. clear ident.
  rewrite sin2_cos2 in phase.
  destruct (Req_dec (x₁ - x₀) 0) as [xeq0 | xne0].
  right. intro yeq0. rewrite xeq0, yeq0 in phase. unfold Rsqr in phase.
  assert (0 * 0 + r * r * 1 + 0 * 0 + 2 * 0 * (r * sin θ₀) - 2 * 0 * (r * cos θ₀) = r*r) as id.
  field. rewrite id in phase. lra.
  left. assumption.
Qed.

Lemma straight_not_stationary2 :
  forall (x₀ y₀ x₁ y₁ θ₀ r : R)
         (phase : straight r θ₀ x₀ y₀ x₁ y₁),
    ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0).
Proof.
  intros.
  unfold straight, Tcy, Tcx in phase.
  rewrite <- cos_sin in phase.
  assert (cos (PI / 2 + θ₀) = - - cos (PI / 2 + θ₀)) as ident. field.
  rewrite ident in phase. clear ident.
  rewrite <- sin_cos in phase.
  assert ((x₁ - (x₀ + r * - sin θ₀))² + (y₁ - (y₀ + r * cos θ₀))² =
          ((x₁ - x₀)² + r² * ((sin θ₀)² +(cos θ₀)²) + (y₁ - y₀)² +
           2*(x₁ - x₀)*(r * sin θ₀) - 2 * (y₁ - y₀) * (r * cos θ₀))) as ident.
  unfold Rsqr. field. rewrite ident in phase. clear ident.
  rewrite sin2_cos2 in phase.
  intros [xeq0 yeq0]. rewrite xeq0, yeq0 in phase. unfold Rsqr in phase.
  assert (0 * 0 + r * r * 1 + 0 * 0 + 2 * 0 * (r * sin θ₀) - 2 * 0 * (r * cos θ₀) = r*r) as id.
  field. rewrite id in phase. lra.
Qed.


  

Lemma zlt_mult : forall a b,
    0 < a * b -> (0 <= a -> 0 < b).
Proof.
  intros.
  inversion_clear H0.
  assert (0 = a * 0 ). field. rewrite H0 in H.
  eapply (Rmult_lt_reg_l); eauto.
  exfalso. rewrite <- H1 in H.
  lra.
Qed.


Lemma zgt_mult : forall a b,
    0 > a * b -> (0 <= a -> 0 > b).
Proof.
  intros.
  inversion_clear H0.
  assert (0 = a * 0 ). field. rewrite H0 in H.
  eapply (Rmult_gt_reg_l); eauto.
  exfalso. rewrite <- H1 in H.
  lra.
Qed.

(* end hide *)

(**

   We define variants of a function κ (Greek lower-case kappa) to
   compute the orientation, measured in radians, of a line segment
   from a point on a circular path of radius r, to point (x₁, y₁). The
   circular path is set so its center is at (0,r) and the point on the
   path is indexed by θ, the angle tangent to the path at that point,
   if it were followed counterclockwise from the origin.

   For one-turn-to-bearing motion, we use kappa to trace out the
   non-linear function that represents the angle measuring the
   orientation of the line segment vs. the angle describing the point
   on the turn at which we depart from circular motion.

   We use this to show that the tangent rays from each point on the
   path are either θ or θ + PI, one of which has a discontinuous
   derivative when attached to the original path.

   The quantity κ₂ is based on atan2, which has a branch cut so that it
   produces values (-PI,PI]. The quantity κ is similar to κ₂, except
   that it is defined using atan instead of atan2, introducing an
   ambiguity of PI for the angles it computes. κ' is the derivative of
   both these quantities. κ₃ and κ₄ have similar meanings, but with
   atan defined with different branch cuts; κ₃ has a branch cut on the
   +x axis, so produces values from (0,2*PI], and κ₄ has a branch cut
   on the -y axis, so produces values from (-PI/2 3*PI/2]. The
   derivatives of all variations of the kappa functions (where they
   exist, away from the branch cuts) are uniformly given by κ'. *)

(* This angle determined by the kappa function is geometrically
   related to the quantity η that one can find named in the proofs,
   except that η in our proofs is used only for the line segment that
   is restricted to be tangent to the circle at the point of
   departure, whereas κ is used to explore the angle from different
   points on the circle, where the point of departure may or may not
   be tangent. *)

Definition κ x₁ y₁ r θ := atan ((y₁ - r*(1-cos θ))/(x₁ - r * sin θ)).
Definition κ₂ x₁ y₁ r θ := atan2 (y₁ - r*(1-cos θ)) (x₁ - r * sin θ).
Definition κ₃ x₁ y₁ r θ := atan3 (y₁ - r*(1-cos θ)) (x₁ - r * sin θ).
Definition κ₄ x₁ y₁ r θ := atan4 (y₁ - r*(1-cos θ)) (x₁ - r * sin θ).
Definition κ' x₁ y₁ r θ := (- r * sin θ * (x₁ - r * sin θ) -
                            r * cos θ * (- y₁ + r * (1 - cos θ)))
                                  / ((y₁ - r * (1 - cos θ))² + (x₁ - r * sin θ)²).

Lemma k_periodic : forall x₁ y₁ r k θc,
   κ x₁ y₁ r θc = κ x₁ y₁ r (θc + 2 * IZR k * PI).
Proof.
  intros.
  unfold κ.
  rewrite cos_period1, sin_period1. reflexivity.
Qed.

Lemma k2_periodic : forall x₁ y₁ r k θc,
   κ₂ x₁ y₁ r θc = κ₂ x₁ y₁ r (θc + 2 * IZR k * PI).
Proof.
  intros.
  unfold κ₂.
  rewrite cos_period1, sin_period1. reflexivity.
Qed.

Lemma k3_periodic : forall x₁ y₁ r k θc,
   κ₃ x₁ y₁ r θc = κ₃ x₁ y₁ r (θc + 2 * IZR k * PI).
Proof.
  intros.
  unfold κ₃.
  rewrite cos_period1, sin_period1. reflexivity.
Qed.

Lemma k'_periodic : forall x₁ y₁ r k θc,
   κ' x₁ y₁ r θc = κ' x₁ y₁ r (θc + 2 * IZR k * PI).
Proof.
  intros.
  unfold κ'.
  rewrite cos_period1, sin_period1. reflexivity.
Qed.

Lemma k_is_derive_atan : forall x₁ y₁ r x (dne0 : (x₁ - r * sin x) <> 0),
      is_derive (κ x₁ y₁ r) x (κ' x₁ y₁ r x).
Proof.
  intros.
  unfold κ, κ', Rsqr.
  auto_derive. assumption.
  field.
  split; [| assumption].
  change ((y₁ - r * (1 - cos x))² + (x₁ - r * sin x)² <> 0);
  apply tech_Rplus; [ apply Rle_0_sqr | apply Rlt_0_sqr; assumption].
Qed.

(* begin  hide *)

Lemma k_is_derive_atan_PI : forall x₁ y₁ r,
    let κPI :=  (fun θ => (κ x₁ y₁ r θ) + PI) in
    forall x (dne0 : (x₁ - r * sin x) <> 0),
      is_derive κPI x (κ' x₁ y₁ r x).
Proof.
  intros.
  assert ((κ' x₁ y₁ r x) = (κ' x₁ y₁ r x) + 0) as id. field. rewrite id. clear id.
  change (is_derive κPI x (plus (κ' x₁ y₁ r x) zero)).
  unfold κPI.
  assert ((fun (θ : R) => atan ((y₁ - r * (1 - cos θ)) / (x₁ - r * sin θ)) + PI) =
          (fun (θ : R) => plus (κ x₁ y₁ r θ) ((fun (_:R) => PI) θ))) as plusfn.
  unfold plus. simpl.
  unfold κ. reflexivity.
  unfold κ.
  rewrite plusfn.
  change (is_derive (fun θ => plus (κ x₁ y₁ r θ) ((fun _ => PI) θ)) x (plus (κ' x₁ y₁ r x) ((fun _ => 0) x))).
  apply (is_derive_plus  (κ x₁ y₁ r) (fun _ => PI)).
  apply k_is_derive_atan; try assumption.
  auto_derive. constructor. reflexivity.
Qed.

Lemma k_is_derive_atan_mPI : forall x₁ y₁ r ,
    let κmPI :=  (fun θ => (κ x₁ y₁ r θ) - PI) in
    forall x (dne0 : (x₁ - r * sin x) <> 0),
      is_derive κmPI x (κ' x₁ y₁ r x).
Proof.
  intros.
  assert ((κ' x₁ y₁ r x) = (κ' x₁ y₁ r x) - 0) as id. field. rewrite id. clear id.
  change (is_derive κmPI x (minus (κ' x₁ y₁ r x) zero)).
  unfold κmPI, κ.
  assert ((fun (θ : R) => atan ((y₁ - r * (1 - cos θ)) / (x₁ - r * sin θ)) - PI) =
          (fun (θ : R) => minus (κ x₁ y₁ r θ) ((fun (_:R) => PI) θ))) as plusfn.
  unfold plus. simpl.
  unfold κ. reflexivity.
  rewrite plusfn.
  change (is_derive (fun θ => minus (κ x₁ y₁ r θ) ((fun _ => PI) θ)) x
                    (minus (κ' x₁ y₁ r x) ((fun _ => 0) x))).
  apply (is_derive_minus (κ x₁ y₁ r) (fun _ => PI)).
  apply k_is_derive_atan; try assumption.
  auto_derive. constructor. reflexivity.
Qed.


Lemma k_is_derive_atan2_Q1 :
  forall x₁ y₁ r x,
    0 < (x₁ - r * sin x) -> 0 < (y₁ - r * (1- cos x)) ->
      is_derive (κ₂ x₁ y₁ r) x (κ' x₁ y₁ r x).
Proof.
  intros *. intros r1 r0.
  set (η0 := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)))).
  set (ηPI := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)) + PI)).
  set (ηmPI := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)) - PI)).

  set (den := (fun a => x₁ - r * sin a)) in *.
  set (num := (fun a => y₁ - r * (1-cos a))) in *.
  
  assert (continuity_pt num x) as numcont. unfold num. intros. reg.
  assert (continuity_pt den x) as dencont. unfold den. intros. reg.
  assert (continuous num x) as numconts. intros.
  apply continuity_pt_impl_continuous_pt. apply numcont. clear numcont.
  assert (continuous den x) as denconts. intros.
  apply continuity_pt_impl_continuous_pt. apply dencont. clear dencont.
  rewrite reasonable_continuity in numconts.
  rewrite reasonable_continuity in denconts.
  
  specialize (atan2_atan_Q1 _ _ r1 r0) as atan2def.
  change ((κ₂ x₁ y₁ r) x = η0 x) in atan2def. symmetry in atan2def.
  assert (locally x (fun t => η0 t = (κ₂ x₁ y₁ r) t)) as locmatch.
  unfold locally.
  change (0 < num x) in r0.
  change (0 < den x) in r1.
  set (epsn := (mkposreal _ r0)).
  set (epsd := (mkposreal _ r1)).
  specialize (numconts epsn) as [deln numb].
  specialize (denconts epsd) as [deld denb].
  specialize (Rmin_stable_in_posreal deln deld) as epspf.
  set (eps := (mkposreal _ epspf)).
  exists eps. intros y ballx.
  unfold ball in ballx. simpl in ballx.
  unfold AbsRing_ball, R_AbsRing, minus, plus, opp, abs in ballx.
  simpl in ballx.
  assert (y + - x = y - x) as id. field. rewrite id in ballx. clear id.
  specialize (Rmin_def _ _ _ ballx) as [rmdn rmdd].
  specialize (numb _ rmdn).
  specialize (denb _ rmdd).
  simpl in numb, denb.
  rewrite Rabs_lt_between in numb, denb.
  inversion_clear numb as [nlb nub]. clear nub.
  inversion_clear denb as [dlb dub]. clear dub.
  assert (0 < num y) as zltny. lra. clear nlb.
  assert (0 < den y) as zltdy. lra. clear dlb.
  unfold η0,κ₂. symmetry.
  apply atan2_atan_Q1; assumption. 
  apply (is_derive_n_ext_loc η0 (κ₂ x₁ y₁ r) 1 x (κ' x₁ y₁ r x) locmatch).
  apply k_is_derive_atan. intro. lra.
Qed.


Lemma k_is_derive_atan2_Q2 :
  forall x₁ y₁ r x,
    (x₁ - r * sin x) < 0 -> 0 < (y₁ - r * (1- cos x)) ->
      is_derive (κ₂ x₁ y₁ r) x (κ' x₁ y₁ r x).
Proof.
  intros *. intros n0 r0.
  set (η0 := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)))).
  set (ηPI := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)) + PI)).
  set (ηmPI := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)) - PI)).

  set (den := (fun a => x₁ - r * sin a)) in *.
  set (num := (fun a => y₁ - r * (1-cos a))) in *.
  
  assert (continuity_pt num x) as numcont. unfold num. intros. reg.
  assert (continuity_pt den x) as dencont. unfold den. intros. reg.
  assert (continuous num x) as numconts. {
    intros.
    apply continuity_pt_impl_continuous_pt. apply numcont. }
  clear numcont.
  assert (continuous den x) as denconts. {
    intros.
    apply continuity_pt_impl_continuous_pt. apply dencont. }
  clear dencont.
  rewrite reasonable_continuity in numconts.
  rewrite reasonable_continuity in denconts.

  specialize (atan2_atan_Q2 _ _ n0 r0) as atan2def.
  change ((κ₂ x₁ y₁ r) x = ηPI x) in atan2def. symmetry in atan2def.
  assert (locally x (fun t => ηPI t = (κ₂ x₁ y₁ r) t)) as locmatch. {
    (* atan quadrant 2 *)
    unfold locally.
    change (0 < num x) in r0.
    change (den x < 0) in n0.
    set (epsn := (mkposreal _ r0)).
    assert (0 < - (den x)) as r1. lra.
    set (epsd := (mkposreal _ r1)).
    specialize (numconts epsn) as [deln numb].
    specialize (denconts epsd) as [deld denb].
    specialize (Rmin_stable_in_posreal deln deld) as epspf.
    set (eps := (mkposreal _ epspf)).
    exists eps. intros y ballx.
    unfold ball in ballx. simpl in ballx.
    unfold AbsRing_ball, R_AbsRing, minus, plus, opp, abs in ballx.
    simpl in ballx.
    assert (y + - x = y - x) as id. field. rewrite id in ballx. clear id.
    specialize (Rmin_def _ _ _ ballx) as [rmdn rmdd].
    specialize (numb _ rmdn).
    specialize (denb _ rmdd).
    simpl in numb, denb.
    rewrite Rabs_lt_between in numb, denb.
    inversion_clear numb as [nlb nub]. clear nub.
    inversion_clear denb as [dlb dub]. clear dlb.
    assert (0 < num y) as zltny. lra. clear nlb.
    assert (den y < 0) as zltdy. lra. clear dub.
    unfold ηPI,κ₂. symmetry.
    apply atan2_atan_Q2; assumption. }
  
  apply (is_derive_n_ext_loc ηPI (κ₂ x₁ y₁ r) 1 x ((κ' x₁ y₁ r) x) locmatch).
  apply k_is_derive_atan_PI. intro. lra.
Qed.


Lemma k_is_derive_atan2_Q3 :
  forall x₁ y₁ r x,
    (x₁ - r * sin x) < 0 -> (y₁ - r * (1- cos x)) < 0 ->
      is_derive (κ₂ x₁ y₁ r) x (κ' x₁ y₁ r x).
Proof.
  intros *. intros n2 n1.
  set (η0 := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)))).
  set (ηPI := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)) + PI)).
  set (ηmPI := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)) - PI)).

  set (den := (fun a => x₁ - r * sin a)) in *.
  set (num := (fun a => y₁ - r * (1-cos a))) in *.
  
  assert (continuity_pt num x) as numcont. unfold num. intros. reg.
  assert (continuity_pt den x) as dencont. unfold den. intros. reg.
  assert (continuous num x) as numconts. {
    intros.
    apply continuity_pt_impl_continuous_pt. apply numcont. }
  clear numcont.
  assert (continuous den x) as denconts. {
    intros.
    apply continuity_pt_impl_continuous_pt. apply dencont. }
  clear dencont.
  rewrite reasonable_continuity in numconts.
  rewrite reasonable_continuity in denconts.

  specialize (atan2_atan_Q3 _ _ n2 n1) as atan2def.
  change ((κ₂ x₁ y₁ r) x = ηmPI x) in atan2def. symmetry in atan2def.
  assert (locally x (fun t => ηmPI t = (κ₂ x₁ y₁ r) t)) as locmatch. {
    (* atan quadrant 3 *)
    unfold locally.
    change (num x < 0) in n1.
    change (den x < 0) in n2.
    assert (0 < - (num x)) as r0. lra.
    set (epsn := (mkposreal _ r0)).
    assert (0 < - (den x)) as r1. lra.
    set (epsd := (mkposreal _ r1)).
    specialize (numconts epsn) as [deln numb].
    specialize (denconts epsd) as [deld denb].
    specialize (Rmin_stable_in_posreal deln deld) as epspf.
    set (eps := (mkposreal _ epspf)).
    exists eps. intros y ballx.
    unfold ball in ballx. simpl in ballx.
    unfold AbsRing_ball, R_AbsRing, minus, plus, opp, abs in ballx.
    simpl in ballx.
    assert (y + - x = y - x) as id. field. rewrite id in ballx. clear id.
    specialize (Rmin_def _ _ _ ballx) as [rmdn rmdd].
    specialize (numb _ rmdn).
    specialize (denb _ rmdd).
    simpl in numb, denb.
    rewrite Rabs_lt_between in numb, denb.
    inversion_clear numb as [nlb nub]. clear nlb.
    inversion_clear denb as [dlb dub]. clear dlb.
    assert (num y < 0) as zltny. lra. clear nub.
    assert (den y < 0) as zltdy. lra. clear dub.
    unfold ηmPI,κ₂. symmetry.
    apply atan2_atan_Q3; assumption. }
    
  apply (is_derive_n_ext_loc ηmPI (κ₂ x₁ y₁ r) 1 x ((κ' x₁ y₁ r) x) locmatch).
  apply k_is_derive_atan_mPI. intro. lra.
Qed.


Lemma k_is_derive_atan2_Q4 :
  forall x₁ y₁ r x,
    0 < (x₁ - r * sin x) -> (y₁ - r * (1- cos x)) < 0 ->
      is_derive (κ₂ x₁ y₁ r) x (κ' x₁ y₁ r x).
Proof.
  intros *. intros r0 n0.
  set (η0 := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)))).
  set (ηPI := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)) + PI)).
  set (ηmPI := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)) - PI)).

  set (den := (fun a => x₁ - r * sin a)) in *.
  set (num := (fun a => y₁ - r * (1-cos a))) in *.
  
  assert (continuity_pt num x) as numcont. unfold num. intros. reg.
  assert (continuity_pt den x) as dencont. unfold den. intros. reg.
  assert (continuous num x) as numconts. {
    intros.
    apply continuity_pt_impl_continuous_pt. apply numcont. }
  clear numcont.
  assert (continuous den x) as denconts. {
    intros.
    apply continuity_pt_impl_continuous_pt. apply dencont. }
  clear dencont.
  rewrite reasonable_continuity in numconts.
  rewrite reasonable_continuity in denconts.

  specialize (atan2_atan_Q4 _ _ r0 n0) as atan2def.
  change ((κ₂ x₁ y₁ r) x = η0 x) in atan2def. symmetry in atan2def.
  assert (locally x (fun t => η0 t = (κ₂ x₁ y₁ r) t)) as locmatch. {
    (* atan quadrant 4 *)
    unfold locally.
    change (num x < 0) in n0.
    change (0 < den x) in r0.
    set (epsd := (mkposreal _ r0)).
    assert (0 < - (num x)) as r1. lra.
    set (epsn := (mkposreal _ r1)).
    specialize (numconts epsn) as [deln numb].
    specialize (denconts epsd) as [deld denb].
    specialize (Rmin_stable_in_posreal deln deld) as epspf.
    set (eps := (mkposreal _ epspf)).
    exists eps. intros y ballx.
    unfold ball in ballx. simpl in ballx.
    unfold AbsRing_ball, R_AbsRing, minus, plus, opp, abs in ballx.
    simpl in ballx.
    assert (y + - x = y - x) as id. field. rewrite id in ballx. clear id.
    specialize (Rmin_def _ _ _ ballx) as [rmdn rmdd].
    specialize (numb _ rmdn).
    specialize (denb _ rmdd).
    simpl in numb, denb.
    rewrite Rabs_lt_between in numb, denb.
    inversion_clear numb as [nlb nub]. clear nlb.
    inversion_clear denb as [dlb dub]. clear dub.
    assert (num y < 0) as zltny. lra. clear nub.
    assert (0 < den y) as zltdy. lra. clear dlb.
    unfold η0,κ₂. symmetry.
    apply atan2_atan_Q4; assumption. }

  apply (is_derive_n_ext_loc η0 (κ₂ x₁ y₁ r) 1 x ((κ' x₁ y₁ r) x) locmatch).
  apply k_is_derive_atan. intro. lra.
Qed.

(* end hide *)

Lemma k_is_derive_atan2 :
  forall x₁ y₁ r x (rne0 : r <> 0)
         (dne0 :  ~((x₁ - r * sin x) <= 0 /\ (y₁ - r * (1- cos x)) = 0)),
      is_derive (κ₂ x₁ y₁ r) x (κ' x₁ y₁ r x).
Proof.
  intros.
  specialize PI_RGT_0 as PI_RGT_0.

  set (η0 := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)))).
  set (ηPI := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)) + PI)).
  set (ηmPI := (fun θ : R => atan ((y₁ - r * (1 - cos θ))/(x₁ - r * sin θ)) - PI)).

  set (den := (fun a => x₁ - r * sin a)) in *.
  set (num := (fun a => y₁ - r * (1-cos a))) in *.
  change (~ (den x <= 0 /\ num x = 0)) in dne0.
  
  assert (continuity_pt num x) as numcont. unfold num. intros. reg.
  assert (continuity_pt den x) as dencont. unfold den. intros. reg.
  assert (continuous num x) as numconts. {
    intros.
    apply continuity_pt_impl_continuous_pt. apply numcont. }
  clear numcont.
  assert (continuous den x) as denconts. {
    intros.
    apply continuity_pt_impl_continuous_pt. apply dencont. }
  clear dencont.
  rewrite reasonable_continuity in numconts.
  rewrite reasonable_continuity in denconts.
  
  destruct (Rlt_dec 0 (y₁ - r * (1 - cos x))); [
    destruct (Rlt_dec 0 (x₁ - r * sin x)); 
    [ | apply Rnot_lt_le in n ] |
    destruct (Rlt_dec 0 (x₁ - r * sin x)); 
    apply Rnot_lt_le in n; [| apply Rnot_lt_le in n0]].

  + apply k_is_derive_atan2_Q1; assumption.

  + inversion_clear n as [n0 | n0].

    ++ apply k_is_derive_atan2_Q2; assumption.

       (* atan +y-axis *)
    ++  change (0 < num x) in r0.
  change (den x = 0) in n0.
  specialize (atan2_atan_Q1Q2 _ (den x) r0) as atan2def.
  change ((κ₂ x₁ y₁ r) x = (fun z => PI / 2 - atan (den z / num z)) x) in atan2def.
  assert (locally x (fun t => (fun z => PI / 2 - atan (den z / num z)) t = (κ₂ x₁ y₁ r) t)) as locmatch. {

  unfold locally.
  set (epsn := (mkposreal _ r0)).
  assert (0 < 1) as r1. lra.
  set (epsd := (mkposreal _ r1)).
  specialize (numconts epsn) as [deln numb].
  specialize (denconts epsd) as [deld denb].
  specialize (Rmin_stable_in_posreal deln deld) as epspf.
  set (eps := (mkposreal _ epspf)).
  exists eps. intros y ballx.
  unfold ball in ballx. simpl in ballx. unfold AbsRing_ball, R_AbsRing, minus, plus, opp, abs in ballx.
  simpl in ballx.
  assert (y + - x = y - x) as id. field. rewrite id in ballx. clear id.
  specialize (Rmin_def _ _ _ ballx) as [rmdn rmdd].
  specialize (numb _ rmdn).
  specialize (denb _ rmdd).
  simpl in numb, denb.
  rewrite Rabs_lt_between in numb, denb.
  inversion_clear numb as [nlb nub]. clear nub.
  inversion_clear denb as [dlb dub]. clear dlb.
  assert (den y < 1) as zltny. lra. clear dub.
  assert (0 < num y) as zltdy. lra. clear nlb.
  unfold κ₂. symmetry.
  change (atan2 (num y) (den y) = PI / 2 - atan (den y / num y)).
  apply atan2_atan_Q1Q2; assumption. }
  
  simpl in locmatch.
  apply (is_derive_n_ext_loc (fun z => PI / 2 - atan (den z / num z))
                             (κ₂ x₁ y₁ r) 1 x ((κ' x₁ y₁ r) x) locmatch). simpl.
  auto_derive.
  split. unfold den. auto_derive. auto.
  split. unfold num. auto_derive. auto.
  split. intro. lra. auto.

  change (- ((1 * Derive den x * / num x +
    den x * (- (1 * Derive num x) * / (num x * num x))) *
   / (1 + den x * / num x * (den x * / num x * 1))) = κ' x₁ y₁ r x).
  
  assert (is_derive den x (- r * cos x)) as dden. unfold den.
  auto_derive. auto. field.

  assert (is_derive num x (- r * sin x)) as dnum. unfold num.
  auto_derive. auto. field.

  rewrite (is_derive_unique _ _ _ dden).
  rewrite (is_derive_unique _ _ _ dnum).

  unfold κ', Rsqr, num, den. simpl. field.
  change ((num x)² + (den x)² <> 0 /\ num x <> 0).
  split.
  rewrite Rplus_comm.
  apply tech_Rplus. right. symmetry.
  rewrite n0. apply Rsqr_0.
  apply Rsqr_pos_lt. intro. lra. intro.  lra. 
         
  
  + inversion_clear n as [n0 | n0].

  apply k_is_derive_atan2_Q4; assumption.

  (* atan +x-axis *)
  specialize (atan2_atan_Q1Q4 _ (y₁ - r * (1 - cos x)) r0) as atan2def.
  change ((κ₂ x₁ y₁ r) x = η0 x) in atan2def. symmetry in atan2def.
  assert (locally x (fun t => η0 t = (κ₂ x₁ y₁ r) t)) as locmatch. {

    unfold locally.
    change (num x = 0) in n0.
    change (0 < den x) in r0.
    set (epsd := (mkposreal _ r0)).
    assert (0 < 1) as r1. lra.
    set (epsn := (mkposreal _ r1)).
    specialize (numconts epsn) as [deln numb].
    specialize (denconts epsd) as [deld denb].
    specialize (Rmin_stable_in_posreal deln deld) as epspf.
    set (eps := (mkposreal _ epspf)).
    exists eps. intros y ballx.
    unfold ball in ballx. simpl in ballx.
    unfold AbsRing_ball, R_AbsRing, minus, plus, opp, abs in ballx.
    simpl in ballx.
    assert (y + - x = y - x) as id. field. rewrite id in ballx. clear id.
    specialize (Rmin_def _ _ _ ballx) as [rmdn rmdd].
    specialize (numb _ rmdn).
    specialize (denb _ rmdd).
    simpl in numb, denb.
    rewrite Rabs_lt_between in numb, denb.
    inversion_clear numb as [nlb nub]. clear nlb.
    inversion_clear denb as [dlb dub]. clear dub.
    assert (num y < 1) as zltny. lra. clear nub.
    assert (0 < den y) as zltdy. lra. clear dlb.
    unfold η0,κ₂. symmetry.
    apply atan2_atan_Q1Q4; assumption. }
  apply (is_derive_n_ext_loc η0 (κ₂ x₁ y₁ r) 1 x ((κ' x₁ y₁ r) x) locmatch).
  apply k_is_derive_atan. intro. lra.
  
  + inversion_clear n as [n1|n1].
    inversion_clear n0 as [n2|n2].

    ++ apply k_is_derive_atan2_Q3; assumption.

  (* atan -y-axis *)
    ++ change (num x < 0) in n1.
       change (den x = 0) in n2.
       specialize (atan2_atan_Q3Q4 _ (den x) n1) as atan2def.
       change ((κ₂ x₁ y₁ r) x = (fun z => - PI / 2 - atan (den z / num z)) x) in atan2def.
       assert (locally x (fun t => (fun z => - PI / 2 - atan (den z / num z)) t = (κ₂ x₁ y₁ r) t)) as locmatch. {
         
         unfold locally.
         assert (0 < - num x) as r0. lra.
         set (epsn := (mkposreal _ r0)).
         assert (0 < 1) as r1. lra.
         set (epsd := (mkposreal _ r1)).
         specialize (numconts epsn) as [deln numb].
         specialize (denconts epsd) as [deld denb].
         specialize (Rmin_stable_in_posreal deln deld) as epspf.
         set (eps := (mkposreal _ epspf)).
         exists eps. intros y ballx.
         unfold ball in ballx. simpl in ballx.
         unfold AbsRing_ball, R_AbsRing, minus, plus, opp, abs in ballx.
         simpl in ballx.
         assert (y + - x = y - x) as id. field. rewrite id in ballx. clear id.
         specialize (Rmin_def _ _ _ ballx) as [rmdn rmdd].
         specialize (numb _ rmdn).
         specialize (denb _ rmdd).
         simpl in numb, denb.
         rewrite Rabs_lt_between in numb, denb.
         inversion_clear numb as [nlb nub]. clear nlb.
         inversion_clear denb as [dlb dub]. clear dlb.
         assert (den y < 1) as zltny. lra. clear dub.
         assert (num y < 0) as zltdy. lra. clear nub.
         unfold κ₂. symmetry.
         change (atan2 (num y) (den y) = - PI / 2 - atan (den y / num y)).
         apply atan2_atan_Q3Q4; assumption. }
  
       simpl in locmatch.
       apply (is_derive_n_ext_loc (fun z => - PI / 2 - atan (den z / num z))
                                  (κ₂ x₁ y₁ r) 1 x ((κ' x₁ y₁ r) x) locmatch). simpl.
       auto_derive.
       split. unfold den. auto_derive. auto.
       split. unfold num. auto_derive. auto.
       split. intro. lra. auto.
       
       change (- ((1 * Derive den x * / num x +
                   den x * (- (1 * Derive num x) * / (num x * num x))) *
                  / (1 + den x * / num x * (den x * / num x * 1))) = κ' x₁ y₁ r x).
       
       assert (is_derive den x (- r * cos x)) as dden. unfold den.
       auto_derive. auto. field.
       
       assert (is_derive num x (- r * sin x)) as dnum. unfold num.
       auto_derive. auto. field.
       
       rewrite (is_derive_unique _ _ _ dden).
       rewrite (is_derive_unique _ _ _ dnum).

       unfold κ', Rsqr, num, den. simpl. field.
       change ((num x)² + (den x)² <> 0 /\ num x <> 0).
       split.
       rewrite Rplus_comm.
       apply tech_Rplus. right. symmetry.
       rewrite n2. apply Rsqr_0.
       apply Rsqr_pos_lt. intro. lra. intro.  lra. 
       
    ++ exfalso. auto.
Qed.


Lemma k_is_derive_atan3 :
  forall x₁ y₁ r x (rne0 : r <> 0)
         (dne0 :  ~(0 <= (x₁ - r * sin x) /\ (y₁ - r * (1- cos x)) = 0)),
      is_derive (κ₃ x₁ y₁ r) x (κ' x₁ y₁ r x).
Proof.
  intros.
  unfold κ₃, atan3.
  assert ((κ' x₁ y₁ r x) = (plus (κ' x₁ y₁ r x) zero)) as id.
  unfold plus, zero. simpl. field. rewrite id. clear id.
  change (is_derive
            (fun θ : R => 
               (plus
                  ((fun p:R => atan2 (- (y₁ - r * (1 - cos p)))
                                     (- (x₁ - r * sin p))) θ)
                  ((fun q:R => PI) θ)))
            x
            (plus (κ' x₁ y₁ r x) 0)).
  apply (is_derive_plus (fun p:R => atan2 (- (y₁ - r * (1 - cos p)))
                                          (- (x₁ - r * sin p)))
                        (fun q:R => PI)).

  assert ((fun p : R => atan2 (- (y₁ - r * (1 - cos p)))
                              (- (x₁ - r * sin p))) =
          (fun p : R => atan2 ((- y₁) - (-r) * (1 - cos p))
                              ((- x₁) - (-r) * sin p))) as fex.

  apply functional_extensionality. intro p.
  fieldrewrite (- (y₁ - r * (1 - cos p)))
               ((- y₁) - (-r) * (1 - cos p)).
  fieldrewrite (- (x₁ - r * sin p))
               ((- x₁) - (-r) * sin p).
  reflexivity. rewrite fex. clear fex.

  assert (~ (((- x₁) - (-r) * sin x) <= 0 /\ (-y₁) - (-r) * (1 - cos x) = 0)) as dne1.
  intro. apply dne0. inversion_clear H.
  split.
  setl (-0). setr (- - (x₁ - r * sin x)).
  apply Ropp_le_contravar. setl (- x₁ - - r * sin x). assumption.
  apply (Rmult_eq_reg_l (-1)). setl (- y₁ - - r * (1 - cos x)). setr 0. assumption.
  intro. lra.
  assert ((-r) <> 0). intro. apply rne0.
  apply (Rmult_eq_reg_l (-1)). setl (-r). setr 0. assumption.
  intro. lra.
  assert ((κ' x₁ y₁ r x) = (κ' (-x₁) (-y₁) (-r) x)) as kpid.
  unfold κ', Rsqr. field.
  change ((- y₁ - - r * (1 - cos x))² + (- x₁ - - r * sin x)² <> 0).
  intro.
  specialize (Rle_0_sqr (- y₁ - - r * (1 - cos x))) as lhsnn.
  specialize (Rle_0_sqr (- x₁ - - r * sin x)) as rhsnn.

  inversion_clear lhsnn as [zlty | zeqy].
  inversion_clear rhsnn as [zltx | zeqx].
  specialize (Rplus_lt_0_compat _ _ zlty zltx) as ctd.
  rewrite H0 in ctd. lra.

  rewrite <- zeqx in H0.
  rewrite Rplus_0_r in H0.
  rewrite H0 in zlty. lra.

  inversion_clear rhsnn as [zltx | zeqx].
  rewrite <- zeqy in H0.
  rewrite Rplus_comm in H0.
  rewrite Rplus_0_r in H0.
  rewrite H0 in zltx. lra.
  clear H0. apply dne1.
  symmetry in zeqy.
  apply Rsqr_eq_0 in zeqy.
  symmetry in zeqx.
  apply Rsqr_eq_0 in zeqx.

  split; [right; assumption | assumption].
  rewrite kpid. clear kpid.
  change (is_derive (κ₂ (- x₁) (- y₁) (- r)) x (κ' (- x₁) (- y₁) (- r) x)).
  apply (k_is_derive_atan2 _ _ _ _ H dne1).
  apply (is_derive_const PI).
Qed.


Lemma k_is_derive_atan4 :
  forall x₁ y₁ r x (rne0 : r <> 0)
         (dne0 :  ~((x₁ - r * sin x) = 0 /\ (y₁ - r * (1- cos x)) <= 0)),
      is_derive (κ₄ x₁ y₁ r) x (κ' x₁ y₁ r x).
Proof.
  intros.
  unfold κ₄, atan4.
  assert ((κ' x₁ y₁ r x) = (plus (κ' x₁ y₁ r x) zero)) as id.
  unfold plus, zero. simpl. field. rewrite id. clear id.
  change (is_derive
            (fun θ : R => 
               (plus
                  ((fun p:R => atan2 (- (x₁ - r * sin p))
                                     (y₁ - r * (1 - cos p))) θ)
                  ((fun q:R => PI/2) θ)))
            x
            (plus (κ' x₁ y₁ r x) 0)).
  apply (is_derive_plus (fun p:R => atan2 (- (x₁ - r * sin p))
                                          (y₁ - r * (1 - cos p)))
                        (fun q:R => PI/2)).

  assert (forall p, (- (x₁ - r * sin p) =
                     ((r - x₁) -r*(1 - cos (PI / 2 + p + PI))))) as xxfm.
  intro.
  rewrite neg_cos.
  rewrite <- sin_cos.
  fieldrewrite (r - x₁ - r * (1 - sin p)) (- (x₁ - r * sin p)).
  reflexivity.

  assert (forall p, (y₁ - r * (1 - cos p)) =
                    ((y₁ - r) - r * sin (PI/2 + p+PI))) as yxfm.
  intro.
  rewrite neg_sin.
  rewrite <- cos_sin.
  fieldrewrite (y₁ - r - r * - cos p) (y₁ - r * (1 - cos p)).
  reflexivity.

  set (Y := r - x₁) in *.
  set (X := y₁ - r) in *.


  assert (~ (X - r * sin (PI/2+x+PI) <= 0 /\
             Y - r * (1 - cos (PI/2 + x + PI)) = 0)) as dne1.
  intro. apply dne0. inversion_clear H as [xfor yfor]. {
    split. unfold Y in yfor.
    rewrite neg_cos in yfor.
    rewrite <- sin_cos in yfor.
    apply (Rmult_eq_reg_l (-1)). setr 0.
    rewrite <- yfor. field. discrR.
    unfold X in xfor.
    rewrite neg_sin in xfor.
    rewrite <- cos_sin in xfor.
    setl (y₁ - r - r * - cos x). assumption. }
    
    assert ((fun p : R => atan2 (- (x₁ - r * sin p))
                                (y₁ - r * (1 - cos p))) =
            (fun p : R => atan2 (Y -r*(1 - cos (PI / 2 + p + PI)))
                                (X - r * sin (PI/2 + p+PI)))) as fex. {
    apply functional_extensionality. intro p.
    rewrite xxfm, yxfm. reflexivity. }
  rewrite fex. clear fex.
  
  unfold κ'.
  fieldrewrite (x₁ - r * sin x) (- -(x₁ - r * sin x)).
  rewrite xxfm.
  fieldrewrite (- y₁ + r * (1 - cos x)) (- (y₁ - r * (1 - cos x))).
  rewrite yxfm.
  
  rewrite (Rplus_comm ((X - r * sin (PI / 2 + x + PI))²)
                      ((- (Y - r * (1 - cos (PI / 2 + x + PI))))²)).
  
  rewrite (sin_cos x).
  rewrite <- neg_cos.
  rewrite (cos_sin x).
  fieldrewrite (r * sin (PI / 2 + x) * - (X - r * sin (PI / 2 + x + PI)))
               (r * - sin (PI / 2 + x) * (X - r * sin (PI / 2 + x + PI))).
  rewrite <- neg_sin.
  fieldrewrite
    (- r * cos (PI / 2 + x + PI) * - (Y - r * (1 - cos (PI / 2 + x + PI))) -
     r * sin (PI / 2 + x + PI) * (X - r * sin (PI / 2 + x + PI)))
    (- r * sin (PI / 2 + x + PI) * (X - r * sin (PI / 2 + x + PI))
     - r * cos (PI / 2 + x + PI) *  (- Y + r * (1 - cos (PI / 2 + x + PI)))).
  assert ((- (Y - r * (1 - cos (PI / 2 + x + PI))))² =
          (Y - r * (1 - cos (PI / 2 + x + PI)))²) as id. unfold Rsqr. field.
  rewrite id. clear id.
  assert ((fun p : R =>
             atan2 (Y - r * (1 - cos (PI / 2 + p + PI)))
                   (X - r * sin (PI / 2 + p + PI))) =
          comp (κ₂ X Y r)
               (fun p => PI / 2 + p + PI)) as fid.
  apply functional_extensionality. intro.
  unfold comp. reflexivity.
  rewrite fid. clear fid.

  
  assert 
    ((- r * sin (PI / 2 + x + PI) * (X - r * sin (PI / 2 + x + PI)) -
      r * cos (PI / 2 + x + PI) * (- Y + r * (1 - cos (PI / 2 + x + PI))))
       / ((Y - r * (1 - cos (PI / 2 + x + PI)))² + (X - r * sin (PI / 2 + x + PI))²)=
     (scal one (comp (κ' X Y r) (fun p : R => PI / 2 + p + PI) x))) as did.
  unfold comp, κ', scal, one, mult. simpl. unfold mult. simpl. field.
  intro.
  apply sumsqeq0 in H as [larg0 rarg0].
  apply dne1.
  split. right. assumption. assumption.

  rewrite did. clear did.

  assert (is_derive (fun p : R => PI / 2 + p + PI) x one).
  auto_derive. constructor. auto.
  apply (is_derive_comp (κ₂ X Y r) (fun p : R => PI / 2 + p + PI) x
        (comp (κ' X Y r) (fun p : R => PI / 2 + p + PI) x) one).
  unfold comp.
  apply (k_is_derive_atan2); assumption.
  assumption.
  auto_derive. constructor. reflexivity.
Qed.


Lemma k_extrema_vals :
  forall y₁ x₁ r z
         (zrng : -PI < z <= PI ) (rne0 : r <> 0)
         (dne0 :  ~((x₁ - r * sin z) = 0 /\ (y₁ - r * (1- cos z)) = 0)),
      κ' x₁ y₁ r z = 0 <-> exists k, (κ₂ x₁ y₁ r) z = z + IZR k * PI.
Proof.
  intros. 
  assert ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)² <> 0) as zltssqr.
  intro. apply dne0.
  apply Rplus_sqr_eq_0. rewrite Rplus_comm. assumption.
  unfold κ₂, atan2.
  destruct (pre_atan2 (y₁ - r * (1 - cos z)) (x₁ - r * sin z)) as [x [xrng [sxd syd]]].

  assert (sqrt ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²) <> 0) as sqrtsqrne0.
  intro. apply sqrt_eq_0 in H. apply zltssqr. assumption.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.

  split.
  intro etadeq0.
  unfold κ' in etadeq0.
  apply zero_num2 in etadeq0; [| assumption].

  assert (sin z * cos x - cos z * sin x = 0) as nd.
  apply (Rmult_eq_reg_l (-1)); [|discrR]. setr 0. setl (- sin z * cos x + cos z * sin x).
  apply (Rmult_eq_reg_r (sqrt ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²)));
    [|assumption].
  setl (- sin z * (sqrt ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²) * cos x) +
        cos z * (sqrt ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²) * sin x)).
  setr 0. rewrite <- sxd. rewrite <- syd.
  apply (Rmult_eq_reg_r r); [|assumption].
  setl (- r * sin z * (x₁ - r * sin z) - r * cos z * (- y₁ + r * (1 - cos z))).
  setr 0. assumption.

  
  rewrite <- sin_minus in nd.
  inversion_clear zrng as [zlb zub].
  inversion_clear xrng as [xlb xub].
  assert (-2 * PI < z - x) as m2PIltzmx. lra.
  assert (z - x <= 2*PI) as xle2PI. lra.
  destruct (Rle_dec 0 (z - x)).
  specialize (sin_eq_O_2PI_0 _ r0 xle2PI nd) as zmxvals.
  inversion_clear zmxvals as [zmxz | [zmxPI | zmx2PI]].
  exists (0%Z). unfold IZR. setr z.
  apply (Rplus_eq_reg_r (-x)). setl 0. setr (z - x). symmetry. assumption.
  exists ((-1)%Z). unfold IZR.
  rewrite <- zmxPI.
  assert (IPR 1 = 1). unfold IPR. field. rewrite H. clear H. field.
  exists ((-2)%Z). unfold IZR.
  assert (IPR 2 = 2). unfold IPR, IPR_2. field. rewrite H. clear H. setr (z - (2*PI)).
  rewrite <- zmx2PI. field.

  apply Rnot_le_lt in n.
  rewrite <- (sin_period _ 1) in nd. unfold INR in nd.
  assert (0 <= z - x + 2 * 1 * PI) as zlearg. lra.
  assert (z - x + 2 * 1 * PI<= 2*PI) as argle2PI. lra.
  specialize (sin_eq_O_2PI_0 _ zlearg argle2PI nd) as zmxvals.
  inversion_clear zmxvals as [zmxz | [zmxPI | zmx2PI]].
  exists ((2)%Z). apply (Rplus_eq_reg_r (-x)).
  setl 0. setr (z - x + 2 * 1 * PI). symmetry. assumption.
  exists ((1)%Z). apply (Rplus_eq_reg_r (-x + PI)).
  setl (PI). setr (z - x + 2 * 1 * PI). symmetry. assumption.
  exists (0%Z). apply (Rplus_eq_reg_r (2* PI - x)).
  setl (2*PI). setr (z - x + 2 * 1 * PI). symmetry. assumption.

  intros eqty.
  inversion_clear eqty as [k etaxeqx].
  unfold κ'.
  apply (Rmult_eq_reg_r ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²));
    [|assumption].
  setr 0. setl (- r * sin z * (x₁ - r * sin z) + r * cos z * (y₁ - r * (1 - cos z))).
  assumption.
  rewrite syd. rewrite sxd at 2.

  setl ((r * sqrt ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²))*
        (- sin z * cos x + cos z * sin x)).
  apply (Rmult_eq_reg_r (/ (r * sqrt ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²))));
  [|apply Rinv_neq_0_compat;
    apply Rmult_integral_contrapositive_currified;
    assumption].
  setl (sin x * cos z - cos x * sin z); 
    [split; assumption|].
  setr 0; [split; assumption|].
  rewrite <- sin_minus.
  rewrite etaxeqx.
  fieldrewrite (z + IZR k * PI - z) (IZR k * PI).
  apply sin_eq_0_1. exists k. reflexivity.
Qed.


Lemma k_center_val : forall x₁ y₁ r,
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall z (zrng : 0 < r* z < Rabs r * (2 * PI))
           (rne0 : r <> 0)
           (sinzne0 : sin z <> 0)
           (sgncompat : 0 < r * θmax)
           (phase :  straight r 0 0 0 x₁ y₁)
      (etamid : (κ₂ x₁ y₁ r) z = θmax/2),
      (κ₂ x₁ y₁ r) z = z/2.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field. rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field. rewrite id in phase. clear id.

  assert (~((x₁ - r * sin z) = 0 /\ (y₁ - r * (1- cos z)) = 0)) as dne0. {
    intro noc. inversion_clear noc as [nox noy].
    assert (x₁ = r * sin z) as x1cd.
    apply (Rplus_eq_reg_r (- r * sin z)). setr 0. setl (x₁ - r * sin z). assumption.
    assert (y₁ = r * (1-cos z)) as y1cd.
    apply (Rplus_eq_reg_r (- r * (1-cos z))). setr 0. setl (y₁ - r * (1-cos z)). assumption.
    rewrite x1cd, y1cd in phase. 
    assert (1 < 1) as c.
    apply (Rmult_lt_reg_l (r²)).
    apply Rsqr_pos_lt ; assumption.
    rewrite <- (sin2_cos2 z) at 2.
    setr ((r * sin z)² + (r * (1 - cos z) - r)²). setl r². assumption.
    lra.
  }
  
  unfold κ₂ in *.
  unfold θmax, calcθ₁ in *. clear θmax.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id in etamid, sgncompat. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id in etamid, sgncompat. clear id.
  assert (2 * atan2 y₁ x₁ / 2 = atan2 y₁ x₁) as id. field.
  rewrite id in etamid. clear id.

  unfold atan2 in *.
  destruct (pre_atan2 (y₁ - r * (1 - cos z)) (x₁ - r * sin z)) as [η [tcrng [tlb tub]]].
  destruct (pre_atan2 y₁ x₁) as [θmax2 [tm2rng [y1d x1d]]].
  subst. 

  set (H := sqrt ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²)) in *.
  set (I := sqrt (y₁² + x₁²)) in *.

  rewrite y1d in tlb.
  assert ((I-H) * sin θmax2 = r * (1 - cos z)) as sinid.
  apply (Rplus_eq_reg_r (- r * (1-cos z) + H * sin θmax2)).
  setl (I * sin θmax2 - r * (1 - cos z)). setr (H * sin θmax2). assumption.

  rewrite x1d in tub.
  assert ((I-H) * cos θmax2 = r * sin z) as cosid.
  apply (Rplus_eq_reg_r (- r * sin z + H * cos θmax2)).
  setl (I * cos θmax2 - r * sin z). setr (H * cos θmax2). assumption.

  rewrite <- x1d in tub.
  rewrite <- y1d in tlb.

  (* cos experiment*)
  assert (sin θmax2 * sin z = cos θmax2 * (1 - cos z)) as id.
  apply (Rmult_eq_reg_l ((I-H)*r)).
  setl ((I - H) * sin θmax2 * (r * sin z)).
  setr ((I - H) * cos θmax2 * r * (1 - cos z)).
  rewrite sinid, cosid. field.

  apply Rmult_integral_contrapositive_currified. intro.
  rewrite H0 in sinid,cosid.
  assert (sin z = 0). apply (Rmult_eq_reg_l r). setr (0 * cos θmax2). symmetry. assumption.
  assumption. apply sinzne0. assumption. assumption.
  assert (cos (θmax2 - z) = cos θmax2) as id2.
  rewrite cos_minus.
  apply (Rplus_eq_reg_r (- cos θmax2 * cos z)).
  setl (sin θmax2 * sin z). setr (cos θmax2 * (1 - cos z)). assumption.
  rewrite <- cos_neg in id2.
  assert ((- (θmax2 - z)) = z - θmax2). field. rewrite H0 in id2. clear H0.

  apply (Rmult_eq_reg_r 2); [|discrR]. apply (Rplus_eq_reg_r (- θmax2)).
  setr (z- θmax2). setl (θmax2). symmetry.

  apply (Rplus_eq_compat_r (- cos θmax2)) in id2.
  assert (cos (z - θmax2) - cos θmax2 = 0) as id3.
  setr (cos θmax2 + - cos θmax2).
  setl (cos (z - θmax2) + - cos θmax2). assumption. clear id2.
  rewrite form2 in id3.
  assert ((z - θmax2 + θmax2) / 2 = z/2) as id4. field. rewrite id4 in id3. clear id4.
  assert (((z - θmax2 - θmax2) / 2) = z/2 - θmax2) as id4. field. rewrite id4 in id3. clear id4.

  apply (Rplus_eq_reg_r (-θmax2));
    apply (Rmult_eq_reg_r (/2)); [| apply Rinv_neq_0_compat; discrR];
      setr 0; setl (z / 2 - θmax2).

  inversion zrng as [zlb lub].
  assert (sin (z/2) <> 0) as sinz2ne0. intro. apply sinzne0.

  assert (-PI < z/2 <= PI) as z2rng2. {
    split;
      [apply (Rmult_lt_reg_l 2); [ lra| setr z; setl (-2*PI)]|
       apply (Rmult_le_reg_l 2); [ lra| setl z]].

    destruct (Rlt_dec 0 r).
    apply (Rlt_trans _ 0). lra.
    apply (Rmult_lt_reg_r r); try assumption. setl 0.
    rewrite Rmult_comm. assumption.

    apply Rnot_lt_le in n.
    destruct n.
    apply (Rmult_lt_reg_r (-r)); try assumption. lra.
    apply Ropp_lt_cancel. setl (r*z). setr (- r *(2*PI)).
    rewrite Rabs_left in lub. assumption. assumption.

    exfalso. clear - zlb H1.
    rewrite H1 in zlb.
    rewrite Rmult_0_l in zlb.
    lra.

    destruct (Rlt_dec 0 r).
    left.
    apply (Rmult_lt_reg_l r). assumption.
    rewrite Rabs_right in lub; [ assumption|lra].
    apply Rnot_lt_le in n.
    destruct n. left.
    apply (Rmult_lt_reg_l (-r)). lra.
    apply (Rlt_trans _ 0). setl (- (r*z)). lra.
    rewrite Rabs_left in lub.
    lra. assumption.

    exfalso. clear - zlb H1.
    rewrite H1 in zlb.
    rewrite Rmult_0_l in zlb.
    lra.
  }

  specialize (sinθeq0 _ z2rng2 H0) as zval.
  inversion_clear zval as [z2eq0 | z2eqPI].
  assert (z = 0) as zeq0. apply (Rmult_eq_reg_r (/2)). setl (z/2). setr 0. assumption.
  apply Rinv_neq_0_compat. discrR. rewrite zeq0. apply sin_0.

  assert (z = 2*PI) as zeq2PI. {
    apply (Rmult_eq_reg_r (/2)). setl (z/2). setr PI. assumption.
    apply Rinv_neq_0_compat. discrR.
  }
  rewrite zeq2PI. apply sin_2PI.

  apply Rmult_integral in id3.
  inversion_clear id3 as [yes | no]; [| exfalso; apply sinz2ne0; assumption].
  apply Rmult_integral in yes as [nay | yay].
  lra.

  destruct (Rlt_dec 0 θmax2) as [zlttm2 | zgetm2].
  + assert (0 < z) as zltz. {
      apply (Rmult_lt_reg_l (r)).
      apply (Rmult_lt_reg_r (2*θmax2)).
      apply Rmult_lt_0_compat. lra. assumption.
      setl 0. assumption.
      setl 0. assumption.
    }
    
    
    assert (z < 2*PI) as z2ltPI. {
      destruct (Rlt_dec 0 r).
      apply (Rmult_lt_reg_l r); try assumption.
      rewrite <- (Rabs_right r) at 2; try assumption.
      left. assumption.
      
      exfalso. apply Rnot_lt_le in n.
      apply (Rmult_le_compat_r z) in n; try (left; assumption).
      rewrite Rmult_0_l in n.
      clear - n zlb. lra.
    }
    
    
    assert (θmax2 < PI) as tm2ltPI. {
      destruct tm2rng as [tm2lb [tm2ub | tm2eq]].
      assumption.
      exfalso.
      rewrite tm2eq in *.
      assert (- PI < z/2-PI <= PI) as arng ; [ split; lra|].
      specialize (sinθeq0 _ arng yay) as zval.
      destruct zval; lra.
    }
    
    assert (- PI < z/2-θmax2 <= PI) as arng ; [ split; lra|].
    specialize (sinθeq0 _ arng yay) as zval.
    destruct zval; [assumption| lra].
  + apply Rnot_lt_le in zgetm2.
    destruct zgetm2 as [tm2lt0 |tm2eq0].
    assert (z < 0) as zltz. {
      apply (Rmult_lt_reg_l (- r)).
      apply (Rmult_lt_reg_r (2*- θmax2)).
      apply Rmult_lt_0_compat; lra.
      setl 0. setr (r * (2 * θmax2)). assumption.
      setr 0. setl (- (r*z)). lra.
    }
    
    
    assert (- 2*PI < z) as z2ltPI. {
      destruct (Rlt_dec 0 (- r)).
      apply (Rmult_lt_reg_l (-r)); try assumption.
      rewrite <- (Rabs_left r) at 1; try assumption.
      apply Ropp_lt_cancel.
      setl (r*z). setr (Rabs r * (2 * PI)). assumption.  lra.
      
      exfalso. apply Rnot_lt_le in n.
      apply (Rmult_le_compat_r (-z)) in n; try (left; lra).
      rewrite Rmult_0_l in n.
      clear - n zlb.
      rewrite Rmult_opp_opp in n.
      lra.
    }
    
    destruct tm2rng as [tm2lb tm2ub].
    
    assert (- PI < z/2-θmax2 <= PI) as arng ; [ split; lra|].
    specialize (sinθeq0 _ arng yay) as zval.
    destruct zval; [assumption| lra].

    exfalso. clear - sinz2ne0 yay tm2eq0.
    subst.
    rewrite Rminus_0_r in yay.
    apply sinz2ne0. assumption.
Qed.


Lemma k_tan_val : forall x₁ y₁ r,
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall z (zrng : -PI < z <= PI)
           (rne0 : r <> 0)
           (sinzne0 : sin z <> 0)
           (sgncompat : 0 < r * θmax)
           (sgncompat : 0 < r * z)
           (phase :  straight r 0 0 0 x₁ y₁)
      (etatan : (κ₂ x₁ y₁ r) z = z),
      (2 * r - y₁ <> 0 ->
       tan (z/2) = (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) \/
       tan (z/2) = (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) /\
      (2 * r - y₁ = 0 -> tan (z/2) = y₁/(2*x₁)).
Proof.
  intros.
  unfold κ₂,atan2 in *.
  destruct (pre_atan2 (y₁ - r * (1 - cos z))
                      (x₁ - r * sin z)) as [q [qrng [ydef xdef]]].
  subst.
  set (H:=sqrt ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²)) in *.


  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field. rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field. rewrite id in phase. clear id.
  assert (~((x₁ - r * sin z) = 0 /\ (y₁ - r * (1- cos z)) = 0)) as dne0.
  intro noc. inversion_clear noc as [nox noy].
  assert (x₁ = r * sin z) as x1cd.
  apply (Rplus_eq_reg_r (- r * sin z)). setr 0. setl (x₁ - r * sin z).
  assumption.
  assert (y₁ = r * (1-cos z)) as y1cd.
  apply (Rplus_eq_reg_r (- r * (1-cos z))). setr 0. setl (y₁ - r * (1-cos z)).
  assumption.
  rewrite x1cd, y1cd in phase. 
  assert (1 < 1) as c.
  apply (Rmult_lt_reg_l (r²)).
  apply Rsqr_pos_lt ; assumption.
  rewrite <- (sin2_cos2 z) at 2.
  setr ((r * sin z)² + (r * (1 - cos z) - r)²). setl r². assumption.
  lra.

  specialize (Rplus_le_le_0_compat _ _ (Rle_0_sqr (y₁ - r * (1 - cos z)))
                                   (Rle_0_sqr (x₁ - r * sin z))) as argge0.
  inversion_clear argge0 as [arglt0 |argeq0].
  2:{exfalso.
  specialize (Rle_0_sqr (y₁ - r * (1 - cos z))) as yge0.
  specialize (Rle_0_sqr (x₁ - r * sin z)) as xge0.
  inversion_clear yge0 as [zlty | zeqy]. lra.
  inversion_clear xge0 as [zlty | zeqy2]. lra.
  apply dne0. split. 
  apply Rsqr_eq_0. auto.
  apply Rsqr_eq_0. auto. }

  apply sqrt_lt_R0 in arglt0.
     change (0 < H) in arglt0.

  assert (H <> 0) as Hne0. intro Heq0.  lra.

  assert ((x₁ - r * sin z)* sin z = (y₁ - r * (1 - cos z))*cos z) as id1.
  apply (Rmult_eq_reg_l H); [| assumption].
  setr ((y₁ - r * (1 - cos z)) * (H * cos z)).
  setl ((x₁ - r * sin z) * (H*sin z)).
  rewrite <- xdef, ydef. field.

  assert (x₁ * sin z = y₁* cos z + r * (1 - cos z)) as id2.
  rewrite <- (sin2_cos2 z). unfold Rsqr.
  apply (Rplus_eq_reg_r (- r * sin z * sin z)).
  setl ((x₁ - r * sin z) * sin z).
  setr ((y₁ - r * (1 - cos z)) * cos z).
  assumption.

  apply (Rmult_eq_compat_r (/ sin z)) in id2.
  assert (x₁ = (y₁ * cos z / sin z + r * tan (z/2))) as id3.
  setl (x₁ * sin z * / sin z). assumption.
  rewrite tant2_2; [|assumption]. 
  setr ((y₁ * cos z + r * (1 - cos z)) * / sin z).
  assumption. assumption.

  set (α := z/2) in *.
  assert (z = 2 * α) as zalpharel. unfold α. field. rewrite zalpharel in id3.
  rewrite sin_2a, cos_2a in id3.
  assert (- PI < α <= PI) as arng;[ inversion_clear zrng; split; lra |].
  assert (sin α <> 0) as sinane0.
  intro sinane0.
  specialize (sinθeq0 _ arng sinane0) as [aeq0 |aeqPI].
  rewrite aeq0 in *.
  assert (2*0=0) as R0eq0. field. rewrite R0eq0 in zalpharel.
  clear R0eq0.
  rewrite zalpharel in *.
  apply sinzne0. rewrite sin_0. reflexivity.

  rewrite aeqPI in *.
  inversion_clear zrng. lra.

  assert (cos α <> 0) as cosane0. unfold tan in id3.
  intro cosaeq0. rewrite cosaeq0 in id3. 
  assert (2 * sin α * 0 = 0) as zero. field. rewrite zero in id3.
  assert ((0 * 0 - sin α * sin α) = - sin α * sin α) as sin2. field.
  rewrite sin2 in id3. clear sin2 zero.

  specialize (cosθeq0 _ arng cosaeq0) as [aPI2 | amPI2].
  rewrite aPI2 in *.
  assert (z = PI) as zdef. rewrite zalpharel. field.
  rewrite zdef in sinzne0.
  rewrite sin_PI in sinzne0. apply sinzne0. reflexivity.

  rewrite amPI2 in *.
  assert (z = - PI) as zdef. rewrite zalpharel. field.
  rewrite zdef in sinzne0.
  rewrite sin_neg, sin_PI in sinzne0. apply sinzne0.
  apply Ropp_0.
  change (x₁ = y₁ * ((cos α)² - (sin α)²) / (2 * sin α * cos α) + r * tan α) in id3.
  
  assert (((cos α)² - (sin α)²) = (1 - (tan α)²) * (cos α)²) as id4.
  unfold Rsqr.
  unfold tan. field. assumption. rewrite id4 in id3. clear id4.
  assert (2 * sin α * cos α = 2 * tan α * (cos α)²) as id5.
  unfold Rsqr. unfold tan. field. assumption. rewrite id5 in id3. clear id5.

  assert (y₁ * ((1 - (tan α)²) * (cos α)²) / (2 * tan α * (cos α)²) =
          y₁ * (1 - (tan α)²) / (2 * tan α)) as id6.
  unfold Rsqr. unfold tan. field. split; assumption.

  rewrite id6 in id3. clear id6.
  apply (Rmult_eq_compat_l (2 * tan α)) in id3.

  assert (2 * tan α * (y₁ * (1 - (tan α)²) / (2 * tan α) + r * tan α) =
          y₁ * (1 - (tan α)²) + 2 * r * (tan α)²) as id7.
  unfold Rsqr. field. unfold tan.
  
  assert ((sin α / cos α) = (sin α * / cos α)) as id8. field; assumption.
  rewrite id8. clear id8. intro sinacosaeq0.
  specialize (Rmult_integral _ _ sinacosaeq0) as [zaeq0 | zaeq0]. auto.
  generalize zaeq0.
  apply Rinv_neq_0_compat. assumption.
  rewrite id7 in id3. clear id7.

  set (Q := tan α) in *.
  assert ((2 * r - y₁) * Q² + ((- 2) * x₁) * Q + y₁ = 0) as id9.
  apply (Rplus_eq_reg_r (2 * Q * x₁)). setr (2 * Q * x₁). symmetry.
  setr ((2 * r - y₁) * Q² + y₁).
  rewrite id3. field. clear id3.

  assert (0 <= (-2 * x₁)² - 4 * (2 * r - y₁) * y₁) as discrge0.
  assert ((-2 * x₁)² - 4 * (2 * r - y₁) * y₁ =
          4 * (x₁² - 2 * r * y₁ + y₁²)) as id10. unfold Rsqr. field.
  rewrite id10. clear id10.
  apply Rmult_le_pos. left. lra. left.
  apply (Rplus_lt_reg_l r²). setl (r²).
  assert (r² + (x₁² - 2 * r * y₁ + y₁²) =
          x₁² + (y₁-r)²) as id11. unfold Rsqr. field.
  rewrite id11. clear id11. assumption.

  destruct (Req_dec (2*r - y₁) 0) as [aeq0 | nz].
  rewrite aeq0 in id9.
  destruct (Req_dec x₁ 0) as [x1eq0 | x1ne0].
  rewrite x1eq0 in id9.
  assert (y₁ = 0) as y1eq0.
  apply (Rplus_eq_reg_l (0 * Q² + -2 * 0 * Q)). setr 0. assumption.
  rewrite y1eq0 in aeq0.
  assert (r=0) as req0.
  apply (Rmult_eq_reg_l 2).
  apply (Rplus_eq_reg_r (-0)).
  setr 0. setl (2*r - 0). assumption. discrR.
  exfalso. apply rne0. assumption.

  assert (Q = y₁/(2*x₁)) as soln.
  apply (Rmult_eq_reg_l (2*x₁));
    [|  apply Rmult_integral_contrapositive_currified;
        [discrR| assumption]].
  setr y₁. assumption.
  apply (Rplus_eq_reg_l (-2*x₁*Q)).
  apply (Rplus_eq_reg_l 0). 
  rewrite <- (Rplus_assoc 0 (-2 * x₁ * Q) y₁).
  fieldrewrite 0 (0*Q²). setl 0. symmetry. assumption.
  split; intro. exfalso. apply H0. assumption. assumption.
  
  specialize (quad (2*r - y₁) (-2*x₁) y₁ Q nz discrge0 id9) as Qval.
  assert (- (-2 * x₁) = 2*x₁) as id11.
  field. rewrite id11 in Qval. clear id11.
  assert ((-2 * x₁)² = 4 * x₁²) as id12.
  unfold Rsqr. field. rewrite id12 in Qval. clear id12.
  rewrite Rmult_assoc in Qval.
  rewrite <- (Rmult_minus_distr_l) in Qval.
  rewrite sqrt_mult_alt in Qval; [|left; lra].

  assert (sqrt 4 = 2). unfold sqrt. destruct (Rcase_abs 4).
  lra. destruct (Rge_le 4 0 r0).
  unfold Rsqrt. simpl. destruct (Rsqrt_exists 4 (or_introl r1)).
  inversion_clear a.
  assert (4 = 2²). unfold Rsqr. field. rewrite H2 in H1.
  apply Rsqr_inj. assumption. left. lra. symmetry. assumption.
  clear - e. exfalso. generalize e. change (0 <> 4). discrR.
  rewrite H0 in Qval.

  rewrite <- Rmult_minus_distr_l in Qval.
  rewrite <- Rmult_plus_distr_l in Qval.
  clear H0.

  assert (2 * (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * (2 * r - y₁)) =
          (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)).
  field. assumption. rewrite H0 in Qval. clear H0.
  assert (2 * (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * (2 * r - y₁)) =
          (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)).
  field. assumption. rewrite H0 in Qval. clear H0.
  split; intro. assumption. exfalso. apply nz. assumption.
Qed.

(* begin hide *)

Lemma k_deriv_0 : forall x₁ y₁ r,
    forall (rne0 : r <> 0)
           (phase :  straight r 0 0 0 x₁ y₁),
      (κ' x₁ y₁ r) 0 = r * y₁ / (y₁² + x₁²).
Proof.
  intros.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field. rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field. rewrite id in phase. clear id.
  assert (r² < (x₁² + y₁²) + r² - 2 * y₁ *r) as m.
  setr (x₁² + (y₁ - r)²). assumption.
  
  unfold κ'.
  rewrite sin_0, cos_0.
  unfold Rsqr.
  setl (( r * y₁ ) /(y₁² + x₁²)). {
  change (y₁² + x₁² <> 0).
  rewrite Rplus_comm.
  intro noO.
  rewrite noO in m.
  rewrite Rplus_0_l in m.
  specialize (Rle_0_sqr y₁) as zley1.
  specialize (Rle_0_sqr x₁) as zlex1.
  destruct zley1 as [zlty12 | zeqy12].
  specialize (Rplus_le_lt_0_compat _ _ zlex1 zlty12) as ssgt0.
  clear - ssgt0 noO. lra.
  rewrite <- Rsqr_0 in zeqy12.
  apply Rsqr_eq_abs_0 in zeqy12.
  rewrite Rabs_R0 in zeqy12.
  unfold Rabs in zeqy12.
  destruct (Rcase_abs y₁).
  apply Ropp_eq_compat in zeqy12.
  rewrite Ropp_0,Ropp_involutive in zeqy12.
  rewrite <- zeqy12 in m.
  rewrite Rmult_assoc, Rmult_comm, Rmult_0_l, Rmult_0_l, Rminus_0_r in m.
  clear - m. lra.
  rewrite <- zeqy12 in m.
  rewrite Rmult_assoc, Rmult_comm, Rmult_0_l, Rmult_0_l, Rminus_0_r in m.
  clear - m. lra. }

  reflexivity.
Qed.

Lemma k_deriv_sign_0 : forall x₁ y₁ r,
    forall (rne0 : r <> 0)
           (phase :  straight r 0 0 0 x₁ y₁),
      sign (κ' x₁ y₁ r 0) =
      sign (r * y₁).
Proof.
  intros.
  rewrite k_deriv_0; try assumption.
  rewrite sign_eq_pos_den. reflexivity.

  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field. rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field. rewrite id in phase. clear id.

  specialize (Rle_0_sqr x₁) as [x1gt0 | x1eq0].
  specialize (Rplus_le_lt_compat _ _ _ _ (Rle_0_sqr (y₁)) x1gt0) as cont.
  lra.
  rewrite <- x1eq0 in *. clear x1eq0.
  rewrite Rplus_comm in phase.
  rewrite Rplus_0_r in *.

  specialize (Rle_0_sqr y₁) as [zlty12|zeqy12];[assumption|].

  exfalso.
  rename phase into m.
  rewrite <- Rsqr_0 in zeqy12.
  apply Rsqr_eq_abs_0 in zeqy12.
  rewrite Rabs_R0 in zeqy12.
  unfold Rabs in zeqy12.
  destruct (Rcase_abs y₁).
  apply Ropp_eq_compat in zeqy12.
  rewrite Ropp_0,Ropp_involutive in zeqy12.
  rewrite <- zeqy12 in m. lra.
  rewrite <- zeqy12 in m.
  rewrite Rminus_0_l, <- Rsqr_neg in m. lra.
Qed.


Lemma k_deriv_PI : forall x₁ y₁ r,
    forall (rne0 : r <> 0)
           (phase :  straight r 0 0 0 x₁ y₁),
      (κ' x₁ y₁ r) PI = (r * (- y₁ + r * 2)) /((y₁ - 2 * r)² + (x₁)²).
Proof.
  intros.
  
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field. rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field. rewrite id in phase. clear id.

  unfold κ'.
  rewrite sin_PI, cos_PI.
  unfold Rsqr.
  setl ((r * (- y₁ + r * 2))
          /((y₁ - 2 * r)*(y₁ - 2 * r) + (x₁)*(x₁))); [|reflexivity].
  change ((y₁ - 2 * r)² + x₁² <> 0).
  
  intro.
  specialize (Rle_0_sqr x₁) as [x1gt0 | x1eq0].
  specialize (Rplus_le_lt_compat _ _ _ _ (Rle_0_sqr (y₁-2*r)) x1gt0) as cont.
  lra.
  rewrite <- x1eq0 in *. clear x1eq0.
  rewrite Rplus_comm in phase.
  rewrite Rplus_0_r in H, phase.
  apply Rsqr_eq_0 in H.
  assert ((y₁ - r)² = (y₁² + r² - 2 * r * y₁)) as id.
  unfold Rsqr. field. rewrite id in phase. clear id.
  assert (0 <  (y₁ - 2 * r) * y₁) as phase2.
  setr (y₁² - 2 * r * y₁).
  apply (Rplus_lt_reg_r (r²)).
  rewrite Rplus_comm.
  rewrite Rplus_0_r.
  rewrite (Rplus_comm (y₁² - 2 * r * y₁)).
  setr (y₁² + r² - 2 * r * y₁). assumption.
  rewrite H,Rmult_0_l in phase2. lra.
Qed.

Lemma k_deriv_sign_PI : forall x₁ y₁ r,
    forall (rne0 : r <> 0)
           (phase :  straight r 0 0 0 x₁ y₁),
      sign (κ' x₁ y₁ r PI) =
      sign ((r * (- y₁ + r * 2))).
Proof.
  intros.
  rewrite k_deriv_PI; try assumption.
  rewrite sign_eq_pos_den. reflexivity.

  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field. rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field. rewrite id in phase. clear id.

  specialize (Rle_0_sqr x₁) as [x1gt0 | x1eq0].
  specialize (Rplus_le_lt_compat _ _ _ _ (Rle_0_sqr (y₁-2*r)) x1gt0) as cont.
  lra.
  rewrite <- x1eq0 in *. clear x1eq0.
  rewrite Rplus_comm in phase.
  rewrite Rplus_0_r in *.

  assert ((y₁ - r)² = (y₁² + r² - 2 * r * y₁)) as id.
  unfold Rsqr. field. rewrite id in phase. clear id.
  assert (0 <  (y₁ - 2 * r) * y₁) as phase2.
  setr (y₁² - 2 * r * y₁).
  apply (Rplus_lt_reg_r (r²)).
  rewrite Rplus_comm.
  rewrite Rplus_0_r.
  rewrite (Rplus_comm (y₁² - 2 * r * y₁)).
  setr (y₁² + r² - 2 * r * y₁). assumption.

  destruct (Rlt_dec 0 y₁).
  rewrite <- (Rmult_0_l y₁) in phase2.
  apply Rmult_lt_reg_r in phase2.
  rewrite <- (Rmult_0_l (y₁ - 2 * r)).
  unfold Rsqr.
  apply Rmult_lt_compat_r; assumption. assumption.

  apply Rnot_lt_le in n.
  inversion_clear n as [y1lt0 |y1eq0].
  assert ((y₁ - 2 * r) * y₁ = -(y₁ - 2 * r) * (-y₁)) as id.
  field. rewrite id in phase2. clear id.
  assert (0 < - y₁) as zltny1. lra. clear y1lt0.
  rewrite Rsqr_neg.
  
  rewrite <- (Rmult_0_l (-y₁)) in phase2.
  apply Rmult_lt_reg_r in phase2; try assumption.
  rewrite <- (Rmult_0_l (-(y₁ - 2 * r))).
  unfold Rsqr.
  apply Rmult_lt_compat_r; assumption.

  subst.
  rewrite Rminus_0_l, <- Rsqr_neg.
  rewrite Rsqr_mult.
  apply Rmult_lt_0_compat; apply Rlt_0_sqr; lra.
Qed.
  
Lemma k_deriv_quadratic : forall x₁ y₁ r,
    forall z (zrng : -PI < z < PI)
           (rne0 : r <> 0)
           (phase :  straight r 0 0 0 x₁ y₁)
           (zne0 : z <> 0),
      (κ' x₁ y₁ r) z = r * ((2*r-y₁)*(tan (z/2))² - 2 * x₁ * tan (z/2) + y₁)
                             /((2 * (1-cos z)/(sin z)²) *
                               ((y₁ - r * (1-cos z))²+(x₁ - r * sin z)²)).
Proof.
  intros.
  inversion_clear zrng as [zlb zub].

  assert (sin z <> 0) as sinzne0.
  intro sinzeq0. apply zne0.
  assert (-PI < z <= PI) as zrng2.
   split. assumption. left. assumption.
  specialize (sinθeq0 _ zrng2 sinzeq0) as sval. clear zrng2.
  inversion_clear sval as [zeq0 |zeqPI]. assumption.
  
  exfalso. lra.

  assert (1 - cos z <> 0) as coszne1.
  intro. apply sinzne0.
  assert (cos z = 1) as coszeq1.
  apply (Rplus_eq_reg_r (- cos z)). setl 0. setr (1 - cos z).
  symmetry. assumption.
  destruct (Rle_dec 0 z).
  assert (z < 2*PI) as zlt2PI. lra.
  assert (0 <= z < 2*PI) as zrng. split; assumption.
  specialize (cosθeq1 _ zrng coszeq1) as zeq0.
  subst. apply sin_0.
  apply Rnot_le_lt in n.
  assert (0 <= - z) as zlenz.
  left. lra.
  assert (- z < 2*PI) as nzlt2PI. lra.
  assert (0 <= - z < 2*PI) as zrng. split; assumption.
  rewrite <- cos_neg in coszeq1.
  specialize (cosθeq1 _ zrng coszeq1) as nzeq0.
  assert (z = 0) as zeq02.
  apply (Rmult_eq_reg_l (-1)). setl (-z). setr 0. assumption.
  discrR.
  subst. apply sin_0.
  
  assert ((sin z)² <> 0) as sin2zne0. intro. apply sinzne0.
  apply Rsqr_eq_0. assumption.

  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field. rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field. rewrite id in phase. clear id.

  assert (~((x₁ - r * sin z) = 0 /\ (y₁ - r * (1- cos z)) = 0)) as dne0.
  intro noc. inversion_clear noc as [nox noy].
  assert (x₁ = r * sin z) as x1cd.
  apply (Rplus_eq_reg_r (- r * sin z)). setr 0. setl (x₁ - r * sin z).
  assumption.
  assert (y₁ = r * (1-cos z)) as y1cd.
  apply (Rplus_eq_reg_r (- r * (1-cos z))). setr 0. setl (y₁ - r * (1-cos z)).
  assumption.
  rewrite x1cd, y1cd in phase.
  assert (1 < 1) as c.
  apply (Rmult_lt_reg_l (r²)).
  apply Rsqr_pos_lt ; assumption.
  rewrite <- (sin2_cos2 z) at 2.
  setr ((r * sin z)² + (r * (1 - cos z) - r)²). setl r². assumption.
  lra.

  assert ((x₁ - r * sin z)² + (y₁ - r * (1 - cos z))² <> 0) as noc.
  intro oc. apply dne0.
  split.
  eapply Rplus_sqr_eq_0_l. apply oc.
  rewrite Rplus_comm in oc.
  eapply Rplus_sqr_eq_0_l. apply oc.
  
  unfold κ'.
  assert ((- r * sin z * (x₁ - r * sin z) - r * cos z * (- y₁ + r * (1 - cos z))) =
          r²*(1-cos z) + r*y₁*cos z - r * x₁ * sin z) as id.
  unfold Rsqr.
  setl ( - r * sin z *x₁ + r * cos z * y₁ + - r * cos z * r +
         r * r * ( (sin z)² + (cos z)²)). rewrite sin2_cos2. field.
  rewrite id. clear id.
  
  
  assert (r * ((2 * r - y₁) * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + y₁) =
          (r² * (1 - cos z) + r * y₁ * cos z - r * x₁ * sin z) *
          (2*(1-cos z)/(sin z)²)) as id.
  setr ((2 * r² * ((1 - cos z)/ (sin z))²) +
        2 *r * y₁ * (cos z / sin z) * ((1 - cos z) / (sin z)) -
        r * x₁ * 2 * ((1 - cos z) / (sin z))). assumption.
  rewrite <- tant2_2.
  assert (z = 2*(z/2)) as id. field.
  rewrite id at 4.
  rewrite id at 5.
  rewrite cos_2a, sin_2a.

  set (α := z/2) in *.

  assert (sin α <> 0) as sinane0.
  intro sinaeq0. apply zne0.
  assert (-PI < α <= PI) as arng.
  split. lra. left. lra.
  specialize (sinθeq0 _ arng sinaeq0) as sval. clear arng.
  inversion_clear sval as [zeq0 |zeqPI].
  unfold α in zeq0.
  apply (Rmult_eq_reg_r (/2)). setl (z/2). setr 0. assumption.
  apply Rinv_neq_0_compat. discrR.
  exfalso. lra.

  assert (cos α <> 0) as cosane0.
  intro cosaeq0. apply zne0.
  assert (-PI < α <= PI) as arng.
  split. lra. left. lra.
  exfalso.
  specialize (cosθeq0 _ arng cosaeq0) as sval. clear arng.
  inversion_clear sval as [aeqPI2 |zeqnPI2].
  lra.
  unfold α in zeqnPI2.
  assert (z = -PI) as zeqnPI.
  apply (Rmult_eq_reg_r (/2)). setl (z/2). setr (-PI/2). assumption.
  apply Rinv_neq_0_compat. discrR.
  lra.

  assert (((cos α)² - (sin α)²) = (1 - (tan α)²) * (cos α)²) as id4.
  unfold Rsqr.
  unfold tan. field. assumption. unfold Rsqr in id4. rewrite id4. clear id4.
  assert (2 * sin α * cos α = 2 * tan α * (cos α)²) as id5.
  unfold Rsqr. unfold tan. field. assumption. rewrite id5. clear id5.
  
  assert (((1 - (tan α)²) * (cos α)²) / (2 * tan α * (cos α)²) =
          (1 - (tan α)²) / (2 * tan α)) as id6.
  unfold Rsqr. unfold tan. field. split; assumption.
  fold ((cos α)²).
  fold ((tan α)²).
  rewrite id6. clear id6.
  
  setr (r * ((2 * r - y₁) *(tan α)² - x₁ * 2 * tan α +  y₁)).
  unfold tan.
  intro tanaeq0. apply sinane0.
  apply (Rmult_eq_reg_r (/ cos α)). setr 0. assumption.
  setl (sin α / cos α). assumption. assumption.
  apply Rinv_neq_0_compat. assumption.
  fieldrewrite (x₁ * 2* tan α) (2 * x₁ * tan α).
  reflexivity.
  assumption.

  setl (1 * (r² * (1 - cos z) + r * y₁ * cos z - r * x₁ * sin z)
              / ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²)).
  rewrite Rplus_comm in noc. assumption.

  assert ((2*(1-cos z)/(sin z)²)/(2*(1-cos z)/(sin z)²) = 1).
  field.
  split. assumption.
  assumption.
  rewrite <- H at 1.

  setl (2 * (1 - cos z) / (sin z)² *
        (r*r * (1-cos z) + r * y₁ * cos z - r * x₁ * sin z)
          / ((2 * (1 - cos z) / (sin z)²)
             * ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²))).
  split. assumption.
  split. rewrite Rplus_comm in noc. apply noc.
  assumption.
  
  fold (r²).
  setl (((r² * (1 - cos z) + r * y₁ * cos z - r * x₁ * sin z)
        * (2 * (1 - cos z) / (sin z)²)) *
        / (2 * (1 - cos z) / (sin z)² * ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²))).
  split. assumption.
  split. rewrite Rplus_comm in noc. apply noc.
  assumption.
  rewrite <- id.
  field.
  split. assumption.
  split. rewrite Rplus_comm in noc. apply noc.
  assumption.
Qed.

 
Lemma k_deriv_sign_rng : forall x₁ y₁ r,
    forall z (zrng : -PI < z < PI)
           (rne0 : r <> 0)
           (phase :  straight r 0 0 0 x₁ y₁),
      sign (κ' x₁ y₁ r z) =
      sign (r * ((2*r-y₁)*(tan (z/2))² - 2 * x₁ * tan (z/2) + y₁)).
Proof.
  intros.
  inversion zrng as [zlb zub].

  destruct (Req_dec z 0) as [zeq0| zne0].
  rewrite zeq0.
  fieldrewrite (0/2) 0.
  rewrite tan_0, Rsqr_0, Rmult_0_r, Rmult_0_r, Rminus_0_r, Rplus_0_l.
  apply k_deriv_sign_0; try assumption.

  assert (sin z <> 0) as sinzne0.
  intro sinzeq0. apply zne0.
  assert (-PI < z <= PI) as zrng2.
   split. assumption. left. assumption.
  specialize (sinθeq0 _ zrng2 sinzeq0) as sval. clear zrng2.
  inversion_clear sval as [zeq0 |zeqPI]. assumption.
  exfalso. lra.

  assert (1 - cos z <> 0) as coszne1.
  intro. apply sinzne0.
  assert (cos z = 1) as coszeq1.
  apply (Rplus_eq_reg_r (- cos z)). setl 0. setr (1 - cos z).
  symmetry. assumption.
  destruct (Rle_dec 0 z).
  assert (z < 2*PI) as zlt2PI. lra.
  assert (0 <= z < 2*PI) as zrng2. split; assumption.
  specialize (cosθeq1 _ zrng2 coszeq1) as zeq0.
  subst. apply sin_0.
  apply Rnot_le_lt in n.
  assert (0 <= - z) as zlenz.
  left. lra.
  assert (- z < 2*PI) as nzlt2PI. lra.
  assert (0 <= - z < 2*PI) as zrng2. split; assumption.
  rewrite <- cos_neg in coszeq1.
  specialize (cosθeq1 _ zrng2 coszeq1) as nzeq0.
  assert (z = 0) as zeq02.
  apply (Rmult_eq_reg_l (-1)). setl (-z). setr 0. assumption.
  discrR.
  subst. apply sin_0.

  assert (0 < 1 - cos z) as zlt1mcosz.
  specialize (COS_bound z) as [coszlb coszub].
  apply (Rplus_lt_reg_r (cos z)). setl (cos z). setr 1.
  inversion_clear coszub as [coszlt1 |coszeq1]. assumption.
  exfalso. apply coszne1. 
  rewrite coszeq1. field. clear coszne1.
  
  assert ((sin z)² <> 0) as sin2zne0. intro. apply sinzne0.
  apply Rsqr_eq_0. assumption.

  generalize phase. intro phase0.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.

  assert (~((x₁ - r * sin z) = 0 /\ (y₁ - r * (1- cos z)) = 0)) as dne0.
  intro noc. inversion_clear noc as [nox noy].
  assert (x₁ = r * sin z) as x1cd.
  apply (Rplus_eq_reg_r (- r * sin z)). setr 0. setl (x₁ - r * sin z).
  assumption.
  assert (y₁ = r * (1-cos z)) as y1cd.
  apply (Rplus_eq_reg_r (- r * (1-cos z))). setr 0. setl (y₁ - r * (1-cos z)).
  assumption.
  rewrite x1cd, y1cd in phase.
  assert (1 < 1) as c.
  apply (Rmult_lt_reg_l (r²)).
  apply Rsqr_pos_lt ; assumption.
  rewrite <- (sin2_cos2 z) at 2.
  setr ((r * sin z)² + (r * (1 - cos z) - r)²). setl r². assumption.
  lra.

  assert (0 < (y₁ - r * (1-cos z))²+(x₁ - r * sin z)²) as posgt0.
  destruct (Req_dec (x₁ - r * sin z) 0) as [xceq0 | xcne0].
  rewrite xceq0. rewrite xceq0 in dne0.
  assert ((y₁ - r * (1 - cos z))² + 0² = (y₁ - r * (1 - cos z))²) as id.
  unfold Rsqr. field. rewrite id. clear id.
  assert (y₁ - r * (1 - cos z) <> 0) as ycne0.
  intro. apply dne0. split. reflexivity. assumption.
  apply Rsqr_pos_lt. assumption.
  apply Rplus_le_lt_0_compat.
  apply Rle_0_sqr.
  apply Rsqr_pos_lt. assumption.

  assert (0 < (2 * (1-cos z)/(sin z)²) *
              ((y₁ - r * (1-cos z))²+(x₁ - r * sin z)²)) as R0ltden.
  apply Rmult_lt_0_compat; [|assumption].
  apply Rmult_lt_0_compat.
  apply Rmult_lt_0_compat; [ lra |assumption].
  apply Rinv_0_lt_compat.
  specialize (Rle_0_sqr (sin z)) as R0lesinz.
  inversion_clear R0lesinz as [R0ltsinz | R0eqsinz]. assumption.
  exfalso. apply sin2zne0. rewrite R0eqsinz. reflexivity.

  rewrite k_deriv_quadratic; try assumption.
  apply sign_eq_pos_den. assumption.
Qed.


Lemma k_deriv_sign : forall x₁ y₁ r z,
    forall (cne0 : cos (z/2) <> 0)
           (rne0 : r <> 0)
           (phase :  straight r 0 0 0 x₁ y₁),
      sign (κ' x₁ y₁ r z) =
      sign (r * ((2*r-y₁)*(tan (z/2))² - 2 * x₁ * tan (z/2) + y₁)).
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  assert (2 * PI > 0) as tpigt0; [ lra|].
  specialize (inrange_mT2T2 z _ tpigt0) as [k Zrng0].
  rewrite (k'_periodic _ _ _ k).
  rewrite <- (tan_period _ k); [|assumption].
  fieldrewrite (z / 2 + IZR k * PI) ((z + 2 * IZR k * PI)/2).
  fieldrewrite (2 * IZR k * PI) (IZR k * (2*PI)).
  set (Z := z + IZR k * (2 * PI)) in *.
  assert (-PI < Z <= PI) as Zrng ;[  lra|].
  
  destruct Zrng as [zlb [zub |zpi]].
  assert (-PI < Z < PI) as zrng. lra.
  apply k_deriv_sign_rng; try assumption.

  exfalso.
  unfold Z in zpi.
  clear - cne0 zpi.
  assert (z = (2* IZR (- k) * PI)+ PI) as id.
  apply (Rplus_eq_reg_r (IZR k * (2 * PI))).
  rewrite opp_IZR, zpi. field.
  apply cne0. clear - id.
  rewrite id. clear id.
  
  fieldrewrite ((2 * IZR (- k) * PI + PI) / 2)
               (IZR (- k) * PI + PI / 2).
  apply cos_eq_0_1.
  exists (-k)%Z.
  reflexivity.
Qed.

Lemma straight_std_impl_ineq : forall r x₁ y₁ (phase : straight r 0 0 0 x₁ y₁),
    r² < x₁² + (y₁ - r)².
Proof.
  intros.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.
  assumption.
Qed.

Lemma straight_symmetry : forall r θ₀ x₀ y₀ x₁ y₁,
    straight r θ₀ x₀ y₀ x₁ y₁ -> straight (-r) (-θ₀) x₀ (-y₀) x₁ (-y₁).
Proof.
  intros *. intro st.
  unfold straight, Tcx, Tcy in *.
  rewrite <- (Rsqr_neg r).
  fieldrewrite (- r * cos (PI / 2 + - θ₀)) (r * - cos (PI / 2 + - θ₀)).
  rewrite <- sin_cos, <- cos_sin, cos_neg, sin_neg, sin_cos, (cos_sin θ₀).
  fieldrewrite (- - cos (PI / 2 + θ₀)) (cos (PI / 2 + θ₀)).
  fieldrewrite (- y₁ - (- y₀ + - r * sin (PI / 2 + θ₀)))
               (- (y₁ - (y₀ + r * sin (PI / 2 + θ₀)))).
  rewrite <- Rsqr_neg. assumption.
Qed.

Lemma str_noton :
  forall x y r (phase : straight r 0 0 0 x y) i,
    (~ (x - r * sin i = 0 /\ y - r * (1 - cos i) = 0)).
Proof.
  intros.
  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x - (0 + r * 0) = x) as id. field.
  rewrite id in phase. clear id.
  assert (y - (0 + r * 1) = y - r) as id. field.
  rewrite id in phase. clear id.

  intros notx1y1.
  inversion_clear notx1y1 as [notx1 noty1].
  
  assert (x² + (y - r)² = x² - (2 * r - y) * y + r²) as id. unfold Rsqr. field.
  rewrite id in phase. clear id.
  rewrite <- (Rplus_0_l r²) in phase at 1.
  apply RIneq.Rplus_lt_reg_r in phase.
  assert (x = r * sin i) as x1def.
  apply (Rplus_eq_reg_r (- r * sin i)).
  setr 0. setl (x - r * sin i). assumption.
  assert (y = r * (1-cos i)) as y1def.
  apply (Rplus_eq_reg_r (- r * (1-cos i))).
  setr 0. setl (y - r * (1-cos i)). assumption.
  rewrite x1def, y1def in phase.
  assert ((r * sin i)² - (2 * r - r * (1 - cos i)) * (r * (1 - cos i)) = 0) as id.
  unfold Rsqr.
  setl (r * r * (sin i * sin i + cos i * cos i - 1)).
  change (r * r * ((sin i)² + (cos i)² - 1) = 0).
  rewrite sin2_cos2. field.
  rewrite id in phase. lra.
Qed.

(* end hide *)

Lemma k_deriv_sign_lin_rpos : forall x₁ y₁ r,
    forall z (zrng : -PI < z < PI)
           (R0ltr : 0 < r)
           (phase :  straight r 0 0 0 x₁ y₁)
           (nonquad : 2*r - y₁ = 0),
      ((0 < x₁ /\ z/2 < atan (y₁ / (2 * x₁)) -> sign (κ' x₁ y₁ r z) = 1) /\
       (0 < x₁ /\ z/2 > atan (y₁ / (2 * x₁)) -> sign (κ' x₁ y₁ r z) = - 1) /\
       (x₁ = 0 -> False) /\
       (x₁ < 0 /\ z/2 < atan (y₁ / (2 * x₁)) -> sign (κ' x₁ y₁ r z) = - 1) /\
       (x₁ < 0 /\ z/2 > atan (y₁ / (2 * x₁)) -> sign (κ' x₁ y₁ r z) = 1)).
Proof.
  intros.
  rewrite k_deriv_sign_rng ; try assumption ; try (intro; lra).
  rewrite nonquad.
  split.
  intros cond. inversion_clear cond as [R0ltx1 zbnd].
  assert (sign (r * (0 * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + y₁)) =
          sign ( - 2 * x₁ * tan (z / 2) + y₁)) as id0.
  assert ((0 * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + y₁) =
          ( - 2 * x₁ * tan (z / 2) + y₁)) as id. unfold Rsqr. field.
  rewrite id. clear id.
  rewrite sign_mult.
  rewrite sign_eq_1; [|assumption].
  field.
  rewrite id0. clear id0.
  inversion_clear zrng as [zlb zub].
  rewrite sign_eq_1. reflexivity.
  apply (Rplus_lt_reg_l (2 * x₁ * tan (z / 2))).
  setl (2 * x₁ * tan (z / 2)). setr y₁.
  apply (Rmult_lt_reg_l (/(2 * x₁))).
  apply Rinv_0_lt_compat.
  apply (Rmult_lt_reg_l (/2)).
  apply Rinv_0_lt_compat. lra.
  setl 0. setr x₁. assumption.
  setl (tan (z / 2)). intro. lra.
  setr (y₁/ (2 * x₁)). intro. lra.
  rewrite <- atan_right_inv.
  apply tan_increasing.
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (y₁ / (2 * x₁))) as [abl abu].
  assumption.

  split.
  intros cond. inversion_clear cond as [R0ltx1 zbnd].
  assert (sign (r * (0 * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + y₁)) =
          sign ( - 2 * x₁ * tan (z / 2) + y₁)) as id0.
  assert ((0 * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + y₁) =
          ( - 2 * x₁ * tan (z / 2) + y₁)) as id. unfold Rsqr. field.
  rewrite id. clear id.
  rewrite sign_mult.
  rewrite sign_eq_1; [|assumption].
  field.
  rewrite id0. clear id0.
  inversion_clear zrng as [zlb zub].
  rewrite sign_eq_m1. reflexivity.
  apply (Rplus_lt_reg_l (2 * x₁ * tan (z / 2))).
  setr (2 * x₁ * tan (z / 2)). setl y₁.
  apply (Rmult_lt_reg_l (/(2 * x₁))).
  apply Rinv_0_lt_compat.
  apply (Rmult_lt_reg_l (/2)).
  apply Rinv_0_lt_compat. lra.
  setl 0. setr x₁. assumption.
  setr (tan (z / 2)). intro. lra.
  setl (y₁/ (2 * x₁)). intro. lra.

  apply Rgt_lt in zbnd.
  rewrite <- (atan_right_inv (y₁ / (2 * x₁))).
  apply tan_increasing.
  specialize (atan_bound (y₁ / (2 * x₁))) as [abl abu].
  assumption.
  assumption. lra.

  split.
  intros x1eq0. 
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.
  rewrite x1eq0 in phase.
  assert (y₁ = 2 * r) as y1def.
  apply (Rplus_eq_reg_r (-y₁)). setl 0. setr (2 * r - y₁). symmetry. assumption.
  rewrite y1def in phase.
  assert (0² + (2 * r - r)² = r²) as id.
  unfold Rsqr. field. rewrite id in phase. lra.

  split. intros cond.
  inversion_clear cond as [x1lt0 zval].
  assert (sign (r * (0 * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + y₁)) =
          sign ( - 2 * x₁ * tan (z / 2) + y₁)) as id0.
  assert ((0 * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + y₁) =
          ( - 2 * x₁ * tan (z / 2) + y₁)) as id. unfold Rsqr. field.
  rewrite id. clear id.
  rewrite sign_mult.
  rewrite sign_eq_1; [|assumption].
  field.
  rewrite id0. clear id0.
  inversion_clear zrng as [zlb zub].
  rewrite sign_eq_m1. reflexivity.
  apply (Rplus_lt_reg_l (2 * x₁ * tan (z / 2))).
  setr (2 * x₁ * tan (z / 2)). setl y₁.
  apply (Rmult_lt_reg_l (/(2 * (- x₁)))).
  apply Rinv_0_lt_compat.
  apply (Rmult_lt_reg_l (/2)).
  apply Rinv_0_lt_compat. lra.
  setl 0. setr (-x₁). lra. 
  setr (- tan (z / 2)). intro. lra.
  setl (- (y₁/ (2 * x₁))). intro. lra.
  apply Ropp_lt_contravar.
  rewrite <- atan_right_inv.
  apply tan_increasing.
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (y₁ / (2 * x₁))) as [abl abu].
  assumption.

  intros cond.
  inversion_clear cond as [x1lt0 zval].
  assert (sign (r * (0 * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + y₁)) =
          sign ( - 2 * x₁ * tan (z / 2) + y₁)) as id0.
  assert ((0 * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + y₁) =
          ( - 2 * x₁ * tan (z / 2) + y₁)) as id. unfold Rsqr. field.
  rewrite id. clear id.
  rewrite sign_mult.
  rewrite sign_eq_1; [|assumption].
  field.
  rewrite id0. clear id0.
  inversion_clear zrng as [zlb zub].
  rewrite sign_eq_1. reflexivity.
  apply (Rplus_lt_reg_l (2 * x₁ * tan (z / 2))).
  setl (2 * x₁ * tan (z / 2)). setr y₁.
  apply (Rmult_lt_reg_l (/(2 * (- x₁)))).
  apply Rinv_0_lt_compat.
  apply (Rmult_lt_reg_l (/2)).
  apply Rinv_0_lt_compat. lra.
  setl 0. setr (- x₁). lra. 
  setl (- tan (z / 2)). intro. lra.
  setr (- (y₁/ (2 * x₁))). intro. lra.
  apply Ropp_lt_contravar.
  rewrite <- (atan_right_inv (y₁ / (2 * x₁))).
  apply tan_increasing.
  specialize (atan_bound (y₁ / (2 * x₁))) as [abl abu].
  assumption.
  apply Rgt_lt in zval. assumption. lra.
Qed.

Lemma k_deriv_sign_lin2 : forall x₁ y₁ r,
    forall z (zrng : -PI < z < PI)
           (R0ltr : r <> 0)
           (phase :  straight r 0 0 0 x₁ y₁)
           (nonquad : 2*r - y₁ = 0),
      sign (κ' x₁ y₁ r z) = 0 -> 
      ((z/2 = atan (y₁ / (2 * x₁))) /\ (x₁ <> 0)).
Proof.
  intros until 3. intros ytop sgnkpeq0.
  assert (y₁ = 2 * r) as y1def.
  apply (Rplus_eq_reg_r (-y₁)). setl 0. rewrite <- ytop. field.

  destruct (Req_dec x₁ 0).
  + exfalso.
    specialize (straight_std_impl_ineq _ _ _ phase) as phaseb.
    subst.
    clear ytop.
    assert (0² + (2 * r - r)² = r²) as id. unfold Rsqr. field.
    rewrite id in phaseb. clear id. lra.
                    
  + split;[|assumption].
    rewrite k_deriv_sign_rng in sgnkpeq0; auto.
    rewrite ytop in sgnkpeq0.
    assert ((0 * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + y₁) =
            ( - 2 * x₁ * tan (z / 2) + y₁)) as id. unfold Rsqr. field.
    rewrite id in sgnkpeq0. clear id.
    rewrite sign_mult in sgnkpeq0.
    assert (sign r <> 0) as srne0. {
      unfold sign.
      destruct (total_order_T 0 r) as [[zlt|zeq]|zgt]; 
        [discrR| exfalso; apply R0ltr; auto| discrR]. }
    assert (sign (-2 * x₁ * tan (z / 2) + y₁) = 0) as teq0. {
      apply (Rmult_eq_reg_l (sign r)); try assumption.
      rewrite Rmult_0_r.
      assumption. }
    clear sgnkpeq0.
    unfold sign in teq0.

    destruct (total_order_T 0 (-2 * x₁ * tan (z / 2) + y₁)) ;
      [destruct s; [ lra| clear teq0] | lra].

    assert (-PI/2 < z/2 < PI/2) as z2rng.
    inversion_clear zrng.
    apply (Rmult_lt_compat_r (/2)) in H0; [| lra].
    apply (Rmult_lt_compat_r (/2)) in H1; [| lra].
    split; lra.

    specialize (atan_bound (y₁ / (2 * x₁))) as atbnd.

    apply (tan_is_inj _ _ z2rng atbnd).
    rewrite atan_right_inv.
    apply (Rmult_eq_reg_l (2 * x₁)). setr y₁. assumption.
    apply (Rplus_eq_reg_l (- 2 * x₁* tan (z / 2))). setl 0.
    assumption. intro. apply H.
    apply (Rmult_eq_reg_l 2). setr 0. assumption.
    discrR.
Qed.


Lemma k_deriv_sign_lin_rpos3 : forall x₁ y₁ r,
    forall z (zrng : -PI < z < PI)
           (R0ltr : 0 < r)
           (phase :  straight r 0 0 0 x₁ y₁)
           (zne0 : z <> 0)
           (nonquad : y₁ = 0),
      sign (κ' x₁ y₁ r z) = 0 -> 
      (z/2 = atan (x₁ / r)).
Proof.
  intros until 4. intros ytop sgnkpeq0.
  rename ytop into y1def.
  
  destruct (Req_dec x₁ 0).
  + exfalso.
    specialize (straight_std_impl_ineq _ _ _ phase) as phaseb.
    subst.
    assert (0² + (0 - r)² = r²) as id. unfold Rsqr. field.
    rewrite id in phaseb. clear id. lra.
                    
  + rewrite k_deriv_sign_rng in sgnkpeq0; auto; [| intro; lra].
    rewrite y1def in sgnkpeq0.
    assert ((r * ((2 * r - 0) * (tan (z / 2))² - 2 * x₁ * tan (z / 2) + 0)) =
            ( (2 * r) * ((r * tan (z / 2) - x₁ )* tan (z / 2)))) as id.
    unfold Rsqr. field.
    rewrite id in sgnkpeq0. clear id.
    rewrite sign_mult in sgnkpeq0.
    rewrite sign_eq_1 in sgnkpeq0; try lra.
    rewrite Rmult_1_l in sgnkpeq0.
    unfold sign in sgnkpeq0.

    destruct (total_order_T 0 ((r * tan (z / 2) - x₁) * tan (z / 2))) ; [|lra].
    destruct s; [ exfalso; lra|].
    clear sgnkpeq0.

    assert (-PI/2 < z/2 < PI/2) as z2rng. {
    inversion_clear zrng as [zlb zub].
    apply (Rmult_lt_compat_r (/2)) in zlb; [| lra].
    apply (Rmult_lt_compat_r (/2)) in zub; [| lra].
    split; lra.
    }

    assert (tan (z/2) <> 0) as tanz2ne0. {
    intro. rewrite <- tan_0 in H0.
    apply tan_is_inj in H0; try assumption.  apply zne0.
    apply (Rmult_eq_reg_r (/2)). setr 0. setl (z/2). assumption.
    apply Rinv_neq_0_compat. discrR.
    specialize PI_RGT_0 as PI_RGT_0. 
    split; [|lra].
    apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr 0. lra. }
    
    symmetry in e.
    apply Rmult_integral in e.
    inversion_clear e as [zeqn |contr]; [|exfalso; auto].
    apply tan_is_inj; try assumption; [ apply atan_bound|].
    rewrite atan_right_inv.
    apply (Rmult_eq_reg_r r).
    apply (Rplus_eq_reg_r (- x₁)). setr 0. intro. lra.
    rewrite <- zeqn. field. intro. lra.
Qed.

Lemma k'_symmetry : forall x₁ y₁ r z,
    (κ' x₁ y₁ r z) = (κ' x₁ (- y₁) (- r) (-z)).
Proof.
  intros.
  unfold κ'.
  assert (((- y₁ - - r * (1 - cos (- z)))² + (x₁ - - r * sin (- z))²) =
          ((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²)) as eqd.
  rewrite sin_neg, cos_neg. unfold Rsqr. field.
  rewrite eqd. clear eqd.
  set (D:=((y₁ - r * (1 - cos z))² + (x₁ - r * sin z)²)) in *.

  assert ((- r * sin z * (x₁ - r * sin z) - r * cos z * (- y₁ + r * (1 - cos z))) =
          (- - r * sin (- z) * (x₁ - - r * sin (- z)) -
           - r * cos (- z) * (- - y₁ + - r * (1 - cos (- z))))) as id.
  rewrite sin_neg, cos_neg. field. rewrite id. reflexivity.

Qed.


Lemma k_deriv_sign_lin_rneg : forall x₁ y₁ r,
    forall z (zrng : -PI < z < PI)
           (rlt0 : r < 0)
           (phase :  straight r 0 0 0 x₁ y₁)
           (zne0 : z <> 0)
           (nonquad : 2*r - y₁ = 0),
      ((0 < x₁ /\ z/2 < atan (y₁ / (2 * x₁)) -> sign (κ' x₁ y₁ r z) = - 1) /\
       (0 < x₁ /\ z/2 > atan (y₁ / (2 * x₁)) -> sign (κ' x₁ y₁ r z) = 1) /\
       (x₁ = 0 -> False) /\
       (x₁ < 0 /\ z/2 < atan (y₁ / (2 * x₁)) -> sign (κ' x₁ y₁ r z) = 1) /\
       (x₁ < 0 /\ z/2 > atan (y₁ / (2 * x₁)) -> sign (κ' x₁ y₁ r z) = - 1)).
Proof.
  intros.
  assert (0 < (-r)) as R0ltr. lra.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.
  
  assert (straight (- r) 0 0 0 x₁ (-y₁)) as phase2.
  unfold straight, Tcx, Tcy.
  assert ((PI / 2 + 0) = PI/2) as id. field.
  rewrite id. clear id.
  rewrite cos_PI2, sin_PI2.
  assert (x₁ - (0 + - r * 0) = x₁) as id. field.
  rewrite id. clear id.
  assert (- y₁ - (0 + - r * 1) = - y₁ + r) as id. field.
  rewrite id. clear id.

  assert ((- r)² = (r)²) as id. unfold Rsqr. field. rewrite id. clear id.
  assert ((- y₁ + r)² = (y₁ - r)²) as id. unfold Rsqr. field. rewrite id. assumption.

  assert (2 * (-r) - (-y₁) = 0) as nonquad2.
  rewrite <- Ropp_0.
  rewrite <- nonquad. field.

  assert (- PI < - z < PI) as zrng2. inversion_clear zrng as [zlb zub].
  split; lra.
  assert (- z <> 0) as zne02. intro. apply zne0.
  apply (Rmult_eq_reg_r (-1)). setr 0. setl (-z). assumption. discrR.

  specialize (k_deriv_sign_lin_rpos _ _ (-r) _ zrng2 R0ltr phase2 nonquad2)
    as [c1 [c2 [c3 [c4 c5]]]].

  rewrite k'_symmetry.

  split. intro pc. inversion_clear pc as [xbnd zlb].
  apply c2. split. assumption.
  fieldrewrite (- y₁ / (2 * x₁)) (- (y₁ / (2 * x₁))).
  unfold not. apply c3.
  rewrite atan_opp. setl (- (z/2)).
  apply Ropp_lt_gt_contravar. assumption.

  split. intro pc. inversion_clear pc as [xbnd zlb].
  apply c1. split. assumption.
  fieldrewrite (- y₁ / (2 * x₁)) (- (y₁ / (2 * x₁))).
  unfold not. apply c3.
  rewrite atan_opp. setl (- (z/2)).
  apply Ropp_lt_gt_contravar. assumption.

  split. apply c3.

  split. intro pc. inversion_clear pc as [xbnd zlb].
  apply c5. split. assumption.
  fieldrewrite (- y₁ / (2 * x₁)) (- (y₁ / (2 * x₁))).
  unfold not. apply c3.
  rewrite atan_opp. setl (- (z/2)).
  apply Ropp_lt_gt_contravar. assumption.

  intro pc. inversion_clear pc as [xbnd zlb].
  apply c4. split. assumption.
  fieldrewrite (- y₁ / (2 * x₁)) (- (y₁ / (2 * x₁))).
  unfold not. apply c3.
  rewrite atan_opp. setl (- (z/2)).
  apply Ropp_lt_gt_contravar. assumption.
Qed.

Lemma k_deriv_sign_quad :
  forall x₁ y₁ r z
         (rne0 : r <> 0)
         (phase :  straight r 0 0 0 x₁ y₁)
         (Ane0 : 2 * r - y₁ <> 0),
    (z/2 = atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) \/
     z/2 = atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) ->
     sign (κ' x₁ y₁ r z) = 0 ).
Proof.
  intros.

  assert (-PI < z < PI) as zrng. {
    destruct H.
    specialize (atan_bound ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                              / (2 * r - y₁))) as [atl atu].
    lra.
    specialize (atan_bound ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                              / (2 * r - y₁))) as [atl atu].
    lra.
  }
  
  generalize phase. intro Dnneg.
  unfold straight, Tcx, Tcy in Dnneg.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in Dnneg. clear id.
  rewrite cos_PI2, sin_PI2 in Dnneg.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in Dnneg. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in Dnneg. clear id.
  assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
  rewrite id in Dnneg. clear id.
  rewrite <- (Rplus_0_l r²) in Dnneg at 1.
  apply RIneq.Rplus_lt_reg_r, Rlt_le in Dnneg.
  
  inversion_clear H as [c1 |c2].
  
  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase).
  rewrite (factor_quad _ _ _ _ Ane0); [| assumption].
  assert ((tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))
          = 0) as id.
  apply (Rplus_eq_reg_r ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setr ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setl (tan (z/2)). assumption.
  rewrite c1.
  rewrite atan_right_inv. reflexivity.
  rewrite id.
  fieldrewrite (r * ((2 * r - y₁) *
                     ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                       / (2 * r - y₁)) * 0)))
               0. assumption.
  apply sign_0.

  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase).
  rewrite (factor_quad _ _ _ _ Ane0); [| assumption].
  assert ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))
          = 0) as id.
  apply (Rplus_eq_reg_r ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setr ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setl (tan (z/2)). assumption.
  rewrite c2.
  rewrite atan_right_inv. reflexivity.
  rewrite id.
  fieldrewrite (r * ((2 * r - y₁) *
                     (0 *(tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                       / (2 * r - y₁)))))
               0. assumption.
  apply sign_0.
Qed.


Lemma k_deriv_sign_quad2 : forall x₁ y₁ r,
    forall z (zrng : -PI < z < PI)
           (rne0 : r <> 0)
           (phase :  straight r 0 0 0 x₁ y₁)
           (Ane0 : 2 * r - y₁ <> 0),
      sign (κ' x₁ y₁ r z) = 0 -> 
      (z/2 = atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) \/
       z/2 = atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
Proof.
  intros.

  generalize phase. intro Dnneg.
  unfold straight, Tcx, Tcy in Dnneg.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in Dnneg. clear id.
  rewrite cos_PI2, sin_PI2 in Dnneg.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in Dnneg. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in Dnneg. clear id.
  assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
  rewrite id in Dnneg. clear id.
  rewrite <- (Rplus_0_l r²) in Dnneg at 1.
  apply RIneq.Rplus_lt_reg_r, Rlt_le in Dnneg.

  rewrite k_deriv_sign_rng in H.
  rewrite sign_mult in H.
  apply Rmult_integral in H.
  inversion_clear H as [im | gd].
  exfalso.
  apply sign_neq_0 in rne0.
  apply rne0. assumption.
  rewrite (factor_quad (2 * r - y₁) x₁ y₁ (tan (z / 2)) Ane0 Dnneg) in gd.
  rewrite sign_mult in gd. 
  apply Rmult_integral in gd.
  inversion_clear gd as [bd | gd2].
  exfalso.
  apply sign_neq_0 in Ane0.
  apply Ane0. assumption.
  
  rewrite sign_mult in gd2.
  apply Rmult_integral in gd2.
  inversion_clear gd2 as [Pse0 | Mse0].
  right.
  apply tan_is_inj.
  inversion_clear zrng.
  split.
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.
  apply atan_bound.
  rewrite atan_right_inv.
  apply (Rplus_eq_reg_r (- (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setr 0. assumption.
  setl (tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)).
  assumption.

  destruct (Req_dec (tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                       / (2 * r - y₁)) 0).
  rewrite H. reflexivity.
  exfalso.
  apply sign_neq_0 in H. apply H. assumption.

  left.
  apply tan_is_inj.
  inversion_clear zrng.
  split.
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.
  apply atan_bound.
  rewrite atan_right_inv.
  apply (Rplus_eq_reg_r (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setr 0. assumption.
  setl (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)).
  assumption.

  destruct (Req_dec (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                       / (2 * r - y₁)) 0).
  rewrite H. reflexivity.
  exfalso.
  apply sign_neq_0 in H. apply H. assumption.
  assumption. assumption. assumption. 
Qed.

Lemma k_deriv_sign_quad_Apos_rpos : forall x₁ y₁ r,
    forall (Apos : 0 < 2*r - y₁)
           (R0ltr : 0 < r)
           (phase :  straight r 0 0 0 x₁ y₁)
           z (zrng : -PI < z < PI),
      ((atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z/2 <
        atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) ->
             sign (κ' x₁ y₁ r z) = - 1) /\
       (z/2 < atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) \/
        atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z/2 ->
        sign (κ' x₁ y₁ r z) = 1)).
Proof.
  intros.

  generalize phase. intro Dnneg.
  unfold straight, Tcx, Tcy in Dnneg.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in Dnneg. clear id.
  rewrite cos_PI2, sin_PI2 in Dnneg.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in Dnneg. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in Dnneg. clear id.
  assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
  rewrite id in Dnneg. clear id.
  rewrite <- (Rplus_0_l r²) in Dnneg at 1.
  apply RIneq.Rplus_lt_reg_r, Rlt_le in Dnneg.
  
  assert (r <> 0) as rne0. intro; lra.
  assert (2 * r - y₁ <> 0) as trmyne0. intro. lra.
  repeat split; try intro c;
    (inversion_clear c as [c1 c2] || inversion_clear c as [c1 | c2]).
  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_m1. reflexivity.
  setr (r*0). apply Rmult_lt_compat_l; [assumption|].
  setr ((2*r-y₁)*0). apply Rmult_lt_compat_l; [assumption|].
  fieldrewrite (tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))
               (-1 * ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) -
                      tan (z / 2))).
  assumption.
  setl (- (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2)) *
           ((tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))).
  assumption.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setl (tan (z/2)).
  rewrite <- atan_right_inv.
  apply tan_increasing. inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  apply (Rplus_lt_reg_r ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setl ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing. 
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.


  assert (z / 2 < atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
    as c2.
  apply (Rlt_le_trans _ (atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  assumption.
  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sp.
  inversion_clear sp as [R0eqs | R0lts]. left.
  apply atan_increasing.
  apply (Rplus_lt_reg_r (-(x₁/(2 * r - y₁)))).
  setl (- (sqrt (x₁² - (2 * r - y₁) * y₁) / (2 * r - y₁))). assumption.
  setr ((sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  apply pos_opp_lt.
  apply (Rmult_lt_reg_l (2 * r - y₁)). assumption. setl 0.
  setr (sqrt (x₁² - (2 * r - y₁) * y₁)). assumption. assumption.
  right. rewrite <- R0lts.
  fieldrewrite (x₁ - 0) (x₁ + 0). reflexivity.

  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_1. reflexivity.
  setl (r*0). apply Rmult_lt_compat_l; [assumption|].
  setl ((2*r-y₁)*0). apply Rmult_lt_compat_l; [assumption|].
  setr (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2)) *
        ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2))).
  assumption.
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))). assumption.
  setl (tan (z/2)).
  rewrite <- (atan_right_inv).
  apply tan_increasing. inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setl (tan (z/2)). 
  rewrite <- (atan_right_inv).
  apply tan_increasing.  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.

  assert (atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z / 2)
    as c1.
  apply (Rle_lt_trans _ (atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sp.
  inversion_clear sp as [R0eqs | R0lts]. left.
  apply atan_increasing.
  apply (Rplus_lt_reg_r (-(x₁/(2 * r - y₁)))).
  setl (- (sqrt (x₁² - (2 * r - y₁) * y₁) / (2 * r - y₁))). assumption.
  setr ((sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  apply pos_opp_lt.
  apply (Rmult_lt_reg_l (2 * r - y₁)). assumption. setl 0.
  setr (sqrt (x₁² - (2 * r - y₁) * y₁)). assumption. assumption.
  right. rewrite <- R0lts.
  fieldrewrite (x₁ - 0) (x₁ + 0). reflexivity.
  assumption.

  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_1. reflexivity.
  setl (r*0). apply Rmult_lt_compat_l; [assumption|].
  setl ((2*r-y₁)*0). apply Rmult_lt_compat_l; [assumption|].
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setl (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing.
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.

  apply (Rplus_lt_reg_r (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  setl ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing.
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.
Qed.

Lemma k_deriv_sign_quad_Apos_rneg : forall x₁ y₁ r,
    forall (Apos : 0 < 2*r - y₁)
           (rlt0 : r < 0)
           (phase :  straight r 0 0 0 x₁ y₁)
           z (zrng : -PI < z < PI),
      ((atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z/2 <
       atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) ->
             sign (κ' x₁ y₁ r z) = 1) /\
       (z/2 < atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) \/
        atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z/2 ->
        sign (κ' x₁ y₁ r z) = - 1)).
Proof.
  intros.

  generalize phase. intro Dnneg.
  unfold straight, Tcx, Tcy in Dnneg.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in Dnneg. clear id.
  rewrite cos_PI2, sin_PI2 in Dnneg.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in Dnneg. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in Dnneg. clear id.
  assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
  rewrite id in Dnneg. clear id.
  rewrite <- (Rplus_0_l r²) in Dnneg at 1.
  apply RIneq.Rplus_lt_reg_r, Rlt_le in Dnneg.
  
  assert (r <> 0) as rne0. intro; lra.
  assert (2 * r - y₁ <> 0) as trmyne0. intro. lra.
  repeat split; try intro c;
    (inversion_clear c as [c1 c2] || inversion_clear c as [c1 | c2]).
  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase ).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_1. reflexivity.
  rewrite <- (Ropp_involutive r) at 1.
  setr (- (- r *
  ((2 * r - y₁) *
   ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
    (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))))).
  assumption.
  setl (-0).
  apply Ropp_lt_contravar.
  setr (-r*0).
  apply Rmult_lt_compat_l; [lra|].
  setr ((2*r-y₁)*0). apply Rmult_lt_compat_l; [assumption|].
  fieldrewrite (tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))
               (-1 * ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) -
                      tan (z / 2))).
  assumption.
  setl (- (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2)) *
           ((tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))).
  assumption.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setl (tan (z/2)).
  rewrite <- atan_right_inv.
  apply tan_increasing. inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  apply (Rplus_lt_reg_r ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setl ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing. 
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.


  assert (z / 2 < atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
    as c2.
  apply (Rlt_le_trans _ (atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  assumption.
  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sp.
  inversion_clear sp as [R0eqs | R0lts]. left.
  apply atan_increasing.
  apply (Rplus_lt_reg_r (-(x₁/(2 * r - y₁)))).
  setl (- (sqrt (x₁² - (2 * r - y₁) * y₁) / (2 * r - y₁))). assumption.
  setr ((sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  apply pos_opp_lt.
  apply (Rmult_lt_reg_l (2 * r - y₁)). assumption. setl 0.
  setr (sqrt (x₁² - (2 * r - y₁) * y₁)). assumption. assumption.
  right. rewrite <- R0lts.
  fieldrewrite (x₁ - 0) (x₁ + 0). reflexivity.

  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase ).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_m1. reflexivity.
  rewrite <- (Ropp_involutive r) at 1.
  setl (- r *
        -((2 * r - y₁) *
          ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
           (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))).
  assumption.
  setr (-r*0). apply Rmult_lt_compat_l; [lra|].
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  setl ((2*r-y₁)*0). apply Rmult_lt_compat_l; [assumption|].
  setr (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2)) *
        ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2))).
  assumption.
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))). assumption.
  setl (tan (z/2)).
  rewrite <- (atan_right_inv).
  apply tan_increasing. inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setl (tan (z/2)). 
  rewrite <- (atan_right_inv).
  apply tan_increasing.  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.

  assert (atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z / 2)
    as c1.
  apply (Rle_lt_trans _ (atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sp.
  inversion_clear sp as [R0eqs | R0lts]. left.
  apply atan_increasing.
  apply (Rplus_lt_reg_r (-(x₁/(2 * r - y₁)))).
  setl (- (sqrt (x₁² - (2 * r - y₁) * y₁) / (2 * r - y₁))). assumption.
  setr ((sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  apply pos_opp_lt.
  apply (Rmult_lt_reg_l (2 * r - y₁)). assumption. setl 0.
  setr (sqrt (x₁² - (2 * r - y₁) * y₁)). assumption. assumption.
  right. rewrite <- R0lts.
  fieldrewrite (x₁ - 0) (x₁ + 0). reflexivity.
  assumption.

  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase ).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_m1. reflexivity.
  rewrite <- (Ropp_involutive r) at 1.
  setl (- r *
        -((2 * r - y₁) *
          ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
           (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))).
  assumption.
  setr (-r*0). apply Rmult_lt_compat_l; [lra|].
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  setl ((2*r-y₁)*0). apply Rmult_lt_compat_l; [assumption|].
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setl (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing.
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.

  apply (Rplus_lt_reg_r (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  setl ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing.
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.
Qed.


Lemma k_deriv_sign_quad_Aneg_rpos : forall x₁ y₁ r,
    forall (Aneg : 2*r - y₁ < 0)
           (R0ltr : 0 < r)
           (phase :  straight r 0 0 0 x₁ y₁)
           z (zrng : -PI < z < PI),
      ((atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z/2 <
       atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) ->
             sign (κ' x₁ y₁ r z) = 1) /\
       (z/2 < atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) \/
        atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z/2 ->
        sign (κ' x₁ y₁ r z) = - 1)).
Proof.
  intros.

  generalize phase. intro Dnneg.
  unfold straight, Tcx, Tcy in Dnneg.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in Dnneg. clear id.
  rewrite cos_PI2, sin_PI2 in Dnneg.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in Dnneg. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in Dnneg. clear id.
  assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
  rewrite id in Dnneg. clear id.
  rewrite <- (Rplus_0_l r²) in Dnneg at 1.
  apply RIneq.Rplus_lt_reg_r, Rlt_le in Dnneg.
  
  assert (r <> 0) as rne0. intro; lra.
  assert (2 * r - y₁ <> 0) as trmyne0. intro. lra.
  repeat split; try intro c;
    (inversion_clear c as [c1 c2] || inversion_clear c as [c1 | c2]).
  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase ).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_1. reflexivity.
  setl (r*0). apply Rmult_lt_compat_l; [assumption|].
  setr (- (2 * r - y₁) *
  - ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
     (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  assumption.
  setl (- (2*r-y₁)*0). apply Rmult_lt_compat_l; [lra|].
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  fieldrewrite (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))
               (- ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)
                       - (tan (z / 2)))).
  assumption.
  setl (- ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
           ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2)))).
  assumption.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setl ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing. 
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setl (tan (z/2)).
  rewrite <- atan_right_inv.
  apply tan_increasing. inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.

  assert (z / 2 < atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
    as c2.
  apply (Rlt_le_trans _ (atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  assumption.
  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sp.
  inversion_clear sp as [R0eqs | R0lts]. left.
  apply atan_increasing.
  apply (Rplus_lt_reg_r (-(x₁/(2 * r - y₁)))).
  setr ((sqrt (x₁² - (2 * r - y₁) * y₁) / - (2 * r - y₁))). assumption.
  setl (-((sqrt (x₁² - (2 * r - y₁) * y₁)) / - (2 * r - y₁))). assumption.
  apply pos_opp_lt.
  apply (Rmult_lt_reg_l (-(2 * r - y₁))). lra. setl 0.
  setr (sqrt (x₁² - (2 * r - y₁) * y₁)). assumption. assumption.
  right. rewrite <- R0lts.
  fieldrewrite (x₁ - 0) (x₁ + 0). reflexivity.

  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase ).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_m1. reflexivity.
  setr (r*0). apply Rmult_lt_compat_l; [assumption|].
  setl (- (2 * r - y₁) *
          -((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
            (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  assumption.
  setr (- (2*r-y₁)*0). apply Rmult_lt_compat_l; [lra|].
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  setr (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2)) *
        ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2))).
  assumption.
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))). assumption.
  setl (tan (z/2)).
  rewrite <- (atan_right_inv).
  apply tan_increasing. inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setl (tan (z/2)). 
  rewrite <- (atan_right_inv).
  apply tan_increasing.  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.

  assert (atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z / 2)
    as c1.
  apply (Rle_lt_trans _ (atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sp.
  inversion_clear sp as [R0eqs | R0lts]. left.
  apply atan_increasing.
  apply (Rplus_lt_reg_r (-(x₁/(2 * r - y₁)))).
  setr ((sqrt (x₁² - (2 * r - y₁) * y₁) / - (2 * r - y₁))). assumption.
  setl (-(sqrt (x₁² - (2 * r - y₁) * y₁) / - (2 * r - y₁))). assumption.
  apply pos_opp_lt.
  apply (Rmult_lt_reg_l (- (2 * r - y₁))). lra. setl 0.
  setr (sqrt (x₁² - (2 * r - y₁) * y₁)). assumption. assumption.
  right. rewrite <- R0lts.
  fieldrewrite (x₁ - 0) (x₁ + 0). reflexivity.
  assumption.

  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase ).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_m1. reflexivity.
  setr (r*0). apply Rmult_lt_compat_l; [assumption|].
  setl (- (2 * r - y₁) *
          -((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
            (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  assumption.
  setr (- (2*r-y₁)*0). apply Rmult_lt_compat_l; [lra|].
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setl (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing.
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.

  apply (Rplus_lt_reg_r (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  setl ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing.
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.
Qed.

Lemma k_deriv_sign_quad_Aneg_rneg : forall x₁ y₁ r,
    forall (Aneg : 2*r - y₁ < 0)
           (rlt0 : r < 0)
           (phase :  straight r 0 0 0 x₁ y₁)           
           z (zrng : -PI < z < PI),
      ((atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z/2 <
        atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) ->
             sign (κ' x₁ y₁ r z) = - 1) /\
       (z/2 < atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) \/
        atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z/2 ->
        sign (κ' x₁ y₁ r z) = 1)).
Proof.
  intros.

  generalize phase. intro Dnneg.
  unfold straight, Tcx, Tcy in Dnneg.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in Dnneg. clear id.
  rewrite cos_PI2, sin_PI2 in Dnneg.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in Dnneg. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in Dnneg. clear id.
  assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
  rewrite id in Dnneg. clear id.
  rewrite <- (Rplus_0_l r²) in Dnneg at 1.
  apply RIneq.Rplus_lt_reg_r, Rlt_le in Dnneg.
  
  assert (r <> 0) as rne0. intro; lra.
  assert (2 * r - y₁ <> 0) as trmyne0. intro. lra.
  repeat split; try intro c;
    (inversion_clear c as [c1 c2] || inversion_clear c as [c1 | c2]).
  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase ).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_m1. reflexivity.
  rewrite <- (Ropp_involutive r) at 1.
  setl (- (- r * ((2 * r - y₁) *
   ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
    (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))))).
  assumption.
  setr (-0).
  apply Ropp_lt_contravar.
  setl (-r*0).
  apply Rmult_lt_compat_l; [lra|].
  setr (- (2 * r - y₁) *
  - ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
     (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  assumption.
  setl (- (2*r-y₁)*0). apply Rmult_lt_compat_l; [lra|].
  setr (((((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2))) *
          ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))).
  assumption.
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setl (tan (z/2)).
  rewrite <- atan_right_inv.
  apply tan_increasing. inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  apply (Rplus_lt_reg_r ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setl ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing. 
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.

  assert (z / 2 < atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
    as c2.
  apply (Rlt_le_trans _ (atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  assumption.
  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sp.
  inversion_clear sp as [R0eqs | R0lts]. left.
  apply atan_increasing.
  apply (Rplus_lt_reg_r (-(x₁/(2 * r - y₁)))).
  setr ((sqrt (x₁² - (2 * r - y₁) * y₁) / - (2 * r - y₁))). assumption.
  setl (-((sqrt (x₁² - (2 * r - y₁) * y₁)) / - (2 * r - y₁))). assumption.
  apply pos_opp_lt.
  apply (Rmult_lt_reg_l (-(2 * r - y₁))). lra. setl 0.
  setr (sqrt (x₁² - (2 * r - y₁) * y₁)). assumption. assumption.
  right. rewrite <- R0lts.
  fieldrewrite (x₁ - 0) (x₁ + 0). reflexivity.

  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase ).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_1. reflexivity.
  rewrite <- (Ropp_involutive r) at 1.
  setr (- r *
        (- (2 * r - y₁) *
          ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
           (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))).
  assumption.
  setl (-r*0). apply Rmult_lt_compat_l; [lra|].
  setl (- (2*r-y₁)*0). apply Rmult_lt_compat_l; [lra|].
  setr (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2)) *
        ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁) - tan (z / 2))).
  assumption.
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))). assumption.
  setl (tan (z/2)).
  rewrite <- (atan_right_inv).
  apply tan_increasing. inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  apply (Rplus_lt_reg_r (tan (z/2))).
  setr ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setl (tan (z/2)). 
  rewrite <- (atan_right_inv).
  apply tan_increasing.  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr z. assumption.
  assumption.
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.

  assert (atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) < z / 2)
    as c1.
  apply (Rle_lt_trans _ (atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sp.
  inversion_clear sp as [R0eqs | R0lts]. left.
  apply atan_increasing.
  apply (Rplus_lt_reg_r (-(x₁/(2 * r - y₁)))).
  setl (- (sqrt (x₁² - (2 * r - y₁) * y₁) / - (2 * r - y₁))). assumption.
  setr ((sqrt (x₁² - (2 * r - y₁) * y₁)) / - (2 * r - y₁)). assumption.
  apply pos_opp_lt.
  apply (Rmult_lt_reg_l (-(2 * r - y₁))). lra. setl 0.
  setr (sqrt (x₁² - (2 * r - y₁) * y₁)). assumption. assumption.
  right. rewrite <- R0lts.
  fieldrewrite (x₁ - 0) (x₁ + 0). reflexivity.
  assumption.

  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase ).
  rewrite (factor_quad _ _ _ _ trmyne0); [| assumption].
  rewrite sign_eq_1. reflexivity.
  rewrite <- (Ropp_involutive r) at 1.
  setr (- r *
        (-(2 * r - y₁) *
          ((tan (z / 2) - (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) *
           (tan (z / 2) - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))).
  assumption.
  setl (-r*0). apply Rmult_lt_compat_l; [lra|].
  setl (-(2*r-y₁)*0). apply Rmult_lt_compat_l; [lra|].
  apply Rmult_lt_0_compat.
  apply (Rplus_lt_reg_r ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  setl (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing.
  specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.

  apply (Rplus_lt_reg_r (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
  setl ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)). assumption.
  setr (tan (z/2)). assumption.
  rewrite <- (atan_right_inv ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  apply tan_increasing.
  specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))))
    as [abl abu]. assumption.
  assumption.
  inversion_clear zrng as [zlb zub]. 
  apply (Rmult_lt_reg_r 2). lra. setr (PI). setl z. assumption.
Qed.

Lemma k2k3rel : forall x y r θ,
    ~ ( x - r * sin θ = 0 /\ y - r * (1 - cos θ) = 0) ->
    exists z, κ₂ x y r θ = κ₃ x y r θ + 2 * IZR z * PI.
Proof.
  intros *. intro cnd.
  unfold κ₂,κ₃.
  specialize (atan3_atan2_eqv _ _ cnd) as [k atdf].
  exists k.
  rewrite atdf. reflexivity.
Qed.


Lemma k2_even_deriv_0 :
  forall θ x y r (rne0 : r<> 0)
         (k2vale : exists (n:Z), κ₂ x y r θ = θ + IZR (2 * n) * PI)
         (phase : straight r 0 0 0 x y),
    κ' x y r θ = 0.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [l [slb sub]].
  set (p := θ + IZR l * (2*PI)) in *.
  assert (-PI < p <= PI) as zrng.
  split. setl (- (2*PI)/2). assumption.
  setr (2*PI/2). assumption.

  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ l) in k2def.
  assert (θ + 2 * IZR l * PI = θ + IZR l * (2 * PI)) as id. field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n) * PI =
          (θ + IZR l * (2 * PI)) + IZR (2 * (n-l)) * PI) as id.
  assert (IZR l * (2 * PI) = IZR (2*l) * PI) as id2.
  rewrite mult_IZR. field.
  rewrite id2. clear id2.
  fieldrewrite (θ + IZR (2 * l) * PI + IZR (2 * (n - l)) * PI)
               (θ + (IZR (2 * l) + IZR (2 * (n - l))) * PI).
  rewrite <- plus_IZR.
  assert ((2 * l + (2 * (n - l))) = 2 * n)%Z as id3. omega.
  rewrite id3. clear id3. reflexivity.
  rewrite id in k2def. clear id.
  change (κ₂ x y r p = p + IZR (2 * (n-l)) * PI) in k2def.
  clear slb sub.

  assert (exists q : Z, κ₂ x y r p = p + IZR q * PI) as k2defp.
  exists (2* (n-l))%Z. assumption.

  rewrite <- (k_extrema_vals _ _ _ _ zrng rne0
                             (str_noton _ _ _ phase p)) in k2defp.
  unfold p in k2defp.
  assert (θ + IZR l * (2 * PI) = θ + 2 * IZR l * PI) as id.
  field. rewrite id in k2defp. clear id.
  rewrite <- (k'_periodic _ _ _ l) in k2defp.
  assumption.
Qed.



Lemma k2_odd_deriv_0 :
  forall θ x y r (rne0 : r<> 0)
         (k2vale : exists (n:Z), κ₂ x y r θ = θ + IZR (2 * n + 1) * PI)
         (phase : straight r 0 0 0 x y),
    κ' x y r θ = 0.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [l [slb sub]].
  set (p := θ + IZR l * (2*PI)) in *.
  assert (-PI < p <= PI) as zrng.
  split. setl (- (2*PI)/2). assumption.
  setr (2*PI/2). assumption.

  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ l) in k2def.
  assert (θ + 2 * IZR l * PI = θ + IZR l * (2 * PI)) as id. field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n + 1) * PI =
          (θ + IZR l * (2 * PI)) + IZR (2 * (n-l) + 1) * PI) as id.
  assert (IZR l * (2 * PI) = IZR (2*l) * PI) as id2.
  rewrite mult_IZR. field.
  rewrite id2. clear id2.
  fieldrewrite (θ + IZR (2 * l) * PI + IZR (2 * (n - l) + 1) * PI)
               (θ + (IZR (2 * l) + IZR (2 * (n - l) + 1)) * PI).
  rewrite <- plus_IZR.
  assert ((2 * l + (2 * (n - l) + 1)) = 2 * n + 1)%Z as id3. omega.
  rewrite id3. clear id3. reflexivity.
  rewrite id in k2def. clear id.
  change (κ₂ x y r p = p + IZR (2 * (n-l) + 1) * PI) in k2def.
  clear slb sub.

  assert (exists q : Z, κ₂ x y r p = p + IZR q * PI) as k2defp.
  exists (2* (n-l) + 1)%Z. assumption.

  rewrite <- (k_extrema_vals _ _ _ _ zrng rne0
                             (str_noton _ _ _ phase p)) in k2defp.
  unfold p in k2defp.
  assert (θ + IZR l * (2 * PI) = θ + 2 * IZR l * PI) as id.
  field. rewrite id in k2defp. clear id.
  rewrite <- (k'_periodic _ _ _ l) in k2defp.
  assumption.
Qed.


Lemma k2_symmetry : forall x₁ y₁ r θ,
    ~ (x₁ - r * sin θ <= 0 /\ y₁ - r * (1 - cos θ) = 0) ->
    κ₂ x₁ y₁ r θ = - (κ₂ x₁ (-y₁) (-r) (-θ)).
Proof.
  intros.
  unfold κ₂.
  rewrite cos_neg, sin_neg.
  fieldrewrite (- y₁ - - r * (1 - cos θ)) (- (y₁ - r * (1 - cos θ))).
  fieldrewrite (x₁ - - r * - sin θ) (x₁ - r * sin θ).
  apply atan2_symmetry; assumption.
Qed.


Lemma k2_continuity :
  forall x₁ y₁ r (rne0 : r <> 0)
         (cond : forall θ,
             ~ (x₁ - r * sin θ <= 0 /\
                y₁ - r * (1 - cos θ) = 0)),
    continuity (κ₂ x₁ y₁ r).
Proof.
  intros.
  specialize (k_is_derive_atan2 x₁ y₁ r) as k2id.
  assert (forall x : R, is_derive (κ₂ x₁ y₁ r) x (κ' x₁ y₁ r x)) as kd.
  intro.
  eapply k2id; eauto.
  clear k2id rne0 cond.
  apply derivable_continuous.
  unfold derivable. intro.
  specialize (kd x).
  apply ex_derive_Reals_0.
  unfold ex_derive.
  exists (κ' x₁ y₁ r x). assumption.
Qed.

Lemma k3_continuity :
  forall x₁ y₁ r (rne0 : r <> 0)
         (cond : forall θ,
             ~ (0 <= x₁ - r * sin θ /\
                y₁ - r * (1 - cos θ) = 0)),
    continuity (κ₃ x₁ y₁ r).
Proof.
  intros.
  specialize (k_is_derive_atan3 x₁ y₁ r) as k3id.
  assert (forall x : R, is_derive (κ₃ x₁ y₁ r) x (κ' x₁ y₁ r x)) as kd.
  intro.
  eapply k3id; eauto.
  clear k3id rne0 cond.
  apply derivable_continuous.
  unfold derivable. intro.
  specialize (kd x).
  apply ex_derive_Reals_0.
  unfold ex_derive.
  exists (κ' x₁ y₁ r x). assumption.
Qed.


Lemma IVT_gen_strict :
  forall (f : R -> R) (a b y : R),
    continuity f ->
    Rmin (f a) (f b) < y < Rmax (f a) (f b) ->
    {x : R | Rmin a b < x < Rmax a b /\ f x = y}.
Proof.
  intros *. intros cf yrng.
  assert (Rmin (f a) (f b) <= y <= Rmax (f a) (f b)) as yrng2. {
    destruct yrng; split; left; assumption. }
  
  specialize (IVT_gen f a b y cf yrng2) as [ x [[xl xu] fx]].
  unfold Rmin,Rmax in *.
  destruct (Rle_dec (f a) (f b)) as [falefb |fagtfb];
    destruct (Rle_dec a b) as [aleb | ageb].
  
  + exists x.
    inversion_clear aleb as [altb |aeqb] ; [|subst; destruct yrng; lra].
    destruct xl as [altx |aeqx]. destruct xu as [xltb |xeqb].
    split; [split; assumption| assumption].
    exfalso.
    rewrite xeqb in fx. rewrite <- fx in yrng.
    inversion_clear yrng as [faltfb fbltfb].
    clear - fbltfb. lra.
    exfalso.
    rewrite <- aeqx in fx.
    rewrite <- fx in yrng.
    inversion_clear yrng as [faltfa faltfb].
    clear - faltfa. lra.

  + exists x. apply Rnot_le_lt in ageb.
    destruct xl as [altx |aeqx]. destruct xu as [xltb |xeqb].
    split; [split; assumption| assumption].
    exfalso.
    rewrite xeqb in fx. rewrite <- fx in yrng.
    inversion_clear yrng as [faltfb fbltfb].
    clear - faltfb. lra.
    exfalso.
    rewrite <- aeqx in fx.
    rewrite <- fx in yrng.
    inversion_clear yrng as [faltfa faltfb].
    clear - faltfb. lra.

  + exists x. apply Rnot_le_lt in fagtfb.
    inversion_clear aleb as [altb |aeqb] ; [|subst; destruct yrng; lra].
    destruct xl as [altx |aeqx]. destruct xu as [xltb |xeqb].
    split; [split; assumption| assumption].
    exfalso.
    rewrite xeqb in fx. rewrite <- fx in yrng.
    inversion_clear yrng as [faltfb fbltfb].
    clear - faltfb. lra.
    exfalso.
    rewrite <- aeqx in fx.
    rewrite <- fx in yrng.
    inversion_clear yrng as [faltfa faltfb].
    clear - faltfb. lra.

  + exists x. apply Rnot_le_lt in fagtfb. apply Rnot_le_lt in ageb.
    destruct xl as [altx |aeqx]. destruct xu as [xltb |xeqb].
    split; [split; assumption| assumption].
    exfalso.
    rewrite xeqb in fx. rewrite <- fx in yrng.
    inversion_clear yrng as [faltfb fbltfb].
    clear - fbltfb. lra.
    exfalso.
    rewrite <- aeqx in fx.
    rewrite <- fx in yrng.
    inversion_clear yrng as [faltfa faltfb].
    clear - faltfa. lra.
Qed.

Lemma root_ordering_Q1top:
  forall x₁ y₁ r
         (rgt0 : 0 < r)
         (top : 2 * r - y₁ < 0 )
         (rt : 0 <= x₁)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in 
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) in
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) + 2 * IZR 1 * PI in
    θ1 < θmax < θ2 /\ 0 < θ1 < PI  /\ PI < θ2 < 2*PI. (* 3*PI/2 *)
Proof.
  intros.
  
  specialize PI_RGT_0 as pirgt0.
  assert (2*PI >0) as tpigt0. lra.
  
  assert (0 < y₁) as y1gt0. lra.


  assert (0 < θ1 < PI) as [t1lb t1ub]. {

    assert (x₁² < x₁² - (2 * r - y₁) * y₁) as inq.
    apply (Rplus_lt_reg_r (-x₁²)).
    setl 0. setr (- (2 * r - y₁) * y₁).
    apply Rmult_lt_0_compat; lra.

    assert ((x₁ - Q) < 0) as xpos. {
    apply (Rplus_lt_reg_r Q). setr Q. setl x₁.
    unfold Q.
    rewrite <- (sqrt_Rsqr x₁) at 1; [|assumption].
    apply sqrt_lt_1.
    apply Rle_0_sqr.
    left. apply (Rle_lt_trans _ (x₁²)).
    apply Rle_0_sqr. assumption.
    assumption. }
    clear inq.
    assert (0 < ((x₁ - Q) / (2 * r - y₁))) as argpos.
    fieldrewrite ((x₁ - Q) / (2 * r - y₁)) (- (x₁ - Q) * / - (2 * r - y₁)).
    intro; lra.
    apply Rmult_lt_0_compat. lra.
    apply Rinv_0_lt_compat. lra.
    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.

    specialize (atan_bound ((x₁ - Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atub; [|lra].
    unfold θ1.
    split. lra.
    fieldrewrite (PI) (2 * (PI/2)).
    assumption. }

    assert (PI < θ2 < 2*PI) as [t2lb t2ub]. {

    assert (x₁² < x₁² - (2 * r - y₁) * y₁) as inq.
    apply (Rplus_lt_reg_r (-x₁²)).
    setl 0. setr (- (2 * r - y₁) * y₁).
    apply Rmult_lt_0_compat; lra.

    assert (0 < x₁ + Q) as xpos. {
      apply Rplus_le_lt_0_compat. assumption.
      unfold Q.
      apply (Rle_lt_trans _ (sqrt (x₁²))).
      apply sqrt_pos.
      apply sqrt_lt_1.
      apply Rle_0_sqr.
      apply (Rle_trans _ (x₁²)).
      apply Rle_0_sqr.
      left.
      assumption.
      assumption.
    }
      
    clear inq.
    assert (((x₁ + Q) / (2 * r - y₁)) < 0) as argneg.
    apply (Rmult_lt_reg_r (- ((2 * r - y₁)))). lra.
    setl (- (x₁ + Q)). intro ; lra. setr 0. lra.
    apply atan_increasing in argneg.
    rewrite atan_0 in argneg.
    apply (Rmult_lt_compat_l 2) in argneg; [|lra].
    rewrite Rmult_0_r in argneg.
    apply (Rplus_lt_compat_r (2 * IZR 1 * PI)) in argneg.
    rewrite Rplus_0_l in argneg.
    rewrite Rmult_assoc in argneg at 2.
    rewrite Rmult_1_l in argneg.
    
    specialize (atan_bound ((x₁ + Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atlb; [|lra].
    apply (Rplus_lt_compat_r (2 * IZR 1 * PI)) in atlb.
    assert (2 * (- PI / 2) + 2 * 1 * PI = PI) as id. field.
    rewrite id in atlb. clear id.

    unfold θ2.
    split; assumption.
  }

  rename rt into rt'.
  destruct rt' as [rt |re].
  
  assert (0 < θmax < PI) as [tmlb tbub]. {
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    specialize (atan2Q1 _ _ rt y1gt0) as at2rng.
    inversion_clear at2rng as [lb ub].
    apply (Rmult_lt_compat_l 2) in lb; [|lra].
    apply (Rmult_lt_compat_l 2) in ub; [|lra].
    assert (2 * (PI / 2) = PI) as id. field. rewrite id in *. clear id.
    split; lra.
  }

  specialize (k_is_derive_atan2 x₁ y₁ r) as k2id.
  assert (r <> 0) as rne0. intro; lra.
  assert (forall θ,
             ~ (x₁ - r * sin θ <= 0 /\
                y₁ - r * (1 - cos θ) = 0)) as cond. {
  intros. intros [xc yc].
  assert (y₁ = r * (1 - cos θ)) as y1def.
  apply (Rplus_eq_reg_r (- r * (1 - cos θ))). setr 0. rewrite <- yc. field.
  rewrite y1def in top.
  specialize (COS_bound θ) as [clb cub].
  assert ((1 - cos θ) <= 2) as le2. lra.
  apply (Rmult_le_compat_l r) in le2; [|lra].
  rewrite (Rmult_comm _ 2) in le2.
  apply Ropp_le_contravar in le2.
  repeat rewrite Ropp_mult_distr_l in le2.
  apply (Rplus_le_compat_l (2*r)) in le2.
  assert (2 * r + - r * (1 - cos θ) =
          2 * r - r * (1 - cos θ)) as id. field. rewrite id in le2. clear id.
  assert (2 * r + - (2) * r = 0) as id. field. rewrite id in le2. clear id.
  clear - top le2. lra. }
  assert (forall x : R, is_derive (κ₂ x₁ y₁ r) x (κ' x₁ y₁ r x)) as kd.
  intro.
  eapply k2id; eauto.
  specialize (k2_continuity _ _ _ rne0 cond) as k2c.
  clear cond rne0 k2id.

  assert (θ1 < θ2) as t2ltt2. {
    unfold θ1,θ2.
    specialize (atan_bound ((x₁ - Q) / (2 * r - y₁))) as [atbl1 atbu1].
    specialize (atan_bound ((x₁ + Q) / (2 * r - y₁))) as [atbl2 atbu2].
    apply (Rmult_lt_compat_r 2) in atbl1; [|lra].
    apply (Rmult_lt_compat_r 2) in atbu1; [|lra].
    apply (Rmult_lt_compat_r 2) in atbl2; [|lra].
    apply (Rmult_lt_compat_r 2) in atbu2; [|lra].
    assert (- PI / 2 * 2 = -PI) as id. field. rewrite id in *. clear id.
    assert (PI / 2 * 2 = PI) as id. field. rewrite id in *. clear id.
    lra. }

  assert ((κ₂ x₁ y₁ r PI) < (κ₂ x₁ y₁ r θ1)) as kord. {
    set (f := (κ₂ x₁ y₁ r)) in *.
    eapply (derive_decreasing_interv θ1 PI f); try lra.
    intros.
    assert (derivable_pt f t) as dpft.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r t). apply kd.
    rewrite Derive_Reals.
    rewrite (is_derive_unique _ _ _ (kd t)).
    apply signeqm1_eqv.

    apply k_deriv_sign_quad_Aneg_rpos; auto.
    inversion_clear H as [tlb tub].
    split; try assumption. lra.
    right.
    apply (Rmult_lt_reg_l 2); [lra|]. setr t.
    destruct H.
    assumption.

    Unshelve.
    unfold derivable. intros.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r x). apply kd.
  }

  
  assert (Rmin (κ₂ x₁ y₁ r θ1) (κ₂ x₁ y₁ r PI) < θmax/2 <
          Rmax (κ₂ x₁ y₁ r θ1) (κ₂ x₁ y₁ r PI)) as inq. {
    rewrite Rmin_right, Rmax_left; try (left; assumption).
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).
    split.
    + unfold κ₂.
      rewrite cos_PI, sin_PI.
      fieldrewrite (y₁ - r * (1 - -1)) (y₁ - 2*r).
      fieldrewrite (x₁ - r * 0) (x₁).
      assert (0 < y₁ - 2 * r) as retop. lra.
      rewrite atan2_atan_Q1; try lra.
      rewrite atan2_atan_Q1; try lra.
      apply atan_increasing.
      apply (Rmult_lt_reg_r x₁); try assumption.
      setr y₁. intro; lra.
      setl (y₁ - 2 * r). intro ;lra. lra.

    + assert (y₁ = y₁ - r * (1 - 1)) as id. field. rewrite id at 1. clear id.
      assert (x₁ = x₁ - r * 0) as id. field. rewrite id at 1. clear id.
      rewrite <- sin_0. rewrite <- cos_0 at 2. 
      change (κ₂ x₁ y₁ r 0 < κ₂ x₁ y₁ r θ1).
      
      set (f := (κ₂ x₁ y₁ r)) in *. 
      eapply (derive_increasing_interv 0 θ1 f); try lra.
      intros.
      assert (derivable_pt f t) as dpft.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r t). apply kd.
      rewrite Derive_Reals.
      rewrite (is_derive_unique _ _ _ (kd t)).
      apply signeq1_eqv.

      apply k_deriv_sign_quad_Aneg_rpos; auto.
      inversion_clear H as [tlb tub].
      split; try assumption. lra.
      apply (Rlt_trans _ θ1); assumption. 
      split.
      ++ apply (Rmult_lt_reg_l 2); [lra|]. setr t.
         rewrite <- (Rplus_0_r (2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                            / (2 * r - y₁)))).
         rewrite <- (Rplus_opp_r (2*1*PI)).
         rewrite <- Rplus_assoc.
         change (θ2 - (2*1*PI)< t).
         destruct H.
         apply (Rlt_trans _ 0); lra.
      ++ apply (Rmult_lt_reg_l 2); [lra|]. setl t.
         destruct H.
         assumption.

         Unshelve.
         unfold derivable. intros.
         apply ex_derive_Reals_0.
         unfold ex_derive.
         exists (κ' x₁ y₁ r x). apply kd.
  }

  specialize (IVT_gen_strict _ _ _ _ k2c inq) as [x [bnd def]].
  rewrite Rmin_left in bnd; [|left; assumption].
  rewrite Rmax_right in bnd; [|left; assumption].
  rewrite k_center_val in def.
  assert (x = θmax) as xeq.
  apply (Rmult_eq_reg_r (/2)). assumption.
  apply Rinv_neq_0_compat. discrR.
  subst. destruct bnd as [lb ub].
  split.
  + split; try assumption.
    apply (Rlt_trans _ PI); assumption.
  + split; split; assumption.
  + destruct bnd. split.
  
    apply Rmult_lt_0_compat; [assumption|lra].
    rewrite Rabs_right. apply Rmult_lt_compat_l; try assumption.
    lra. left. assumption.

  + intro; lra.
  + assert (0 < x) as zltx. inversion_clear bnd. lra.
    assert (x < PI) as xltPI. inversion_clear bnd. assumption.
    intro.
    assert (- PI < x <= PI) as xrng. split; lra.
    apply sinθeq0 in H; try assumption.
    inversion_clear H as [xeq0|xeqPI].
    rewrite xeq0 in zltx. clear - zltx. lra.
    rewrite xeqPI in xltPI. clear - xltPI. lra.
  + apply Rmult_lt_0_compat; assumption.
  + assert (0 < x) as zltx. inversion_clear bnd. lra.
    assumption.
  + rewrite def. unfold θmax. reflexivity.

  + unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    rewrite <- re in *.
    rewrite atan2_PI2. 

    repeat split; lra.
    assumption.
Qed.


(*
In these lemmas, sign r = sign θ1 = sign θ2 reflecting the direction
of the turn (+ clockwise, - ccw). θ1,θ2 are defined so their signs are
consistent with r. sign θmax = sign y₁ because it is just 
2*atan2 y1 x1.
If sign θmax <> sign θ1 we need to correct θmax in the inequality
so that the sign is meaningful and matches r.

for root_ordering_Q4top_rneg 
-2*PI < θ2 < -PI maybe could be -3*PI/2 < θ2 < -PI
which means 
for root_ordering_Q1top
PI < θ2 < 2*PI maybe could be PI < θ2 < 3*PI/2
todo?
*)

Lemma root_ordering_Q4top_rneg:
  forall x₁ y₁ r
         (rgt0 : r < 0)
         (top : 0 < 2 * r - y₁)
         (rt : 0 <= x₁)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in 
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) in
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) - 2 * IZR 1 * PI in
    θ2 < θmax < θ1 /\ -PI < θ1 < 0  /\ -2*PI < θ2 < -PI.
Proof.
  intros.
  
  apply straight_symmetry in phase.
  assert (0 < (-r)) as rgt0';[ lra|].
  assert (2*(-r) - (- y₁) <0) as top'; [lra|].
  rewrite Ropp_0 in phase.

  assert (θmax = - calcθ₁ 0 0 0 x₁ (-y₁)) as tmid.
  unfold θmax, calcθ₁ in *. clear θmax.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert (- (x₁ - 0) * sin 0 + (- y₁ - 0) * cos 0 = - y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (- y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  rewrite atan2_symmetry. lra.
  intro sc. destruct sc as [scx scy]. lra.
  rewrite tmid.
  set (θmax' := calcθ₁ 0 0 0 x₁ (- y₁)) in *.

  set (Q' := sqrt (x₁² - (2 * (-r) - (-y₁)) * (-y₁))) in *.
  assert (Q' = Q) as Q1rel;
    [ unfold Q, Q';
      assert ((x₁² - (2 * - r - - y₁) * - y₁) = (x₁² - (2 * r - y₁) * y₁)) as argeq;
      [lra|]; rewrite argeq; reflexivity|].

  set (θ1' := 2 * atan ((x₁ - Q') / (2 * (-r) - (-y₁)))).
  assert (θ1 = -θ1') as t1rel. unfold θ1, θ1'.
  rewrite Q1rel.
  assert ((x₁ - Q) / (2 * - r - - y₁) = (- ((x₁ - Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  set (θ2' := 2 * atan ((x₁ + Q') / (2 * (-r) - (-y₁))) + 2 * 1 * PI).
  assert (θ2 = -θ2') as t2rel. unfold θ2, θ2'.
  rewrite Q1rel.
  assert ((x₁ + Q) / (2 * - r - - y₁) = (- ((x₁ + Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  rewrite t2rel, t1rel.
  enough (θ1' < θmax' < θ2' /\ 0 < θ1' < PI /\ PI < θ2' < 2* PI)
    as [[tmordlb tmordub] [[t1ordlb t1ordub] [t2ordlb t2ordub]]].
  lra.
  apply root_ordering_Q1top; assumption.
Qed.


Lemma root_ordering_Q1arm:
  forall x₁ y₁ r
         (rgt0 : 0 < r)
         (bot : 0 = 2 * r - y₁)
         (Q1 : 0 < y₁)
         (rt : 0 < x₁)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let θ1 := 2 * atan (y₁/(2 * x₁)) in
    let θ2 := PI in
    θ1 < θmax < θ2 /\ 0 < θ1 < PI.
Proof.
  intros.

  specialize PI_RGT_0 as pirgt0.
  assert (2*PI >0) as tpigt0. lra.

  rename Q1 into y1gt0.

  assert (0 < θmax < PI) as [tmlb tbub]. {
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    specialize (atan2Q1 _ _ rt y1gt0) as at2rng.
    inversion_clear at2rng as [lb ub].
    apply (Rmult_lt_compat_l 2) in lb; [|lra].
    apply (Rmult_lt_compat_l 2) in ub; [|lra].
    assert (2 * (PI / 2) = PI) as id. field. rewrite id in *. clear id.
    split; lra.
  }

  
  assert (0 < θ1 < PI) as [t1lb t1ub]. {

    assert (0 < y₁/(2*x₁)) as xpos. {
      apply (Rmult_lt_reg_r (2*(x₁))). lra.
      setl 0. setr (y₁). intro. lra. lra.
    }
      
    apply atan_increasing in xpos.
    rewrite atan_0 in xpos.
    apply (Rmult_lt_compat_l 2) in xpos; [|lra]. 
    rewrite Rmult_0_r in xpos.
    
    specialize (atan_bound (y₁ / (2 * x₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atub; [|lra].
    assert (2 * (PI / 2) = PI) as id. field.
    rewrite id in atub. clear id atlb.

    unfold θ1.
    split; assumption.

  }


  specialize (k_is_derive_atan2 x₁ y₁ r) as k2id.
  assert (r <> 0) as rne0. intro; lra.
  assert (forall θ,
             ~ (x₁ - r * sin θ <= 0 /\
                y₁ - r * (1 - cos θ) = 0)) as cond. {
  intros. intros [xc yc].

  assert (y₁ = r * (1 - cos θ)) as y1def.
  apply (Rplus_eq_reg_r (- r * (1 - cos θ))). setr 0. rewrite <- yc. field.

  apply (straight_std_impl_ineq) in phase.

  assert (r² < r²) as r2ltr2.
  rewrite <- Rmult_1_r, <- (sin2_cos2 θ).
  setr ( (r *sin θ)² + (r * cos θ)²).
  apply (Rlt_le_trans _ (x₁² + (r *cos θ)²)).
  rewrite (Rsqr_neg (r * cos θ)).
  fieldrewrite (- (r * cos θ)) (r * (1 - cos θ) - r).
  rewrite <- y1def.
  assumption.
  apply (Rplus_le_reg_r (-(r * cos θ)²)).
  setl (x₁²). setr ((r * sin θ)²).
  apply Rsqr_le_abs_1.
  rewrite Rabs_right; [|lra].
  rewrite Rabs_right; [|lra].
  apply (Rplus_le_reg_r (-(r * sin θ))).
  setl (x₁ - (r * sin θ)). setr (0).
  assumption.
  lra.
  }

  assert (forall x : R, is_derive (κ₂ x₁ y₁ r) x (κ' x₁ y₁ r x)) as kd.
  intro.
  eapply k2id; eauto.
  specialize (k2_continuity _ _ _ rne0 cond) as k2c.
  clear cond rne0 k2id.

  assert (θ1 < θ2) as t2ltt2. {
    unfold θ1,θ2.
    apply (Rmult_lt_reg_l (/2)).
    apply Rinv_0_lt_compat. lra.
    repeat rewrite <- Rmult_assoc.
    fieldrewrite (/ 2 * 2) 1.
    repeat rewrite Rmult_1_l.
    setr (PI/2).
    apply atan_bound.
  }

  assert ((κ₂ x₁ y₁ r θ2) < (κ₂ x₁ y₁ r θ1)) as kord. {
    set (f := (κ₂ x₁ y₁ r)) in *.
    eapply (derive_decreasing_interv θ1 θ2 f); try lra.
    intros.
    assert (derivable_pt f t) as dpft.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r t). apply kd.
    rewrite Derive_Reals.
    rewrite (is_derive_unique _ _ _ (kd t)).
    apply signeqm1_eqv.

    specialize (k_deriv_sign_lin_rpos x₁ y₁ r t)as linrtsgn.
    assert (- PI < t < PI) as trng.
    inversion_clear H as [tlb tub]. unfold θ2 in tub. split; lra.
    assert (t <> 0) as tne0. lra.
    symmetry in bot.
    specialize (linrtsgn trng rgt0 phase  bot).
    inversion_clear linrtsgn as [x1gtp [x1gtn [x1eq0 [x1ltn x1ltp]]]].
    apply x1gtn.
    split; try assumption.
    inversion_clear H as [lb ub].
    unfold θ1 in lb. lra. 
  
    Unshelve.
    unfold derivable. intros.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r x). apply kd.
  }

  assert (Rmin (κ₂ x₁ y₁ r θ1) (κ₂ x₁ y₁ r θ2) < θmax/2 <
          Rmax (κ₂ x₁ y₁ r θ1) (κ₂ x₁ y₁ r θ2)) as tmrng. {
    rewrite Rmin_right, Rmax_left; try (left; assumption).
    split.

    + set (f := (κ₂ x₁ y₁ r)) in *.
        
      assert (f (-PI) < f 0) as gluerng2. {
        eapply (derive_increasing_interv (-PI) 0 f); try lra;
          try (split; lra).
        intros.
        assert (derivable_pt f t) as dpft.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        exists (κ' x₁ y₁ r t). apply kd.
        rewrite Derive_Reals.
        rewrite (is_derive_unique _ _ _ (kd t)).
        apply signeq1_eqv.

        specialize (k_deriv_sign_lin_rpos x₁ y₁ r t)as linrtsgn.
        assert (- PI < t < PI) as trng.
        inversion_clear H as [tlb tub]. unfold θ2 in tub. split; lra.
        assert (t <> 0) as tne0. lra.
        symmetry in bot.
        specialize (linrtsgn trng rgt0 phase  bot).
        inversion_clear linrtsgn as [x1gtp [x1gtn [x1eq0 [x1ltn x1ltp]]]].
        apply x1gtp.
        
        split; try assumption. 
        apply (Rmult_lt_reg_l 2). lra. setl t.
        apply (Rlt_trans _ 0); try assumption. lra. }

      assert (f (-PI) = f PI) as gluept. {
        unfold f.
        rewrite (k2_periodic _ _ _ 1%Z).
        fieldrewrite (- PI + 2 * 1 * PI) PI. reflexivity. }

      rewrite gluept in gluerng2. clear gluept.
      
      unfold θmax, calcθ₁. rewrite cos_0, sin_0.
      fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
      fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
      fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).

      assert (y₁ = y₁ - r * (1 - 1)) as id. field. rewrite id. clear id.
      assert (x₁ = x₁ - r * 0) as id. field. rewrite id. clear id.
      rewrite <- sin_0. rewrite <- cos_0 at 2.
      change (κ₂ x₁ y₁ r θ2 < κ₂ x₁ y₁ r 0).
      unfold f in *. unfold θ2. assumption.

      + unfold θmax, calcθ₁. rewrite cos_0, sin_0.
        fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
        fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
        fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).
        
        assert (y₁ = y₁ - r * (1 - 1)) as id. field. rewrite id at 1. clear id.
        assert (x₁ = x₁ - r * 0) as id. field. rewrite id at 1. clear id.
        rewrite <- sin_0. rewrite <- cos_0 at 2.
        change (κ₂ x₁ y₁ r 0< κ₂ x₁ y₁ r θ1).
        
        set (f := (κ₂ x₁ y₁ r)) in *. 
        eapply (derive_increasing_interv 0 θ1 f); try lra.
        intros.
        assert (derivable_pt f t) as dpft.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        exists (κ' x₁ y₁ r t). apply kd.
        rewrite Derive_Reals.
        rewrite (is_derive_unique _ _ _ (kd t)).
        apply signeq1_eqv.

        specialize (k_deriv_sign_lin_rpos x₁ y₁ r t)as linrtsgn.
        assert (- PI < t < PI) as trng.
        inversion_clear H as [tlb tub]. unfold θ2 in tub. split; lra.
        assert (t <> 0) as tne0. lra.
        symmetry in bot.
        specialize (linrtsgn trng rgt0 phase  bot).
        inversion_clear linrtsgn as [x1gtp [x1gtn [x1eq0 [x1ltn x1ltp]]]].
        apply x1gtp.

        inversion_clear H as [tlb tub].
        split; try assumption. unfold θ1 in tub. lra.

        Unshelve.
        unfold derivable. intros.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        exists (κ' x₁ y₁ r x). apply kd.
        unfold derivable. intros.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        exists (κ' x₁ y₁ r x). apply kd.
  }
  
  specialize (IVT_gen_strict _ _ _ _ k2c tmrng) as [x [bnd def]].
  rewrite Rmin_left in bnd; [|left; assumption].
  rewrite Rmax_right in bnd; [|left; assumption].
  rewrite k_center_val in def.
  assert (x = θmax) as xeq.
  apply (Rmult_eq_reg_r (/2)). assumption.
  apply Rinv_neq_0_compat. discrR.
  subst.

  split.
  + assumption.
  + split; assumption.
  + destruct bnd as [lb ub].

    split.
    apply Rmult_lt_0_compat; [assumption|lra].
    rewrite Rabs_right. apply Rmult_lt_compat_l; try assumption.
    unfold θ2 in ub. lra. left. assumption.
    
  + intro; lra.
  + assert (0 < x) as zltx. inversion_clear bnd. lra.
    assert (x < PI) as xltPI. inversion_clear bnd.
    unfold θ2 in H0. assumption.
    intro sinx0.
    assert (- PI < x <= PI) as xrng. split; lra.
    apply sinθeq0 in sinx0; try assumption.
    inversion_clear sinx0 as [xeq0|xeqPI].
    rewrite xeq0 in zltx. clear - zltx. lra.
    rewrite xeqPI in xltPI. clear - xltPI. lra.
  + apply Rmult_lt_0_compat; assumption.
  + assert (0 < x) as zltx. inversion_clear bnd. lra.
    assumption.
  + rewrite def. unfold θmax. reflexivity.
Qed.


Lemma root_ordering_Q4arm_rneg:
  forall x₁ y₁ r
         (rgt0 : r < 0)
         (bot : 0 = 2 * r - y₁)
         (Q1 : y₁ < 0)
         (rt : 0 < x₁)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let θ1 := 2 * atan (y₁/(2 * x₁)) in
    let θ2 := - PI in
    θ2 < θmax < θ1 /\ -PI < θ1 < 0.
Proof.
  intros.

  apply straight_symmetry in phase.
  assert (0 < (-r)) as rgt0';[ lra|].
  assert (0 = 2*(-r) - (- y₁)) as bot'; [lra|].
  rewrite Ropp_0 in phase.

  assert (θmax = - calcθ₁ 0 0 0 x₁ (-y₁)) as tmid.
  unfold θmax, calcθ₁ in *. clear θmax.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert (- (x₁ - 0) * sin 0 + (- y₁ - 0) * cos 0 = - y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (- y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  rewrite atan2_symmetry. lra.
  intro sc. destruct sc as [scx scy]. lra.
  rewrite tmid.
  set (θmax' := calcθ₁ 0 0 0 x₁ (- y₁)) in *.

  set (θ1' := 2 * atan ((- y₁) / (2 * x₁))).
  assert (θ1 = -θ1') as t1rel. unfold θ1, θ1'.
  assert ((- y₁ / (2 * x₁)) = (- (y₁ / (2 * x₁)))).
  field. intro; lra. rewrite H.
  rewrite atan_opp. field.

  set (θ2' := PI).
  assert (θ2 = -θ2') as t2rel. unfold θ2, θ2'. reflexivity.

  rewrite t2rel, t1rel.
  enough (θ1' < θmax' < θ2' /\ 0 < θ1' < θ2')
    as [[tmordlb tmordub] [t1ordlb t1ordub]].
  lra.
  eapply root_ordering_Q1arm; try eassumption.
  lra.
Qed.


Lemma root_ordering_Q1bot:
  forall x₁ y₁ r
         (rgt0 : 0 < r)
         (bot : 0 < 2 * r - y₁)
         (Q1 : 0 < y₁)
         (rt : 0 < x₁)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) in
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) in
    θ1 < θmax < θ2 /\ 0 < θ1 < PI /\ 0 < θ2 < PI.
Proof.
  intros.

  specialize PI_RGT_0 as pirgt0.
  assert (2*PI >0) as tpigt0. lra.

  rename Q1 into y1gt0.

  assert (0 < θmax < PI) as [tmlb tbub]. {
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    specialize (atan2Q1 _ _ rt y1gt0) as at2rng.
    inversion_clear at2rng as [lb ub].
    apply (Rmult_lt_compat_l 2) in lb; [|lra].
    apply (Rmult_lt_compat_l 2) in ub; [|lra].
    assert (2 * (PI / 2) = PI) as id. field. rewrite id in *. clear id.
    split; lra.
  }

  assert (x₁² - (2 * r - y₁) * y₁ < x₁²) as inq. {
  apply (Rplus_lt_reg_r (-x₁²)).
  setr 0. setl (- ((2 * r - y₁) * y₁)).
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar. 
  apply Rmult_lt_0_compat; lra. }

  assert (0 < x₁² - (2 * r - y₁) * y₁) as sqalb. {
  apply (Rplus_lt_reg_r (r²)).
  setl (r²). setr (x₁² + (y₁ - r)²).
  apply (straight_std_impl_ineq) in phase.
  assumption.
  }
  
  assert (0 < (x₁ - Q)) as xpos. {
    apply (Rplus_lt_reg_r Q). setl Q. setr x₁.
    unfold Q.
    rewrite <- (sqrt_Rsqr x₁) at 2; [|left; assumption].
    apply sqrt_lt_1; [|apply Rle_0_sqr|assumption].
    left.
    assumption. }
  
  assert (0 < θ1 < PI) as [t1lb t1ub]. {

    assert (0 < ((x₁ - Q) / (2 * r - y₁))) as argpos.
    apply (Rmult_lt_reg_r (2 * r - y₁)); [ assumption|].
    setl 0. setr (x₁ - Q).
    intro; lra. assumption.

    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.

    specialize (atan_bound ((x₁ - Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atub; [|lra].
    unfold θ1.
    split. lra.
    fieldrewrite (PI) (2 * (PI/2)).
    assumption. }

    assert (0 < x₁ + Q) as xppos. {
      apply Rplus_lt_le_0_compat. assumption.
      apply sqrt_pos.
    }

    assert (0 < θ2 < PI) as [t2lb t2ub]. {
      
    assert (0 < ((x₁ + Q) / (2 * r - y₁))) as argpos.
    apply (Rmult_lt_reg_r ((2 * r - y₁))). lra.
    setr (x₁ + Q). intro ; lra. setl 0. lra.
    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.
    
    specialize (atan_bound ((x₁ + Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atub; [|lra].
    assert (2 * ( PI / 2) =  PI) as id. field.
    rewrite id in atub. clear id.

    unfold θ2.
    split; assumption.
  }

  assert (0 <= x₁² - (2 * r - y₁) * y₁) as sqalb2; [left; assumption|].
  apply (sqrt_lt_1 _ _ (Rle_refl 0) sqalb2) in sqalb.
  rewrite sqrt_0 in sqalb. change (0 < Q) in sqalb.

  specialize (k_is_derive_atan2 x₁ y₁ r) as k2id.
  assert (r <> 0) as rne0. intro; lra.
  assert (forall θ,
             ~ (x₁ - r * sin θ <= 0 /\
                y₁ - r * (1 - cos θ) = 0)) as cond. {
  intros. intros [xc yc].

  assert (y₁ = r * (1 - cos θ)) as y1def.
  apply (Rplus_eq_reg_r (- r * (1 - cos θ))). setr 0. rewrite <- yc. field.

  apply (straight_std_impl_ineq) in phase.

  assert (r² < r²) as r2ltr2.
  rewrite <- Rmult_1_r, <- (sin2_cos2 θ).
  setr ( (r *sin θ)² + (r * cos θ)²).
  apply (Rlt_le_trans _ (x₁² + (r *cos θ)²)).
  rewrite (Rsqr_neg (r * cos θ)).
  fieldrewrite (- (r * cos θ)) (r * (1 - cos θ) - r).
  rewrite <- y1def.
  assumption.
  apply (Rplus_le_reg_r (-(r * cos θ)²)).
  setl (x₁²). setr ((r * sin θ)²).
  apply Rsqr_le_abs_1.
  rewrite Rabs_right; [|lra].
  rewrite Rabs_right; [|lra].
  apply (Rplus_le_reg_r (-(r * sin θ))).
  setl (x₁ - (r * sin θ)). setr (0).
  assumption.
  lra.
  }

  assert (forall x : R, is_derive (κ₂ x₁ y₁ r) x (κ' x₁ y₁ r x)) as kd.
  intro.
  eapply k2id; eauto.
  specialize (k2_continuity _ _ _ rne0 cond) as k2c.
  clear cond rne0 k2id.

  assert (θ1 < θ2) as t2ltt2. {
    unfold θ1,θ2.
    apply (Rmult_lt_reg_l (/2)).
    apply Rinv_0_lt_compat. lra.
    repeat rewrite <- Rmult_assoc.
    fieldrewrite (/ 2 * 2) 1.
    repeat rewrite Rmult_1_l.
    apply atan_increasing.
    apply (Rmult_lt_reg_l (2 * r - y₁)). assumption.
    apply (Rplus_lt_reg_r (-x₁)).
    setl (-Q). intro; lra. setr Q. intro; lra.
    lra.
  }

  assert ((κ₂ x₁ y₁ r θ2) < (κ₂ x₁ y₁ r θ1)) as kord. {
    set (f := (κ₂ x₁ y₁ r)) in *.
    eapply (derive_decreasing_interv θ1 θ2 f); try lra.
    intros.
    assert (derivable_pt f t) as dpft.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r t). apply kd.
    rewrite Derive_Reals.
    rewrite (is_derive_unique _ _ _ (kd t)).
    apply signeqm1_eqv.

    apply k_deriv_sign_quad_Apos_rpos; auto.
    inversion_clear H as [tlb tub].
    split; lra.
    inversion_clear H as [tlb tub].
    split.
    apply (Rmult_lt_reg_l 2); [lra|]. setr t.
    assumption.
    apply (Rmult_lt_reg_l 2); [lra|]. setl t.
    assumption.

    Unshelve.
    unfold derivable. intros.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r x). apply kd.
  }

  
  assert (Rmin (κ₂ x₁ y₁ r θ1) (κ₂ x₁ y₁ r θ2) < θmax/2 <
          Rmax (κ₂ x₁ y₁ r θ1) (κ₂ x₁ y₁ r θ2)) as tmrng. {
    rewrite Rmin_right, Rmax_left; try (left; assumption).
    split.

    + set (f := (κ₂ x₁ y₁ r)) in *.
      assert (f θ2 < f PI) as gluerng1. {
        eapply (derive_increasing_interv θ2 PI f); try lra;
          try (split; lra).
        intros.
        assert (derivable_pt f t) as dpft.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        exists (κ' x₁ y₁ r t). apply kd.
        rewrite Derive_Reals.
        rewrite (is_derive_unique _ _ _ (kd t)).
        apply signeq1_eqv.

        inversion_clear H as [tlb tub].
        apply k_deriv_sign_quad_Apos_rpos; auto.
        split; try assumption. lra.
        right.
        apply (Rmult_lt_reg_l 2). lra. setr (t).
        assumption. }
        
      assert (f (-PI) < f 0) as gluerng2. {
        eapply (derive_increasing_interv (-PI) 0 f); try lra;
          try (split; lra).
        intros.
        assert (derivable_pt f t) as dpft.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        exists (κ' x₁ y₁ r t). apply kd.
        rewrite Derive_Reals.
        rewrite (is_derive_unique _ _ _ (kd t)).
        apply signeq1_eqv.

        inversion_clear H as [tlb tub].
        apply k_deriv_sign_quad_Apos_rpos; auto.
        split; try assumption. lra.
        left.
        apply (Rmult_lt_reg_l 2). lra. setl t.
        apply (Rlt_trans _ 0); assumption. }

      assert (f (-PI) = f PI) as gluept. {
        unfold f.
        rewrite (k2_periodic _ _ _ 1%Z).
        fieldrewrite (- PI + 2 * 1 * PI) PI. reflexivity. }

      rewrite gluept in gluerng2. clear gluept.
      
      unfold θmax, calcθ₁. rewrite cos_0, sin_0.
      fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
      fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
      fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).

      assert (y₁ = y₁ - r * (1 - 1)) as id. field. rewrite id. clear id.
      assert (x₁ = x₁ - r * 0) as id. field. rewrite id. clear id.
      rewrite <- sin_0. rewrite <- cos_0 at 2.
      change (κ₂ x₁ y₁ r θ2 < κ₂ x₁ y₁ r 0).
      unfold f in *. lra.

      + unfold θmax, calcθ₁. rewrite cos_0, sin_0.
        fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
        fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
        fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).
        
        assert (y₁ = y₁ - r * (1 - 1)) as id. field. rewrite id at 1. clear id.
        assert (x₁ = x₁ - r * 0) as id. field. rewrite id at 1. clear id.
      rewrite <- sin_0. rewrite <- cos_0 at 2.
      change (κ₂ x₁ y₁ r 0< κ₂ x₁ y₁ r θ1).
      
      set (f := (κ₂ x₁ y₁ r)) in *. 
      eapply (derive_increasing_interv 0 θ1 f); try lra.
      intros.
      assert (derivable_pt f t) as dpft.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r t). apply kd.
      rewrite Derive_Reals.
      rewrite (is_derive_unique _ _ _ (kd t)).
      apply signeq1_eqv.

      apply k_deriv_sign_quad_Apos_rpos; auto.
      inversion_clear H as [tlb tub].
      split; try assumption. lra.
      apply (Rlt_trans _ θ1); assumption. 

      left.
      apply (Rmult_lt_reg_l 2). lra. setl t.
      destruct H.
      assumption.

            Unshelve.
      unfold derivable. intros.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r x). apply kd.
      unfold derivable. intros.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r x). apply kd.
      unfold derivable. intros.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r x). apply kd.

  }
  
  specialize (IVT_gen_strict _ _ _ _ k2c tmrng) as [x [bnd def]].
  rewrite Rmin_left in bnd; [|left; assumption].
  rewrite Rmax_right in bnd; [|left; assumption].
  rewrite k_center_val in def.
  assert (x = θmax) as xeq.
  apply (Rmult_eq_reg_r (/2)). assumption.
  apply Rinv_neq_0_compat. discrR.
  subst.

  split.
  + assumption.
  + split; split; assumption.
  + destruct bnd as [lb ub].

    split.
    apply Rmult_lt_0_compat; [assumption|lra].
    rewrite Rabs_right. apply Rmult_lt_compat_l; try assumption.
    lra. left. assumption.
    
  + intro; lra.
  + assert (0 < x) as zltx. inversion_clear bnd. lra.
    assert (x < PI) as xltPI. inversion_clear bnd. lra.
    intro sinx0.
    assert (- PI < x <= PI) as xrng. split; lra.
    apply sinθeq0 in sinx0; try assumption.
    inversion_clear sinx0 as [xeq0|xeqPI].
    rewrite xeq0 in zltx. clear - zltx. lra.
    rewrite xeqPI in xltPI. clear - xltPI. lra.
  + apply Rmult_lt_0_compat; assumption.
  + assert (0 < x) as zltx. inversion_clear bnd. lra.
    assumption.
  + rewrite def. unfold θmax. reflexivity.
Qed.


Lemma root_ordering_Q4bot_rneg:
  forall x₁ y₁ r
         (rgt0 : r < 0)
         (bot : 2 * r - y₁ < 0)
         (Q1 : y₁ < 0)
         (rt : 0 < x₁)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) in
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) in
    θ2 < θmax < θ1 /\ -PI < θ1 < 0 /\ -PI < θ2 < 0.
Proof.
  intros.

  apply straight_symmetry in phase.
  assert (0 < (-r)) as rgt0';[ lra|].
  assert (0 < 2*(-r) - (- y₁)) as top'; [lra|].
  rewrite Ropp_0 in phase.

  assert (θmax = - calcθ₁ 0 0 0 x₁ (-y₁)) as tmid.
  unfold θmax, calcθ₁ in *. clear θmax.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert (- (x₁ - 0) * sin 0 + (- y₁ - 0) * cos 0 = - y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (- y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  rewrite atan2_symmetry. lra.
  intro sc. destruct sc as [scx scy]. lra.
  rewrite tmid.
  set (θmax' := calcθ₁ 0 0 0 x₁ (- y₁)) in *.

  set (Q' := sqrt (x₁² - (2 * (-r) - (-y₁)) * (-y₁))) in *.
  assert (Q' = Q) as Q1rel;
    [ unfold Q, Q';
      assert ((x₁² - (2 * - r - - y₁) * - y₁) = (x₁² - (2 * r - y₁) * y₁)) as argeq;
      [lra|]; rewrite argeq; reflexivity|].

  set (θ1' := 2 * atan ((x₁ - Q') / (2 * (-r) - (-y₁)))).
  assert (θ1 = -θ1') as t1rel. unfold θ1, θ1'.
  rewrite Q1rel.
  assert ((x₁ - Q) / (2 * - r - - y₁) = (- ((x₁ - Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  set (θ2' := 2 * atan ((x₁ + Q') / (2 * (-r) - (-y₁)))).
  assert (θ2 = -θ2') as t2rel. unfold θ2, θ2'.
  rewrite Q1rel.
  assert ((x₁ + Q) / (2 * - r - - y₁) = (- ((x₁ + Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  rewrite t2rel, t1rel.
  enough (θ1' < θmax' < θ2' /\ 0 < θ1' < PI /\ 0 < θ2' < PI)
    as [[tmordlb tmordub] [[t1ordlb t1ordub] [t2ordlb t2ordub]]].
  lra.
  apply root_ordering_Q1bot; try assumption.
  lra.
Qed.

Lemma root_ordering_Q2top:
  forall x₁ y₁ r 
         (rgt0 : 0 < r)
         (top : 2 * r - y₁ < 0)
         (lf : x₁ <= 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) in
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) + 2 * IZR 1 * PI in
    θ1 < θmax < θ2 /\ (* PI/2 *) 0 < θ1 < PI /\ PI < θ2 < 2*PI. 
Proof.
  intros.
  specialize PI_RGT_0 as pirgt0.
  assert (2*PI >0) as tpigt0. lra.
  
  assert (0 < y₁) as y1gt0. lra.


  assert (0 < θ1 < PI) as [t1lb t1ub]. {

    assert (x₁² < x₁² - (2 * r - y₁) * y₁) as inq.
    apply (Rplus_lt_reg_r (-x₁²)).
    setl 0. setr (- (2 * r - y₁) * y₁).
    apply Rmult_lt_0_compat; lra.

    assert ((x₁ - Q) < 0) as xpos. {
      apply (Rplus_lt_reg_r Q). setr Q. setl x₁.
      apply (Rle_lt_trans _ 0). assumption.
      unfold Q.
      apply sqrt_lt_R0.
      apply (Rle_lt_trans _ (x₁²)).
      apply Rle_0_sqr.
      assumption.
    }

    clear inq.
    assert (0 < ((x₁ - Q) / (2 * r - y₁))) as argpos.
    fieldrewrite ((x₁ - Q) / (2 * r - y₁)) (- (x₁ - Q) * / - (2 * r - y₁)).
    intro; lra.
    apply Rmult_lt_0_compat. lra.
    apply Rinv_0_lt_compat. lra.
    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.

    specialize (atan_bound ((x₁ - Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atub; [|lra].
    unfold θ1.
    split. lra.
    fieldrewrite (PI) (2 * (PI/2)).
    assumption. }

    assert (PI < θ2 < 2*PI) as [t2lb t2ub]. {

    assert (x₁² < x₁² - (2 * r - y₁) * y₁) as inq.
    apply (Rplus_lt_reg_r (-x₁²)).
    setl 0. setr (- (2 * r - y₁) * y₁).
    apply Rmult_lt_0_compat; lra.

    assert (0 < x₁ + Q) as xpos. {
      apply (Rplus_lt_reg_r (-x₁)). setl (-x₁). setr Q.
      unfold Q.
      rewrite <- (sqrt_Rsqr (-x₁)) at 1; [|lra].
      apply sqrt_lt_1;
        [apply Rle_0_sqr |
         apply (Rle_trans _ (x₁²));
         [ apply Rle_0_sqr| left; assumption] |
         rewrite <- Rsqr_neg; assumption].
    }
      
    clear inq.
    assert (((x₁ + Q) / (2 * r - y₁)) < 0) as argneg.
    apply (Rmult_lt_reg_r (- ((2 * r - y₁)))). lra.
    setl (- (x₁ + Q)). intro ; lra. setr 0. lra.
    apply atan_increasing in argneg.
    rewrite atan_0 in argneg.
    apply (Rmult_lt_compat_l 2) in argneg; [|lra].
    rewrite Rmult_0_r in argneg.
    apply (Rplus_lt_compat_r (2 * IZR 1 * PI)) in argneg.
    rewrite Rplus_0_l in argneg.
    rewrite Rmult_assoc in argneg at 2.
    rewrite Rmult_1_l in argneg.
    
    specialize (atan_bound ((x₁ + Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atlb; [|lra].
    apply (Rplus_lt_compat_r (2 * IZR 1 * PI)) in atlb.
    assert (2 * (- PI / 2) + 2 * 1 * PI = PI) as id. field.
    rewrite id in atlb. clear id.

    unfold θ2.
    split; assumption.
  }

  rename lf into lf'.
  destruct lf' as [lf |le].
    
  assert (PI < θmax < 2*PI) as [tmlb tbub]. {
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    specialize (atan2Q2 _ _ lf y1gt0) as at2rng.
    inversion_clear at2rng as [lb ub].
    apply (Rmult_lt_compat_l 2) in lb; [|lra].
    apply (Rmult_lt_compat_l 2) in ub; [|lra].
    assert (2 * (PI / 2) = PI) as id. field. rewrite id in *. clear id.
    split; lra.
  }

  
  specialize (k_is_derive_atan2 x₁ y₁ r) as k2id.
  assert (r <> 0) as rne0. intro; lra.
  assert (forall θ,
             ~ (x₁ - r * sin θ <= 0 /\
                y₁ - r * (1 - cos θ) = 0)) as cond. {
  intros. intros [xc yc].
  assert (y₁ = r * (1 - cos θ)) as y1def.
  apply (Rplus_eq_reg_r (- r * (1 - cos θ))). setr 0. rewrite <- yc. field.
  rewrite y1def in top.
  specialize (COS_bound θ) as [clb cub].
  assert ((1 - cos θ) <= 2) as le2. lra.
  apply (Rmult_le_compat_l r) in le2; [|lra].
  rewrite (Rmult_comm _ 2) in le2.
  apply Ropp_le_contravar in le2.
  repeat rewrite Ropp_mult_distr_l in le2.
  apply (Rplus_le_compat_l (2*r)) in le2.
  assert (2 * r + - r * (1 - cos θ) =
          2 * r - r * (1 - cos θ)) as id. field. rewrite id in le2. clear id.
  assert (2 * r + - (2) * r = 0) as id. field. rewrite id in le2. clear id.
  clear - top le2. lra. }
  
  assert (forall x : R, is_derive (κ₂ x₁ y₁ r) x (κ' x₁ y₁ r x)) as kd.
  intro.
  eapply k2id; eauto.
  specialize (k2_continuity _ _ _ rne0 cond) as k2c.
  clear cond rne0 k2id.

  assert (θ1 < θ2) as t2ltt2. { lra. }

  assert ((κ₂ x₁ y₁ r θ2) < (κ₂ x₁ y₁ r PI)) as kord. {
    rewrite (k2_periodic _ _ _ (-1%Z)).
    rewrite (k2_periodic _ _ _ (-1%Z) PI).
    set (f := (κ₂ x₁ y₁ r)) in *.
    simpl.
    assert (-PI < (θ2 + 2 * -1 * PI)) as t2lb2. lra.
    assert ((θ2 + 2 * -1 * PI) < 0) as t2ub2. lra.
    fieldrewrite (PI + 2 * -1 * PI) (-PI).
   
    eapply (derive_decreasing_interv (-PI) (θ2 + 2 * -1 * PI) f); try lra.
    intros. destruct H as [tlb tub].
    assert (derivable_pt f t) as dpft.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r t). apply kd.
    rewrite Derive_Reals.
    rewrite (is_derive_unique _ _ _ (kd t)).
    apply signeqm1_eqv.

    apply k_deriv_sign_quad_Aneg_rpos; auto.
    split; try assumption. lra. 
    left.
    apply (Rmult_lt_reg_l 2); [lra|]. setl t.
    apply (Rplus_lt_reg_r (2 * 1 * PI)).
    apply (Rplus_lt_reg_r (2 * -1 * PI)).
    setl (t).
    change (t < θ2 + 2 * -1 * PI). lra.

    Unshelve.
    unfold derivable. intros.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r x). apply kd.
  }

  assert (Rmin (κ₂ x₁ y₁ r θ2) (κ₂ x₁ y₁ r PI) < θmax/2 <
          Rmax (κ₂ x₁ y₁ r θ2) (κ₂ x₁ y₁ r PI)) as inq. {
    rewrite Rmin_left, Rmax_right; try (left; assumption).
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).
    split.
    + assert (y₁ = y₁ - r * (1 - 1)) as id. field. rewrite id at 2. clear id.
      assert (x₁ = x₁ - r * 0) as id. field. rewrite id at 2. clear id.
      rewrite <- sin_0. rewrite <- cos_0 at 2. 
      change (κ₂ x₁ y₁ r θ2 < κ₂ x₁ y₁ r 0).
      
      rewrite (k2_periodic _ _ _ (-1%Z)). simpl.
      assert (-PI < (θ2 + 2 * -1 * PI)) as t2lb2. lra.
      assert ((θ2 + 2 * -1 * PI) < 0) as t2ub2. lra.

      set (f := (κ₂ x₁ y₁ r)) in *.
      eapply (derive_increasing_interv (θ2 + 2 * -1 *PI) 0 f); try lra.
      intros.
      assert (derivable_pt f t) as dpft.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r t). apply kd.
      rewrite Derive_Reals.
      rewrite (is_derive_unique _ _ _ (kd t)).
      apply signeq1_eqv.

      apply k_deriv_sign_quad_Aneg_rpos; auto.
      inversion_clear H as [tlb tub].
      split; try assumption. lra. lra.
      split.
      ++ apply (Rmult_lt_reg_l 2); [lra|]. setr t.
         rewrite <- (Rplus_0_r (2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                            / (2 * r - y₁)))).
         rewrite <- (Rplus_opp_r (2*1*PI)).
         rewrite <- Rplus_assoc.
         change (θ2 - (2*1*PI)< t).
         destruct H. lra.
      ++ apply (Rmult_lt_reg_l 2); [lra|]. setl t.
         destruct H.
         change (t < θ1).
         apply (Rlt_trans _ 0); assumption. 

         Unshelve.
         unfold derivable. intros.
         apply ex_derive_Reals_0.
         unfold ex_derive.
         exists (κ' x₁ y₁ r x). apply kd.

    + unfold κ₂.
      rewrite cos_PI, sin_PI.
      fieldrewrite (y₁ - r * (1 - -1)) (y₁ - 2*r).
      fieldrewrite (x₁ - r * 0) (x₁).
      assert (0 < y₁ - 2 * r) as retop. lra.
      rewrite atan2_atan_Q2; try lra.
      rewrite atan2_atan_Q2; try lra.
      apply (Rplus_lt_reg_r (-PI)).
      setr (atan ((y₁ - 2 * r) / x₁)).
      setl (atan (y₁ / x₁)).
      apply atan_increasing.
      apply (Rmult_lt_reg_r (-x₁)); try lra.
      setl (-y₁). intro; lra.
      setr (- (y₁ - 2 * r)). intro ;lra.
      apply (Rplus_lt_reg_r (y₁)).
      setl 0. setr (2 * r).
      lra.
         
  }

  specialize (IVT_gen_strict _ _ _ _ k2c inq) as [x [bnd def]].
  rewrite Rmin_right in bnd; [|left; lra].
  rewrite Rmax_left in bnd; [|left; lra].
  rewrite k_center_val in def.
  assert (x = θmax) as xeq.
  apply (Rmult_eq_reg_r (/2)). assumption.
  apply Rinv_neq_0_compat. discrR.

  split.
  + split. lra. rewrite <- xeq. destruct bnd.
    clear - H0 pirgt0. lra.

  + split; split; lra.
  + destruct bnd.
    split.
    apply Rmult_lt_0_compat;[ assumption|lra].
    rewrite Rabs_right; try (left; assumption).
    apply Rmult_lt_compat_l; try assumption.
    lra.
    
  + intro; lra.
    
  + intro.
    destruct bnd.
    assert (- PI < x + 2* -1 * PI <= PI) as xrng.
    split; lra.
    rewrite <- (sin_period1 _ (-1%Z)) in H.
    simpl in H.
    apply sinθeq0 in H; try assumption.
    inversion_clear H as [xeq0|xeqPI].
    assert (x = 2 * PI) as xeq2PI. lra.
    rewrite xeq2PI in H1. clear - H1 pirgt0 t2ub. lra.
    assert (x = 3*PI) as xeq3PI. lra.
    rewrite xeq3PI in H1. clear - H1 t2ub pirgt0. lra.
  + apply Rmult_lt_0_compat. assumption.
    apply (Rlt_trans _ PI); assumption.
  + assert (0 < x) as zltx. inversion_clear bnd. lra.
    assumption.
  + rewrite def. unfold θmax. reflexivity.

  + unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    rewrite le in *.
    rewrite atan2_PI2. 

    repeat split; lra.
    assumption.
Qed.

Lemma root_ordering_Q3top_rneg:
  forall x₁ y₁ r 
         (rgt0 : r < 0)
         (top : 0 < 2 * r - y₁)
         (lf : x₁ <= 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) in
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) - 2 * IZR 1 * PI in
    θ2 < θmax < θ1 /\ -PI < θ1 < 0 /\ - 2 * PI < θ2 < - PI.
Proof.
  intros.

  apply straight_symmetry in phase.
  assert (0 < (-r)) as rgt0';[ lra|].
  assert (2*(-r) - (- y₁) <0) as top'; [lra|].
  rewrite Ropp_0 in phase.

  assert (θmax = - calcθ₁ 0 0 0 x₁ (-y₁)) as tmid.
  unfold θmax, calcθ₁ in *. clear θmax.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert (- (x₁ - 0) * sin 0 + (- y₁ - 0) * cos 0 = - y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (- y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  rewrite atan2_symmetry. lra.
  intro sc. destruct sc as [scx scy]. lra.
  rewrite tmid.
  set (θmax' := calcθ₁ 0 0 0 x₁ (- y₁)) in *.

  set (Q' := sqrt (x₁² - (2 * (-r) - (-y₁)) * (-y₁))) in *.
  assert (Q' = Q) as Q1rel;
    [ unfold Q, Q';
      assert ((x₁² - (2 * - r - - y₁) * - y₁) = (x₁² - (2 * r - y₁) * y₁)) as argeq;
      [lra|]; rewrite argeq; reflexivity|].

  set (θ1' := 2 * atan ((x₁ - Q') / (2 * (-r) - (-y₁)))).
  assert (θ1 = -θ1') as t1rel. unfold θ1, θ1'.
  rewrite Q1rel.
  assert ((x₁ - Q) / (2 * - r - - y₁) = (- ((x₁ - Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  set (θ2' := 2 * atan ((x₁ + Q') / (2 * (-r) - (-y₁))) + 2 * 1 * PI).
  assert (θ2 = -θ2') as t2rel. unfold θ2, θ2'.
  rewrite Q1rel.
  assert ((x₁ + Q) / (2 * - r - - y₁) = (- ((x₁ + Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  rewrite t2rel, t1rel.
  enough (θ1' < θmax' < θ2' /\ 0 < θ1' < PI /\ PI < θ2' < 2* PI)
    as [[tmordlb tmordub] [[t1ordlb t1ordub] [t2ordlb t2ordub]]].
  lra.
  apply root_ordering_Q2top; assumption.
Qed.


Lemma root_ordering_Q2arm:
  forall x₁ y₁ r 
         (rgt0 : 0 < r)
         (top : 2 * r - y₁ = 0)
         (lf : x₁ <= 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in (* (PI,2*PI) *)
    let θ1 := PI in
    let θ2 := 2*atan (y₁ / (2 * x₁)) + 2 * IZR 1 * PI in
    θ1 < θmax < θ2 /\ PI < θ2 < 2*PI.
Proof.
  intros.
  specialize PI_RGT_0 as pirgt0.
  assert (2*PI >0) as tpigt0. lra.
  
  assert (0 < y₁) as y1gt0. lra.

  rename lf into lf'.
  destruct lf' as [lf |le].
  
  assert (PI < θmax < 2*PI) as [tmlb tbub]. {
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    specialize (atan2Q2 _ _ lf y1gt0) as at2rng.
    inversion_clear at2rng as [lb ub].
    apply (Rmult_lt_compat_l 2) in lb; [|lra].
    apply (Rmult_lt_compat_l 2) in ub; [|lra].
    assert (2 * (PI / 2) = PI) as id. field. rewrite id in *. clear id.
    split; lra.
  }
  
  assert (PI < θ2 < 2*PI) as [t2lb t2ub]. {
    
    assert (y₁/(2*x₁)<0) as xpos. {
      apply (Rmult_lt_reg_r (2*(-x₁))). lra.
      setr 0. setl (-y₁). intro. lra. lra.
    }
      
    apply atan_increasing in xpos.
    rewrite atan_0 in xpos.
    apply (Rmult_lt_compat_l 2) in xpos; [|lra]. 
    rewrite Rmult_0_r in xpos.
    apply (Rplus_lt_compat_r (2 * IZR 1 * PI)) in xpos.
    rewrite Rplus_0_l in xpos.
    rewrite Rmult_assoc in xpos at 2.
    rewrite Rmult_1_l in xpos.
    
    specialize (atan_bound (y₁ / (2 * x₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atlb; [|lra].
    apply (Rplus_lt_compat_r (2 * IZR 1 * PI)) in atlb.
    assert (2 * (- PI / 2) + 2 * 1 * PI = PI) as id. field.
    rewrite id in atlb. clear id.

    unfold θ2.
    split; assumption.
  }

  specialize (k_is_derive_atan3 x₁ y₁ r) as k3id.
  assert (r <> 0) as rne0. intro; lra.
  assert (forall θ,
             ~ (0 <= x₁ - r * sin θ /\
                y₁ - r * (1 - cos θ) = 0)) as cond. {
  intros. intros [xc yc].

  assert (y₁ = r * (1 - cos θ)) as y1def.
  apply (Rplus_eq_reg_r (- r * (1 - cos θ))). setr 0. rewrite <- yc. field.

  apply (straight_std_impl_ineq) in phase.

  assert (r² < r²) as r2ltr2. {
  rewrite <- Rmult_1_r at 2. rewrite <- (sin2_cos2 θ).
  setr ( (r *sin θ)² + (r * cos θ)²).
  apply (Rlt_le_trans _ (x₁² + (r *cos θ)²)).
  rewrite (Rsqr_neg (r * cos θ)).
  fieldrewrite (- (r * cos θ)) (r * (1 - cos θ) - r).
  rewrite <- y1def.
  assumption.
  apply (Rplus_le_reg_r (-(r * cos θ)²)).
  setl (x₁²). setr ((r * sin θ)²).
  apply Rsqr_le_abs_1.
  rewrite Rabs_left; [|lra].
  rewrite Rabs_left.

  apply (Rplus_le_reg_r (x₁)).
  setr (x₁ - (r * sin θ)). setl (0).
  assumption.
  lra. }
  lra. }

  assert (forall x : R, is_derive (κ₃ x₁ y₁ r) x (κ' x₁ y₁ r x)) as kd.
  intro.
  eapply k3id; eauto.
  
  specialize (k3_continuity _ _ _ rne0 cond) as k3c.
  clear cond rne0 k3id.

  assert (θ1 < θ2) as t2ltt2. {
    unfold θ1,θ2.
    apply (Rmult_lt_reg_l (/2)).
    apply Rinv_0_lt_compat. lra.
    repeat rewrite Rmult_plus_distr_l.
    repeat rewrite <- (Rmult_assoc (/ 2)).
    fieldrewrite (/ 2 * 2) 1.
    repeat rewrite Rmult_1_l.
    apply (Rplus_lt_reg_r (-PI)).
    repeat rewrite Rplus_assoc.
    fieldrewrite (/2 * PI + - PI) (-PI/2).
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    apply atan_bound.
    }

  assert ((κ₃ x₁ y₁ r θ2) < (κ₃ x₁ y₁ r θ1)) as kord. {
    set (f := (κ₃ x₁ y₁ r)) in *.
    eapply (derive_decreasing_interv θ1 θ2 f); try lra.
    intros.
    assert (derivable_pt f t) as dpft.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r t). apply kd.
    rewrite Derive_Reals.
    rewrite (is_derive_unique _ _ _ (kd t)).
    apply signeqm1_eqv.

    rewrite (k'_periodic _ _ _ (-1)).
    apply k_deriv_sign_lin_rpos; auto.
    
    inversion_clear H as [tlb tub].
    split. unfold θ1 in tlb. lra. lra.
    split; try assumption.
    inversion_clear H as [tlb tub].
    unfold θ2 in tub. lra.

    Unshelve.
    unfold derivable. intros.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r x). apply kd.
  }

  
  assert (Rmin (κ₃ x₁ y₁ r θ1) (κ₃ x₁ y₁ r θ2) < θmax/2 <
          Rmax (κ₃ x₁ y₁ r θ1) (κ₃ x₁ y₁ r θ2)) as tmrng. {
    rewrite Rmin_right, Rmax_left; try (left; assumption).
    split.

    + set (f := (κ₃ x₁ y₁ r)) in *.
      assert (f θ2  < f (2*PI)) as gluerng1. {
        eapply (derive_increasing_interv θ2 (2*PI) f); try lra;
          try (split; lra).
        intros.
        assert (derivable_pt f t) as dpft.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        exists (κ' x₁ y₁ r t). apply kd.
        rewrite Derive_Reals.
        rewrite (is_derive_unique _ _ _ (kd t)).
        apply signeq1_eqv.

        inversion_clear H as [tlb tub].
        rewrite (k'_periodic _ _ _ (-1)).
        apply k_deriv_sign_lin_rpos; auto.
        split; try assumption. lra. lra.
        split; try assumption.
        apply (Rmult_lt_reg_l 2). lra.
        apply (Rplus_lt_reg_r (2*1*PI)). 
        setr (t).
        assumption. }
        
      assert (f (2*PI) = f 0) as gluept. {
        unfold f. fieldrewrite (2*PI) (2*1*PI).
        unfold κ₃ at 1, atan3 at 1.
        rewrite <- (cos_period1 _ (-1)), <- (sin_period1 _ (-1)).
        fieldrewrite (2 * 1 * PI + 2 * -1 * PI) 0.
        change (κ₃ x₁ y₁ r 0 = κ₃ x₁ y₁ r 0).
        reflexivity. }

      rewrite gluept in gluerng1. clear gluept.
      
      unfold θmax, calcθ₁. rewrite cos_0, sin_0.
      fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
      fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
      fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).

      rewrite atan3_atan2_Q1Q2_eqv; try assumption.

      assert (y₁ = y₁ - r * (1 - 1)) as id. field. rewrite id. clear id.
      assert (x₁ = x₁ - r * 0) as id. field. rewrite id. clear id.
      rewrite <- sin_0. rewrite <- cos_0 at 2.
      change (κ₃ x₁ y₁ r θ2 < κ₃ x₁ y₁ r 0).
      unfold f in *. assumption.
      
    + unfold θmax, calcθ₁. rewrite cos_0, sin_0.
      fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
      fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
      fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).

      rewrite atan3_atan2_Q1Q2_eqv; try assumption.

      assert (y₁ = y₁ - r * (1 - 1)) as id. field. rewrite id at 1. clear id.
      assert (x₁ = x₁ - r * 0) as id. field. rewrite id at 1. clear id.
      rewrite <- sin_0. rewrite <- cos_0 at 2.
      change (κ₃ x₁ y₁ r 0 < κ₃ x₁ y₁ r θ1).

      set (f := (κ₃ x₁ y₁ r)) in *.

      unfold θ1 in *.
      unfold f.
      rewrite (k3_periodic _ _ _ (1)).
      rewrite (k3_periodic _ _ _ (1) PI).
        
      eapply (derive_increasing_interv (0+2*(1)*PI) (PI+2*(1)*PI) f); try lra;
        try (split; lra).
      intros.
      assert (derivable_pt f t) as dpft.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r t). apply kd.
      rewrite Derive_Reals.
      rewrite (is_derive_unique _ _ _ (kd t)).
      apply signeq1_eqv.
      
      inversion_clear H as [tlb tub].
      rewrite (k'_periodic _ _ _ (-1)).
      apply k_deriv_sign_lin_rpos; auto.
      split; try assumption.
      lra. lra.
      split; try assumption.
      apply (Rmult_lt_reg_l 2). lra.
      apply (Rplus_lt_reg_r (2*1*PI)).
      setr t.
      apply (Rlt_trans _ (2*PI)). assumption. lra.

      Unshelve.
      unfold derivable. intros.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r x). apply kd.
      unfold derivable. intros.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r x). apply kd.
  }
  
  specialize (IVT_gen_strict _ _ _ _ k3c tmrng) as [x [bnd def]].
  rewrite Rmin_left in bnd; [|left; assumption].
  rewrite Rmax_right in bnd; [|left; assumption].
  rewrite Rmin_right in tmrng; [|left; assumption].
  rewrite Rmax_left in tmrng; [|left; assumption].

  unfold κ₃ in def.
  rewrite <- atan3_atan2_Q1Q2_eqv in def; try assumption.
  change (κ₂ x₁ y₁ r x = θmax / 2) in def.
  rewrite k_center_val in def.
  assert (x = θmax) as xeq.
  apply (Rmult_eq_reg_r (/2)). assumption.
  apply Rinv_neq_0_compat. discrR.
  subst.

  split.
  + assumption.  
  + split; assumption.

  + destruct bnd as [lb ub].
    
    split.
    unfold θ1 in lb.
    apply Rmult_lt_0_compat; [assumption|lra].
    rewrite Rabs_right. apply Rmult_lt_compat_l; try assumption.
    lra. left. assumption.
    
  + intro; lra.
  + inversion_clear bnd as [lb ub]. unfold θ1 in lb.
    assert (x < 2*PI) as xltPI. lra.
    intro sinx0.
    rewrite <- (sin_period1 _ (-1)) in sinx0.
    assert (- PI < x + 2*-1*PI <= PI) as xrng. split; lra.
    apply sinθeq0 in sinx0; try assumption.
    inversion_clear sinx0 as [xeq0|xeqPI].
    assert (x = 2*PI) as xeq2PI. lra.
    rewrite xeq2PI in xltPI. clear - xltPI. lra.
    assert (x = 3*PI) as xeq3PI. lra.
    rewrite xeq3PI in xltPI. clear - xltPI pirgt0. lra.
  + apply Rmult_lt_0_compat; try assumption.
    apply (Rlt_trans _ PI). lra. assumption.
  + assumption.
  + rewrite def. unfold θmax. reflexivity.
  + assert (PI/2 < θmax/2 < PI) as tm2rng; [split; lra|].
    rewrite <- def in tm2rng.
    apply atan3Q2_rev in tm2rng.
    destruct tm2rng as [xlt0 zlty].
    assumption.
    
    intros [xe ye].
    
    apply (straight_std_impl_ineq) in phase.
    assert (y₁ = r * (1-cos x)) as xdef.
    apply (Rplus_eq_reg_r (-r*(1-cos x))). setr 0. rewrite <- ye. field.
    assert (x₁ = r * sin x) as ydef.
    apply (Rplus_eq_reg_r (-r*sin x)). setr 0. rewrite <- xe. field.
    rewrite ydef, xdef in phase.
    
    assert (r² < r²) as cont. {
      rewrite <- Rmult_1_l. rewrite Rmult_comm, <- (sin2_cos2 x).
      setr ((r *sin x)² + (r *cos x)²).
      rewrite (Rsqr_neg (r * cos x)).
      apply (Rlt_le_trans _ (x₁² + (- (r * cos x))²)).
      fieldrewrite (- (r * cos x)) (r * (1- cos x) - r).
      rewrite ydef. assumption.
      rewrite ydef. right. reflexivity. } lra.

  + exfalso. clear - phase le top y1gt0.
    apply (straight_std_impl_ineq) in phase.
    rewrite le in *.
    rewrite Rsqr_0, Rplus_0_l in phase.
    assert ((y₁ - r)² =  - ((2*r - y₁)*y₁) + r²) as id. unfold Rsqr. field.
    rewrite id,top,Rmult_0_l, Ropp_0,Rplus_0_l in phase. clear id.
    lra.
Qed.

Lemma root_ordering_Q3arm_rneg:
  forall x₁ y₁ r 
         (rgt0 : r < 0)
         (top : 2 * r - y₁ = 0)
         (lf : x₁ <= 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let θ1 := - PI in
    let θ2 := 2*atan (y₁ / (2 * x₁)) - 2 * IZR 1 * PI in
    θ2 < θmax < θ1 /\ -2*PI < θ2 < - PI.
Proof.
  intros.

  apply straight_symmetry in phase.
  assert (0 < (-r)) as rgt0';[ lra|].
  assert (0 = 2*(-r) - (- y₁)) as bot'; [lra|].
  rewrite Ropp_0 in phase.

  assert (θmax = - calcθ₁ 0 0 0 x₁ (-y₁)) as tmid.
  unfold θmax, calcθ₁ in *. clear θmax.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert (- (x₁ - 0) * sin 0 + (- y₁ - 0) * cos 0 = - y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (- y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  rewrite atan2_symmetry. lra.
  intro sc. destruct sc as [scx scy]. lra.
  rewrite tmid.
  set (θmax' := calcθ₁ 0 0 0 x₁ (- y₁)) in *.

  rename lf into lf'.
  destruct lf' as [lf|lf].
  
  set (θ2' := 2 * atan ((- y₁) / (2 * x₁)) + 2 * 1 *PI).
  assert (θ2 = -θ2') as t1rel. unfold θ2, θ2'.
  assert ((- y₁ / (2 * x₁)) = (- (y₁ / (2 * x₁)))).
  field. intro; lra. rewrite H.
  rewrite atan_opp. field.

  set (θ1' := PI).
  assert (θ1 = -θ1') as t2rel. unfold θ1, θ1'. reflexivity.

  rewrite t2rel, t1rel.
  enough (θ1' < θmax' < θ2' /\ PI < θ2' < 2*PI)
    as [[tmordlb tmordub] [t1ordlb t1ordub]].
  unfold θ1' at 2.
  unfold θ1' at 2.
  lra.
  eapply root_ordering_Q2arm; try eassumption.
  lra.
  left. assumption.

  exfalso. clear - phase lf top.
    apply (straight_std_impl_ineq) in phase.
    rewrite lf in *.
    rewrite Rsqr_0, Rplus_0_l in phase.
    assert ((- y₁ - - r)² =  - ((2*r - y₁)*y₁) + r²) as id. unfold Rsqr. field.
    rewrite id,top,Rmult_0_l, Ropp_0,Rplus_0_l, <- Rsqr_neg in phase. clear id.
    lra.
Qed.

Lemma root_ordering_Q2bot:
  forall x₁ y₁ r 
         (rgt0 : 0 < r)
         (bot : 0 < 2 * r - y₁)
         (Q2 : 0 < y₁)
         (lf : x₁ < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in (* (PI,2*PI) *)
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) + 2 * IZR 1 * PI in (* (-PI,0) *)
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) + 2 * IZR 1 * PI  in (* (-PI,0) *)
    θ1 < θmax < θ2 /\ PI < θ1 < 2*PI /\ PI < θ2 < 2*PI.
Proof.
  intros.
  specialize PI_RGT_0 as pirgt0.
  assert (2*PI >0) as tpigt0. lra.

  rename Q2 into y1gt0.

  assert (PI < θmax < 2*PI) as [tmlb tbub]. {
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    specialize (atan2Q2 _ _ lf y1gt0) as at2rng.
    inversion_clear at2rng as [lb ub].
    apply (Rmult_lt_compat_l 2) in lb; [|lra].
    apply (Rmult_lt_compat_l 2) in ub; [|lra].
    assert (2 * (PI / 2) = PI) as id. field. rewrite id in *. clear id.
    split; lra.
  }

  assert (x₁² - (2 * r - y₁) * y₁ < x₁²) as inq. {
    apply (Rplus_lt_reg_r (-x₁²)).
    setr 0. setl (- ((2 * r - y₁) * y₁)).
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar. 
    apply Rmult_lt_0_compat; lra. }

  assert (0 < x₁² - (2 * r - y₁) * y₁) as sqalb. {
    apply (Rplus_lt_reg_r (r²)).
    setl (r²). setr (x₁² + (y₁ - r)²).
    apply (straight_std_impl_ineq) in phase.
    assumption.
  }
  
  assert ((x₁ - Q) < 0) as xpos. {
    apply (Rplus_lt_reg_r Q). setr Q. setl x₁.
    apply (Rlt_trans _ 0). assumption.
    unfold Q.
    apply sqrt_lt_R0.
    assumption. }
  
  assert (PI < θ1 < 2*PI) as [t1lb t1ub]. {

    assert (((x₁ - Q) / (2 * r - y₁)) < 0) as argpos.
    apply (Rmult_lt_reg_r (2 * r - y₁)); [ assumption|].
    setr 0. setl (x₁ - Q).
    intro; lra. assumption.

    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.
    apply (Rplus_lt_compat_r (2*1*PI)) in argpos. rewrite Rplus_0_l in argpos.
    
    specialize (atan_bound ((x₁ - Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atub; [|lra].
    unfold θ1.
    split.
    apply (Rmult_lt_compat_l 2) in atlb.
    apply (Rplus_lt_compat_r (2*1*PI)) in atlb.
    assert (PI = 2 * (- PI / 2) + 2 * 1 * PI) as id. field.
    rewrite id at 1. assumption. lra. lra. }

    assert (x₁ + Q < 0) as xppos. {
    apply (Rplus_lt_reg_r (-x₁)). setr (-x₁). setl Q.
    unfold Q.
    rewrite <- (sqrt_Rsqr (-x₁)) at 1; [|left; lra].
    apply sqrt_lt_1. left. assumption.
    apply Rle_0_sqr.
    rewrite <- Rsqr_neg. assumption.
  }

    assert (PI < θ2 < 2*PI) as [t2lb t2ub]. {
      
    assert (((x₁ + Q) / (2 * r - y₁)) < 0) as argpos.
    apply (Rmult_lt_reg_r ((2 * r - y₁))). lra.
    setl (x₁ + Q). intro ; lra. setr 0. assumption.
    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.
    
    specialize (atan_bound ((x₁ + Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atub; [|lra].
    assert (2 * ( PI / 2) =  PI) as id. field.
    rewrite id in atub. clear id.
    apply (Rplus_lt_compat_r (2*1*PI)) in argpos. rewrite Rplus_0_l in argpos.

    unfold θ2.
    split.
    apply (Rmult_lt_compat_l 2) in atlb.
    apply (Rplus_lt_compat_r (2*1*PI)) in atlb.
    assert (PI = 2 * (- PI / 2) + 2 * 1 * PI) as id. field.
    rewrite id at 1. assumption. lra. lra. }

  assert (0 <= x₁² - (2 * r - y₁) * y₁) as sqalb2; [left; assumption|].
  apply (sqrt_lt_1 _ _ (Rle_refl 0) sqalb2) in sqalb.
  rewrite sqrt_0 in sqalb. change (0 < Q) in sqalb.

  specialize (k_is_derive_atan3 x₁ y₁ r) as k3id.
  assert (r <> 0) as rne0. intro; lra.
  assert (forall θ,
             ~ (0 <= x₁ - r * sin θ /\
                y₁ - r * (1 - cos θ) = 0)) as cond. {
  intros. intros [xc yc].

  assert (y₁ = r * (1 - cos θ)) as y1def.
  apply (Rplus_eq_reg_r (- r * (1 - cos θ))). setr 0. rewrite <- yc. field.

  apply (straight_std_impl_ineq) in phase.

  assert (r² < r²) as r2ltr2. {
  rewrite <- Rmult_1_r at 2. rewrite <- (sin2_cos2 θ).
  setr ( (r *sin θ)² + (r * cos θ)²).
  apply (Rlt_le_trans _ (x₁² + (r *cos θ)²)).
  rewrite (Rsqr_neg (r * cos θ)).
  fieldrewrite (- (r * cos θ)) (r * (1 - cos θ) - r).
  rewrite <- y1def.
  assumption.
  apply (Rplus_le_reg_r (-(r * cos θ)²)).
  setl (x₁²). setr ((r * sin θ)²).
  apply Rsqr_le_abs_1.
  rewrite Rabs_left; [|lra].
  rewrite Rabs_left.

  apply (Rplus_le_reg_r (x₁)).
  setr (x₁ - (r * sin θ)). setl (0).
  assumption.
  lra. }
  lra. }

  assert (forall x : R, is_derive (κ₃ x₁ y₁ r) x (κ' x₁ y₁ r x)) as kd.
  intro.
  eapply k3id; eauto.
  
  specialize (k3_continuity _ _ _ rne0 cond) as k3c.
  clear cond rne0 k3id.

  assert (θ1 < θ2) as t2ltt2. {
    unfold θ1,θ2.
    apply (Rmult_lt_reg_l (/2)).
    apply Rinv_0_lt_compat. lra.
    repeat rewrite Rmult_plus_distr_l.
    repeat rewrite <- (Rmult_assoc (/ 2)).
    fieldrewrite (/ 2 * 2) 1.
    repeat rewrite Rmult_1_l.
    apply (Rplus_lt_reg_r (-PI)).
    repeat rewrite Rplus_assoc.
    fieldrewrite (PI + - PI) 0.
    repeat rewrite Rplus_0_r.
    apply atan_increasing.
    apply (Rmult_lt_reg_l (2 * r - y₁)). assumption.
    apply (Rplus_lt_reg_r (-x₁)).
    setl (-Q). intro; lra. setr Q. intro; lra.
    lra.
  }

  assert ((κ₃ x₁ y₁ r θ2) < (κ₃ x₁ y₁ r θ1)) as kord. {
    set (f := (κ₃ x₁ y₁ r)) in *.
    eapply (derive_decreasing_interv θ1 θ2 f); try lra.
    intros.
    assert (derivable_pt f t) as dpft.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r t). apply kd.
    rewrite Derive_Reals.
    rewrite (is_derive_unique _ _ _ (kd t)).
    apply signeqm1_eqv.

    rewrite (k'_periodic _ _ _ (-1)).
    apply k_deriv_sign_quad_Apos_rpos; auto.
    inversion_clear H as [tlb tub].
    split; lra.
    inversion_clear H as [tlb tub].
    split.
    apply (Rmult_lt_reg_l 2); [lra|].
    apply (Rplus_lt_reg_r (2*1*PI)).
    setr t.
    assumption.
    apply (Rmult_lt_reg_l 2); [lra|].
    apply (Rplus_lt_reg_r (2*1*PI)).
    setl t.
    assumption.

    Unshelve.
    unfold derivable. intros.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (κ' x₁ y₁ r x). apply kd.
  }

  
  assert (Rmin (κ₃ x₁ y₁ r θ1) (κ₃ x₁ y₁ r θ2) < θmax/2 <
          Rmax (κ₃ x₁ y₁ r θ1) (κ₃ x₁ y₁ r θ2)) as tmrng. {
    rewrite Rmin_right, Rmax_left; try (left; assumption).
    split.

    + set (f := (κ₃ x₁ y₁ r)) in *.
      assert (f θ2  < f (2*PI)) as gluerng1. {
        eapply (derive_increasing_interv θ2 (2*PI) f); try lra;
          try (split; lra).
        intros.
        assert (derivable_pt f t) as dpft.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        exists (κ' x₁ y₁ r t). apply kd.
        rewrite Derive_Reals.
        rewrite (is_derive_unique _ _ _ (kd t)).
        apply signeq1_eqv.

        inversion_clear H as [tlb tub].
        rewrite (k'_periodic _ _ _ (-1)).
        apply k_deriv_sign_quad_Apos_rpos; auto.
        split; try assumption. lra. lra.
        right.
        apply (Rmult_lt_reg_l 2). lra.
        apply (Rplus_lt_reg_r (2*1*PI)). 
        setr (t).
        assumption. }
        
      assert (f (2*PI) = f 0) as gluept. {
        unfold f. fieldrewrite (2*PI) (2*1*PI).
        unfold κ₃ at 1, atan3 at 1.
        rewrite <- (cos_period1 _ (-1)), <- (sin_period1 _ (-1)).
        fieldrewrite (2 * 1 * PI + 2 * -1 * PI) 0.
        change (κ₃ x₁ y₁ r 0 = κ₃ x₁ y₁ r 0).
        reflexivity. }

      rewrite gluept in gluerng1. clear gluept.
      
      unfold θmax, calcθ₁. rewrite cos_0, sin_0.
      fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
      fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
      fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).

      rewrite atan3_atan2_Q1Q2_eqv; try assumption.

      assert (y₁ = y₁ - r * (1 - 1)) as id. field. rewrite id. clear id.
      assert (x₁ = x₁ - r * 0) as id. field. rewrite id. clear id.
      rewrite <- sin_0. rewrite <- cos_0 at 2.
      change (κ₃ x₁ y₁ r θ2 < κ₃ x₁ y₁ r 0).
      unfold f in *. assumption.
      
    + unfold θmax, calcθ₁. rewrite cos_0, sin_0.
      fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
      fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
      fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).

      rewrite atan3_atan2_Q1Q2_eqv; try assumption.

      assert (y₁ = y₁ - r * (1 - 1)) as id. field. rewrite id at 1. clear id.
      assert (x₁ = x₁ - r * 0) as id. field. rewrite id at 1. clear id.
      rewrite <- sin_0. rewrite <- cos_0 at 2.
      change (κ₃ x₁ y₁ r 0 < κ₃ x₁ y₁ r θ1).

      set (f := (κ₃ x₁ y₁ r)) in *.
      assert (f PI  < f θ1) as gluerng1. {
        eapply (derive_increasing_interv PI θ1 f); try lra;
          try (split; lra).
        intros.
        assert (derivable_pt f t) as dpft.
        apply ex_derive_Reals_0.
        unfold ex_derive.
        exists (κ' x₁ y₁ r t). apply kd.
        rewrite Derive_Reals.
        rewrite (is_derive_unique _ _ _ (kd t)).
        apply signeq1_eqv.

        inversion_clear H as [tlb tub].
        rewrite (k'_periodic _ _ _ (-1)).
        apply k_deriv_sign_quad_Apos_rpos; auto.
        split; try assumption. lra. lra.
        left.
        apply (Rmult_lt_reg_l 2). lra.
        apply (Rplus_lt_reg_r (2*1*PI)). 
        setl (t).
        assumption. }

      apply (Rlt_trans _ (f PI)); try assumption.
      unfold f.
      rewrite (k3_periodic _ _ _ (1)).
      rewrite (k3_periodic _ _ _ (1) PI).
        
      eapply (derive_increasing_interv (0+2*(1)*PI) (PI+2*(1)*PI) f); try lra;
        try (split; lra).
      intros.
      assert (derivable_pt f t) as dpft.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r t). apply kd.
      rewrite Derive_Reals.
      rewrite (is_derive_unique _ _ _ (kd t)).
      apply signeq1_eqv.
      
      inversion_clear H as [tlb tub].
      rewrite (k'_periodic _ _ _ (-1)).
      apply k_deriv_sign_quad_Apos_rpos; auto.
      split; try assumption.
      lra. lra.
      right.
      apply (Rmult_lt_reg_l 2). lra.
      apply (Rplus_lt_reg_r (2*1*PI)).
      setr t.
      apply (Rlt_trans _ (2*PI)). assumption. lra.

      Unshelve.
      unfold derivable. intros.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r x). apply kd.
      unfold derivable. intros.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r x). apply kd.
      unfold derivable. intros.
      apply ex_derive_Reals_0.
      unfold ex_derive.
      exists (κ' x₁ y₁ r x). apply kd.
      
  }
  
  specialize (IVT_gen_strict _ _ _ _ k3c tmrng) as [x [bnd def]].
  rewrite Rmin_left in bnd; [|left; assumption].
  rewrite Rmax_right in bnd; [|left; assumption].
  rewrite Rmin_right in tmrng; [|left; assumption].
  rewrite Rmax_left in tmrng; [|left; assumption].

  unfold κ₃ in def.
  rewrite <- atan3_atan2_Q1Q2_eqv in def; try assumption.
  change (κ₂ x₁ y₁ r x = θmax / 2) in def.
  rewrite k_center_val in def.
  assert (x = θmax) as xeq.
  apply (Rmult_eq_reg_r (/2)). assumption.
  apply Rinv_neq_0_compat. discrR.
  subst.

  split.
  + assumption.  
  + split. split; lra. split; lra.

  + destruct bnd as [lb ub].
    
    split.
    apply Rmult_lt_0_compat; [assumption|lra].
    rewrite Rabs_right. apply Rmult_lt_compat_l; try assumption.
    lra. left. assumption.
    
  + intro; lra.
  + assert (PI < x) as zltx. inversion_clear bnd. lra.
    assert (x < 2*PI) as xltPI. inversion_clear bnd. lra.
    intro sinx0.
    rewrite <- (sin_period1 _ (-1)) in sinx0.
    assert (- PI < x + 2*-1*PI <= PI) as xrng. split; lra.
    apply sinθeq0 in sinx0; try assumption.
    inversion_clear sinx0 as [xeq0|xeqPI].
    assert (x = 2*PI) as xeq2PI. lra.
    rewrite xeq2PI in xltPI. clear - xltPI. lra.
    assert (x = 3*PI) as xeq3PI. lra.
    rewrite xeq3PI in xltPI. clear - xltPI pirgt0. lra.
  + apply Rmult_lt_0_compat; try assumption.
    apply (Rlt_trans _ PI). lra. assumption.
  + assumption.
  + rewrite def. unfold θmax. reflexivity.
  + assert (PI/2 < θmax/2 < PI) as tm2rng; [split; lra|].
    rewrite <- def in tm2rng.
    apply atan3Q2_rev in tm2rng.
    destruct tm2rng as [xlt0 zlty].
    assumption.
    
    intros [xe ye].
    
    apply (straight_std_impl_ineq) in phase.
    assert (y₁ = r * (1-cos x)) as xdef.
    apply (Rplus_eq_reg_r (-r*(1-cos x))). setr 0. rewrite <- ye. field.
    assert (x₁ = r * sin x) as ydef.
    apply (Rplus_eq_reg_r (-r*sin x)). setr 0. rewrite <- xe. field.
    rewrite ydef, xdef in phase.
    
    assert (r² < r²) as cont. {
      rewrite <- Rmult_1_l. rewrite Rmult_comm, <- (sin2_cos2 x).
      setr ((r *sin x)² + (r *cos x)²).
      rewrite (Rsqr_neg (r * cos x)).
      apply (Rlt_le_trans _ (x₁² + (- (r * cos x))²)).
      fieldrewrite (- (r * cos x)) (r * (1- cos x) - r).
      rewrite ydef. assumption.
      rewrite ydef. right. reflexivity. } lra.
Qed.


Lemma root_ordering_Q3bot_rneg:
  forall x₁ y₁ r 
         (rgt0 : r < 0)
         (bot : 2 * r - y₁ < 0)
         (Q2 : y₁ < 0)
         (lf : x₁ < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) - 2 * IZR 1 * PI in
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) - 2 * IZR 1 * PI  in
    θ2 < θmax < θ1 /\ -2*PI < θ1 < -PI /\ -2*PI < θ2 < -PI.
Proof.
  intros.

  apply straight_symmetry in phase.
  assert (0 < (-r)) as rgt0';[ lra|].
  assert (0 < 2*(-r) - (- y₁)) as top'; [lra|].
  rewrite Ropp_0 in phase.

  assert (θmax = - calcθ₁ 0 0 0 x₁ (-y₁)) as tmid.
  unfold θmax, calcθ₁ in *. clear θmax.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert (- (x₁ - 0) * sin 0 + (- y₁ - 0) * cos 0 = - y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (- y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  rewrite atan2_symmetry. lra.
  intro sc. destruct sc as [scx scy]. lra.
  rewrite tmid.
  set (θmax' := calcθ₁ 0 0 0 x₁ (- y₁)) in *.

  set (Q' := sqrt (x₁² - (2 * (-r) - (-y₁)) * (-y₁))) in *.
  assert (Q' = Q) as Q1rel;
    [ unfold Q, Q';
      assert ((x₁² - (2 * - r - - y₁) * - y₁) = (x₁² - (2 * r - y₁) * y₁)) as argeq;
      [lra|]; rewrite argeq; reflexivity|].

  set (θ1' := 2 * atan ((x₁ - Q') / (2 * (-r) - (-y₁))) + 2 * 1 * PI).
  assert (θ1 = -θ1') as t1rel. unfold θ1, θ1'.
  rewrite Q1rel.
  assert ((x₁ - Q) / (2 * - r - - y₁) = (- ((x₁ - Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  set (θ2' := 2 * atan ((x₁ + Q') / (2 * (-r) - (-y₁))) + 2 * 1 * PI).
  assert (θ2 = -θ2') as t2rel. unfold θ2, θ2'.
  rewrite Q1rel.
  assert ((x₁ + Q) / (2 * - r - - y₁) = (- ((x₁ + Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  rewrite t2rel, t1rel.
  enough (θ1' < θmax' < θ2' /\ PI < θ1' < 2*PI /\ PI < θ2' < 2*PI)
    as [[tmordlb tmordub] [[t1ordlb t1ordub] [t2ordlb t2ordub]]].
  lra.
  apply root_ordering_Q2bot; try assumption.
  lra.
Qed.

Lemma root_ordering_nxarm:
  forall x₁ y₁ r 
         (rgt0 : 0 < r)
         (top : y₁ = 0)
         (lf : x₁ < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) + 2 * IZR 1 * PI in (* (-PI,0) *)
    let θ2 := 2*PI in
    θ1 < θmax /\ θmax = θ2 /\ PI < θ1 < 2*PI. (* θmax = θ2 *)
Proof.
  intros.
  specialize PI_RGT_0 as pirgt0.
  assert (2*PI >0) as tpigt0. lra.

  assert (0 < 2 * r - y₁) as bot; [lra|].

  assert (θmax = 2*PI) as tmeqPI. {
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    rewrite top.
    rewrite (atan2_PI _ lf). reflexivity. }

  assert (x₁² - (2 * r - y₁) * y₁ = x₁²) as inq. {
    apply (Rplus_eq_reg_r (-x₁²)).
    setr 0. rewrite top. setl 0. reflexivity. }

  assert (0 < x₁² - (2 * r - y₁) * y₁) as sqalb. {
    apply (straight_std_impl_ineq) in phase.
    rewrite top. 
    apply (Rplus_lt_reg_r (r²)).
    setl (r²). setr (x₁² + (0 - r)²).
    rewrite <- top.
    assumption.
  }
  
  assert ((x₁ - Q) < 0) as xpos. {
    apply (Rplus_lt_reg_r Q). setr Q. setl x₁.
    apply (Rlt_trans _ 0). assumption.
    unfold Q.
    apply sqrt_lt_R0.
    assumption. }
  
  assert (PI < θ1 < 2*PI) as [t1lb t1ub]. {

    assert (((x₁ - Q) / (2 * r - y₁)) < 0) as argpos.
    apply (Rmult_lt_reg_r (2 * r - y₁)); [ assumption|].
    setr 0. setl (x₁ - Q).
    intro; lra. assumption.

    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.
    apply (Rplus_lt_compat_r (2*1*PI)) in argpos. rewrite Rplus_0_l in argpos.
    
    specialize (atan_bound ((x₁ - Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atub; [|lra].
    unfold θ1.
    split.
    apply (Rmult_lt_compat_l 2) in atlb.
    apply (Rplus_lt_compat_r (2*1*PI)) in atlb.
    assert (PI = 2 * (- PI / 2) + 2 * 1 * PI) as id. field.
    rewrite id at 1. assumption. lra. lra. }

  rewrite tmeqPI in *.
  repeat split; try assumption.
Qed.

Lemma root_ordering_nxarm_rneg:
  forall x₁ y₁ r 
         (rgt0 : r < 0)
         (top : y₁ = 0)
         (lf : x₁ < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) - 2 * IZR 1 * PI in
    let θ2 := - 2*PI in
    - θmax < θ1 /\ - θmax = θ2 /\ -2*PI < θ1 < -PI.
Proof.
  intros.

  apply straight_symmetry in phase.
  assert (0 < (-r)) as rgt0';[ lra|].
  rewrite Ropp_0 in phase.

  assert (θmax = calcθ₁ 0 0 0 x₁ (-y₁)) as tmid.
  unfold θmax.
  rewrite top in *.
  rewrite Ropp_0 in *. reflexivity.
  set (θmax' := calcθ₁ 0 0 0 x₁ (- y₁)) in *.

  set (Q' := sqrt (x₁² - (2 * (-r) - (-y₁)) * (-y₁))) in *.
  assert (Q' = Q) as Q1rel;
    [ unfold Q, Q';
      assert ((x₁² - (2 * - r - - y₁) * - y₁) = (x₁² - (2 * r - y₁) * y₁)) as argeq;
      [lra|]; rewrite argeq; reflexivity|].

  set (θ1' := 2 * atan ((x₁ - Q') / (2 * (-r) - (-y₁))) + 2 * 1 * PI).
  assert (θ1 = -θ1') as t1rel. unfold θ1, θ1'.
  rewrite Q1rel.
  assert ((x₁ - Q) / (2 * - r - - y₁) = (- ((x₁ - Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  set (θ2' := 2 * PI).
  assert (θ2 = -θ2') as t2rel. unfold θ2, θ2'.
  field.

  rewrite tmid.
  rewrite t2rel, t1rel.
  enough (θ1' < θmax' /\ θmax' = θ2' /\ PI < θ1' < 2*PI )
    as [tmord [t1ord [t2ordlb t2ordub]]].
  lra.
  apply root_ordering_nxarm; try assumption.
  lra.
Qed.


Lemma root_ordering_Q3 :
  forall x₁ y₁ r 
         (rgt0 : 0 < r)
         (Q3 : y₁ < 0)
         (lf : x₁ <= 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in (* (-2*PI,-PI) *)
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) + 2 * IZR 1 * PI in (* (-PI,0) *)
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) in (* (0,PI) *)
    θ2 < θmax/2 + 2 * PI < θ1 /\  0 < θ2 < PI / 2 /\ PI < θ1 < 2*PI.
Proof.
  intros.

  specialize PI_RGT_0 as pirgt0.
  assert (2*PI >0) as tpigt0. lra.

  rename Q3 into y1lt0.

  assert (forall r, 0 <= r -> 0 < 2 * r - y₁) as lower. {
    intros s sge0.
    lra. }

  assert (forall r, 0 <= r -> x₁² < x₁² - (2 * r - y₁) * y₁ ) as inq. {
    intros s sge0.
    apply (Rplus_lt_reg_r (-x₁²)).
    setl 0. setr ((2 * s - y₁) * (-y₁)).
    apply Rmult_lt_0_compat; lra.
  }

  assert (forall r, 0 <= r -> 0 < x₁² - (2 * r - y₁) * y₁) as sqalb. {
    intros s sge0.
    apply (Rle_lt_trans _ (x₁²)).
    apply Rle_0_sqr.
    apply inq; try assumption.
  }
  

  assert (forall r,
             0 <= r -> (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) < 0)
    as xpos. {
    intros s sge0.
    specialize (sqalb s sge0).
    specialize (inq s sge0).
    specialize (lower s sge0).
    set (R := sqrt (x₁² - (2 * s - y₁) * y₁)) in *.
    apply (Rplus_lt_reg_r R). setr R. setl (x₁).
    unfold R.
    apply (Rle_lt_trans _ (-x₁)). lra.
    rewrite <- (sqrt_Rsqr (-x₁)) at 1; [| lra].
    rewrite <- Rsqr_neg.
    apply sqrt_lt_1;
      [apply Rle_0_sqr|left; assumption| assumption].
  }
  
  assert (PI < θ1 < 2*PI) as [t1lb t1ub]. {
    assert (0 <= r) as rge0. left. assumption.
    specialize (lower r rge0).

    assert (((x₁ - Q) / (2 * r - y₁)) < 0) as argpos.
    apply (Rmult_lt_reg_r (2 * r - y₁)); [ assumption|].
    setr 0. setl (x₁ - Q).
    intro; lra. apply (xpos r rge0).

    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.
    apply (Rplus_lt_compat_r (2* 1 *PI)) in argpos.
    rewrite Rplus_0_l in argpos.
    rewrite Rmult_assoc in argpos at 2.
    rewrite Rmult_1_l in argpos.
    change (θ1 < 2*PI) in argpos.

    specialize (atan_bound ((x₁ - Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atlb; [|lra].
    apply (Rplus_lt_compat_r (2*1*PI)) in atlb.
    assert (2 * (- PI / 2) + 2 * 1 * PI = PI) as id. field.
    rewrite id in atlb. clear id.
    split; assumption. }

  assert (0 < x₁ + Q) as xppos. {
    apply (Rplus_lt_reg_r (-x₁)). setr Q. setl (-x₁).
    unfold Q.
    rewrite <- (sqrt_Rsqr (-x₁)) at 1; [|lra].
    rewrite <- Rsqr_neg.
    assert (0 <= r) as rge0. left. assumption.

    specialize (sqalb r rge0).
    specialize (inq r rge0).

    apply sqrt_lt_1;
      [apply Rle_0_sqr|left; assumption| assumption].
  }
  
  assert (0 < θ2 < PI / 2) as [t2lb t2ub]. {
      
    assert (0 < ((x₁ + Q) / (2 * r - y₁))) as argpos.
    apply (Rmult_lt_reg_r ((2 * r - y₁))). lra.
    setr (x₁ + Q). intro ; lra. setl 0. lra.
    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.

    split; try assumption.
    unfold θ2.
    assert ((x₁ + Q) < (2 * r - y₁)) as numgt.
    unfold Q.
    apply (Rplus_lt_reg_r (-x₁)).
    setl (sqrt (x₁² - (2 * r - y₁) * y₁)).
    apply Rsqr_incrst_0; [|apply sqrt_pos|apply Rplus_le_le_0_compat; lra].
    rewrite Rsqr_sqrt; [|left; apply sqalb; left; assumption].
    rewrite Rsqr_plus.
    rewrite Rsqr_neg.
    apply (Rplus_lt_reg_r (-((- x₁)² - (2 * r - y₁) * y₁))).
    setl 0. setr ((2 * r - y₁)* 2 * ((r - x₁))).

    apply Rmult_lt_0_compat; lra.
    apply (Rmult_lt_reg_r (/2)).
    apply pos_half_prf.
    setr (PI / 4).
    setl (atan ((x₁ + Q) / (2 * r - y₁))).
    rewrite <- atan_1.
    apply atan_increasing.
    apply (Rmult_lt_reg_r (2 * r - y₁)). lra.
    setr (2 * r - y₁).
    setl (x₁ + Q).
    lra. assumption.
  }

  rename lf into lf'.
  destruct lf' as [lf|le].
  
  assert (-2 * PI < θmax < -PI) as [tmlb tbub]. {
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    specialize (atan2Q3 _ _ lf y1lt0) as at2rng.
    inversion_clear at2rng as [lb ub].
    apply (Rmult_lt_compat_l 2) in lb; [|lra].
    apply (Rmult_lt_compat_l 2) in ub; [|lra].
    assert (2 * - PI  = - 2 * PI) as id. field. rewrite id in *. clear id.
    assert (2 * - (PI/2)  = - PI) as id. field. rewrite id in *. clear id.
    split; assumption.
  }
  
  split; [| split; split; assumption].

  split.
  apply (Rlt_trans _ (PI/2)); try assumption.
  apply (Rplus_lt_reg_r (-2*PI)).
  setl (-3*PI/2).
  unfold θmax, calcθ₁. rewrite cos_0, sin_0.
  fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
  fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
  setr (atan2 y₁ x₁).
  apply (Rlt_trans _ (-PI)).
  lra.
  apply atan2_bound.
  intros [x1eq0 y1eq0]. subst. clear - lf. lra.

  unfold θ1.
  apply (Rplus_lt_reg_r (-2*PI)).
  unfold θmax, calcθ₁. rewrite cos_0, sin_0.
  fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
  fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
  setl (atan2 y₁ x₁).
  setr (2 * atan ((x₁ - Q) / (2 * r - y₁))).

  set (g := (fun r => 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁)))).
  change (atan2 y₁ x₁ < g r).

  set (g' :=
         (fun r =>
            2 * (((2 * r - y₁) * y₁ / sqrt (x₁² - ((2 * r - y₁) * y₁))
                  - 2*(x₁ - sqrt (x₁² - ((2 * r - y₁) * y₁))))
          / ((2 * r - y₁)² + (x₁ - sqrt (x₁² - ((2 * r - y₁) * y₁)))²)))).

  
  (* set (g' := *)
  (*        -(-2*x₁² + (2*r-y₁)*y₁ + 2*x₁*sqrt (x₁² - (2 * r - y₁) * y₁)) *)
  (*           / (sqrt (x₁² - (2 * r - y₁) * y₁) * 
                 (2*r^2 + x₁² - 3 * r * y₁ + y₁²) *)
  (*              - x₁*(x₁² - (2 * r - y₁) * y₁))). *)
  assert (forall r,
             (2 * r - y₁)² + (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))² <> 0)
    as ssq.
  intros s. intro ssq.
  apply Rplus_sqr_eq_0 in ssq.
  destruct ssq as [att atc].
  apply (Rmult_eq_compat_r (-1)) in atc.
  assert (-x₁ + sqrt (x₁² - (2 * s - y₁) * y₁) = 0) as atc2.
  rewrite Rmult_0_l in atc.
  rewrite <- atc. field.
  rewrite Rplus_comm in atc2.
  generalize atc2.
  apply tech_Rplus; [apply sqrt_pos| lra]. 

  assert (forall r, 0 <= r -> is_derive g r (g' r)) as gisder. {
    intros s sge0.
    unfold g, g'. auto_derive.
    split; [|split; auto].
    specialize (sqalb s sge0).
    setr (x₁² - (2 * s - y₁) * y₁).
    assumption.
    specialize (lower s sge0).
    intro; lra.
    fieldrewrite (x₁² + - ((2 * s + - y₁) * y₁))
                 (x₁² - ((2 * s - y₁) * y₁)).
    
    assert (1 +
            (x₁ + - sqrt (x₁² - ((2 * s - y₁) * y₁))) *
            / (2 * s + - y₁) *
            ((x₁ + - sqrt (x₁² - ((2 * s - y₁) * y₁))) *
             / (2 * s + - y₁) * 1) =
            ((2 * s - y₁)² + (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))²)
              /(2 * s - y₁)²) as denid.
    apply (Rmult_eq_reg_r ((2 * s - y₁)²)).
    setr ((2 * s - y₁)² + (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))²).
    intro. lra.
    setl ((2 * s - y₁)² +
          (x₁ + - sqrt (x₁² - ((2 * s - y₁) * y₁))) *
          ((x₁ + - sqrt (x₁² - ((2 * s - y₁) * y₁))) )) .
    intro. lra.
    unfold Rsqr.
    field.
    intro Argsqrne0.
    apply Rsqr_eq_0 in Argsqrne0.
    lra.
    rewrite denid. clear denid.
    rewrite Rinv_Rdiv;
      [|apply (ssq s) |intro trmy; apply Rsqr_eq_0 in trmy;
                       specialize (lower s sge0);
                       lra].
    
    apply (Rmult_eq_reg_r
             ((2 * s - y₁)² + (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))²));
      try assumption.
    setl (2 *
          ((- (- (2 * 1 * y₁) * / (2 * sqrt (x₁² - (2 * s - y₁) * y₁))) *
              ((2 * s - y₁)) + (x₁ + - sqrt (x₁² - (2 * s - y₁) * y₁)) *
                               (- (2 * 1) )))).
    repeat split; try intro; try lra.
    apply sqrt_eq_0 in H. unfold Rsqr in sqalb.
    specialize (sqalb s sge0).
    clear - sqalb H. lra.
    specialize (sqalb s sge0).
    left. assumption.
    change ((2 * s - y₁)² +
            (x₁ - sqrt (x₁ * x₁ - (2 * s - y₁) * y₁))² = 0) in H.
    specialize (ssq s).
    auto.
    setr (2 *
          (((2 * s - y₁) * y₁ / sqrt (x₁² - (2 * s - y₁) * y₁) -
            2 * (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))))).
    repeat split; try intro; try lra.
    specialize (sqalb s sge0).
    apply sqrt_eq_0 in H; unfold Rsqr in sqalb; lra.
    change ((2 * s - y₁)² +
            (x₁ - sqrt (x₁ * x₁ - (2 * s - y₁) * y₁))² = 0) in H.
    specialize (ssq s). auto.
    field.
    specialize (sqalb s sge0).
    intro sne0. apply sqrt_eq_0 in sne0; lra.
    apply (ssq s). }

  (* show: sign g' r = sign (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))² = 1
     because of the ² *)
  
  assert (forall r, 0 <= r -> sign (g' r) = 1) as sgng'. {
    intros s sge0.
    unfold g'.
    rewrite sign_mult.
    rewrite sign_eq_pos_den;
      [|
       specialize (Rle_0_sqr (2 * s - y₁)) as trmy1;
       destruct trmy1 as [zlt2rmy1 |zeq2rmy1];
       [|exfalso; symmetry in zeq2rmy1; apply Rsqr_eq_0 in zeq2rmy1;lra ];
       specialize (Rle_0_sqr (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))) as x1mQge0;
       apply Rplus_lt_le_0_compat; try assumption].
    assert (0 < 2) as zlt2; [lra|].
    rewrite (sign_eq_1 _ zlt2).
    rewrite Rmult_1_l.
    apply sign_eq_1.

    apply (Rmult_lt_reg_r (sqrt (x₁² - (2 * s - y₁) * y₁)));
      [apply sqrt_lt_R0; apply sqalb; assumption|
       setl 0; rewrite Rmult_minus_distr_r].
    setr ((2 * s - y₁) * y₁
          + - 2 * (x₁* sqrt (x₁² - (2 * s - y₁) * y₁)
                 - (sqrt (x₁² - (2 * s - y₁) * y₁) *
                    sqrt (x₁² - (2 * s - y₁) * y₁)))).
    intro.
    rewrite <- sqrt_0 in H.
    apply sqrt_inj in H.
    specialize (sqalb s sge0). unfold Rsqr in sqalb.
    rewrite H in sqalb.
    clear - sqalb. lra.
    left. apply (sqalb); try assumption. right; reflexivity.

    rewrite sqrt_def;
      [|left; apply (sqalb); try assumption].
    setr (2 * (- x₁) * - (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))
          + (2 * s - y₁) * - y₁).
    apply Rplus_lt_0_compat.
    apply Rmult_lt_0_compat.
    apply Rmult_lt_0_compat. assumption. lra.
    specialize (xpos s sge0). lra.
    apply Rmult_lt_0_compat.
    specialize (lower s sge0). assumption. lra.
  }

  assert (y₁ <> 0) as y1ne0. intro. lra.
  assert (x₁ <> 0) as x1ne0. intro. lra.
  rewrite <- (theta1_req0_thetamax _ _ x1ne0 y1ne0).
  rewrite <- Rsqr_pow2.
  change (g 0 < g r).

  assert (forall r, 0 <= r -> Derive g r = g' r) as Derdef. {
    intros.
    specialize (gisder r0 H).
    apply is_derive_unique in gisder.
    assumption.
  }

  eapply (incr_function_le g 0 r g').
  intros. apply gisder; try assumption.
  intros.
  setoid_rewrite signeq1_eqv in sgng'.
  apply sgng'. assumption. right. reflexivity.
  assumption. right. reflexivity.
 
  split; try lra.
  unfold θmax, calcθ₁. rewrite cos_0, sin_0.
  fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
  fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
  fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).
  unfold θ1, θ2, Q in *.
  
  rewrite le in *.
  rewrite atan2_mPI2; try assumption.
  fieldrewrite (- PI / 2 + 2 * PI) (3* PI / 2).
  split. lra.
  rewrite Rsqr_0, Rminus_0_l, Rminus_0_l.
  fieldrewrite (- ((2 * r - y₁) * y₁)) ((2 * r - y₁) * (-y₁)).
  rewrite sqrt_mult; [|left; apply lower; left; assumption|left; lra].
  rewrite <- (sqrt_def (2 * r - y₁)) at 2; [|left; apply lower; left; lra].

  fieldrewrite (- (sqrt (2 * r - y₁) * sqrt (- y₁))
                    /(sqrt (2 * r - y₁) * sqrt (2 * r - y₁)))
               (- (( sqrt (- y₁)) / (sqrt (2 * r - y₁)))).
  intro.
  assert ((2 * r - y₁) = 0) as csq.
  apply sqrt_eq_0. left. apply lower. left. assumption. assumption.
  assert (0 <= r) as rge0. left. assumption.
  specialize (lower _ rge0).
  rewrite csq in lower.
  clear - lower. lra. rewrite atan_opp.
  apply (Rle_lt_trans _ (2 * - (PI/4) + 2 * 1 * PI)). lra.
  rewrite <- atan_1.
  apply (Rplus_lt_reg_r (- 2*1*PI)).
  apply (Rmult_lt_reg_r (/2)).
  apply pos_half_prf.
  setl ( - atan 1).
  setr (- atan (sqrt (- y₁) / sqrt (2 * r - y₁))).
  apply Ropp_lt_contravar.
  apply atan_increasing.
  apply (Rmult_lt_reg_r (sqrt (2 * r - y₁))).
  apply sqrt_lt_R0. apply lower. left. assumption.
  setl (sqrt (-y₁)).

  intro.
  assert ((2 * r - y₁) = 0) as csq.
  apply sqrt_eq_0. left. apply lower. left. assumption. assumption.
  assert (0 <= r) as rge0. left. assumption.
  specialize (lower _ rge0).
  rewrite csq in lower.
  clear - lower. lra.
  rewrite Rmult_1_l.
  apply sqrt_lt_1. left. lra.
  left. apply lower. left. assumption.
  lra.
Qed.

Lemma root_ordering_Q2_rneg :
  forall x₁ y₁ r 
         (rgt0 : r < 0)
         (Q3 : 0 < y₁)
         (lf : x₁ <= 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) - 2 * IZR 1 * PI in
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) in 
    θ1 < θmax/2 - 2 * PI < θ2 /\  -PI/2 < θ2 < 0 /\ -2*PI < θ1 < -PI.
Proof.
  intros.

  apply straight_symmetry in phase.
  assert (0 < (-r)) as rgt0';[ lra|].
  rewrite Ropp_0 in phase.

  assert (θmax = - calcθ₁ 0 0 0 x₁ (-y₁)) as tmid.
  unfold θmax, calcθ₁ in *. clear θmax.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert (- (x₁ - 0) * sin 0 + (- y₁ - 0) * cos 0 = - y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (- y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  rewrite atan2_symmetry. lra.
  intro sc. destruct sc as [scx scy]. lra.
  rewrite tmid.
  set (θmax' := calcθ₁ 0 0 0 x₁ (- y₁)) in *.

  set (Q' := sqrt (x₁² - (2 * (-r) - (-y₁)) * (-y₁))) in *.
  assert (Q' = Q) as Q1rel;
    [ unfold Q, Q';
      assert ((x₁² - (2 * - r - - y₁) * - y₁) = (x₁² - (2 * r - y₁) * y₁)) as argeq;
      [lra|]; rewrite argeq; reflexivity|].

  set (θ1' := 2 * atan ((x₁ - Q') / (2 * (-r) - (-y₁)))  + 2 * 1 * PI).
  assert (θ1 = -θ1') as t1rel. unfold θ1, θ1'.
  rewrite Q1rel.
  assert ((x₁ - Q) / (2 * - r - - y₁) = (- ((x₁ - Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  set (θ2' := 2 * atan ((x₁ + Q') / (2 * (-r) - (-y₁)))).
  assert (θ2 = -θ2') as t2rel. unfold θ2, θ2'.
  rewrite Q1rel.
  assert ((x₁ + Q) / (2 * - r - - y₁) = (- ((x₁ + Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  rewrite t2rel, t1rel.
  enough (θ2' < θmax'/2 + 2*PI < θ1' /\ 0 < θ2' < PI/2 /\ PI < θ1' < 2* PI)
    as [[tmordlb tmordub] [[t1ordlb t1ordub] [t2ordlb t2ordub]]].
  lra.
  apply root_ordering_Q3; try assumption.
  lra.
Qed.


Lemma root_ordering_Q4:
  forall x₁ y₁ r 
         (rgt0 : 0 < r)
         (Q4 : y₁ < 0)
         (rt : 0 <= x₁)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in (* (-PI,0) *)
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) + 2 * IZR 1 * PI in (*(-PI/2,0)*)
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) in (*(0,PI)*)
    θ2 < θmax/2 + 2 * PI < θ1 /\ 0 < θ2 < PI /\ 3*PI/2 < θ1 < 2*PI.
Proof.
  intros.

  specialize PI_RGT_0 as pirgt0.
  assert (2*PI >0) as tpigt0. lra.

  rename Q4 into y1lt0.

  
  assert (forall r, 0 <= r -> 0 < 2 * r - y₁) as lower. {
    intros s sgt0.
    lra. }

  assert (forall r, 0 <= r -> x₁² < x₁² - (2 * r - y₁) * y₁ ) as inq. {
    intros s sgt0.
    apply (Rplus_lt_reg_r (-x₁²)).
    setl 0. setr ((2 * s - y₁) * (-y₁)).
    apply Rmult_lt_0_compat; lra.
  }

  assert (forall r, 0 <= r -> 0 < x₁² - (2 * r - y₁) * y₁) as sqalb. {
    intros s sgt0.
    apply (Rle_lt_trans _ (x₁²)).
    apply Rle_0_sqr.
    apply inq; try assumption.
  }
  
  assert (forall r,
             0 <= r -> (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) < 0)
    as xpos. {
    intros s sgt0.
    specialize (sqalb s sgt0).
    specialize (inq s sgt0).
    specialize (lower s sgt0).
    set (R := sqrt (x₁² - (2 * s - y₁) * y₁)) in *.
    apply (Rplus_lt_reg_r R). setr R. setl (x₁).
    unfold R.

    rewrite <- Rabs_right ; [|apply Rle_ge; apply sqrt_pos].
    rewrite <- (Rabs_right x₁) at 1; [| lra].
    apply Rsqr_lt_abs_0.
    rewrite Rsqr_sqrt; [ assumption | left; assumption].
  }
  
  assert (3*PI/2 < θ1 < 2*PI) as [t1lb t1ub]. {
    assert (0 <= r) as rge0. lra.
    specialize (lower r rge0).

    assert (((x₁ - Q) / (2 * r - y₁)) < 0) as argpos. {
    apply (Rmult_lt_reg_r (2 * r - y₁)); [ assumption|].
    setr 0. setl (x₁ - Q).
    intro; lra. apply (xpos r rge0). }

    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.
    apply (Rplus_lt_compat_r (2* 1 *PI)) in argpos.
    rewrite Rplus_0_l in argpos.
    rewrite Rmult_assoc in argpos at 2.
    rewrite Rmult_1_l in argpos.
    change (θ1 < 2*PI) in argpos.

    assert (- 1 < ((x₁ - Q) / (2 * r - y₁))) as argpos2. {
    apply (Rmult_lt_reg_r (2 * r - y₁)); [ assumption|].
    setr (x₁ - Q). intro; lra.
    setl (- (2 * r - y₁)). unfold Q.
    unfold Q.
    apply (Rplus_lt_reg_r ((2 * r - y₁) + sqrt (x₁² - (2 * r - y₁) * y₁))).
    setl (sqrt (x₁² - (2 * r - y₁) * y₁)).
    setr (x₁ + (2 * r - y₁)).
    rewrite <- Rabs_pos_eq; [ |left; apply Rplus_le_lt_0_compat ; assumption].    
    rewrite <- Rabs_pos_eq at 1; [ |apply sqrt_pos].
    apply Rsqr_lt_abs_0.
    rewrite Rsqr_sqrt; [|left; auto].
    apply (Rplus_lt_reg_r (- x₁²)).
    apply (Rmult_lt_reg_r (/ (2 * r - y₁))).
    apply Rinv_0_lt_compat; try assumption.
    setr ((2 * r - y₁) + 2 * x₁). intro ; lra.
    setl (- y₁). intro; lra. lra.
    }

    apply atan_increasing in argpos2.
    assert (-1 = Ropp 1) as id. field. rewrite id in argpos2. clear id.
    rewrite atan_opp in argpos2.
    rewrite atan_1 in argpos2.

    apply (Rmult_lt_compat_l 2) in argpos2.
    apply (Rplus_lt_compat_r (2*1*PI)) in argpos2.
    assert (2 * - (PI / 4) + 2 * 1 * PI = 3 *PI/2) as id.
    field. rewrite id in argpos2. clear id.
    split; assumption. lra. }

  assert (0 < x₁ + Q) as xppos. {
    apply Rplus_le_lt_0_compat; try assumption.
    unfold Q.
    apply sqrt_lt_R0.
    setr (x₁² + (2 * r - y₁) * - y₁).
    apply Rplus_le_lt_0_compat; try assumption.
    apply Rle_0_sqr.
    apply Rmult_lt_0_compat.
    apply lower. left. assumption.
    lra. }

  assert (0 < θ2 < PI) as [t2lb t2ub]. {
      
    assert (0 < ((x₁ + Q) / (2 * r - y₁))) as argpos.
    apply (Rmult_lt_reg_r ((2 * r - y₁))). lra.
    setr (x₁ + Q). intro ; lra. setl 0. lra.
    apply atan_increasing in argpos.
    rewrite atan_0 in argpos.
    apply (Rmult_lt_compat_l 2) in argpos; [|lra].
    rewrite Rmult_0_r in argpos.
    
    specialize (atan_bound ((x₁ + Q) / (2 * r - y₁))) as [atlb atub].
    apply (Rmult_lt_compat_l 2) in atub; [|lra].
    assert (2 * ( PI / 2) =  PI) as id. field.
    rewrite id in atub. clear id.

    unfold θ2.
    split; assumption. }

  rename rt into rt'.
  destruct rt' as [rt | req ].
  
  assert (- PI < θmax < 0) as [tmlb tbub]. {
    unfold θmax, calcθ₁. rewrite cos_0, sin_0.
    fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
    fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
    specialize (atan2Q4 _ _ rt y1lt0) as at2rng.
    inversion_clear at2rng as [lb ub].
    apply (Rmult_lt_compat_l 2) in lb; [|lra].
    apply (Rmult_lt_compat_l 2) in ub; [|lra].
    assert (2 * - (PI/2)  = - PI) as id. field. rewrite id in *. clear id.
    rewrite Rmult_0_r in ub.
    split; assumption.
  }
  
  split; [| split; split; assumption].
  
  split.
  lra.
  unfold θ1.
  apply (Rplus_lt_reg_r (-2*PI)).
  setl (θmax / 2). setr (2 * atan ((x₁ - Q) / (2 * r - y₁))).
  assert (θmax / 2 = atan2 y₁ x₁) as tm2def. {
  unfold θmax, calcθ₁. rewrite cos_0, sin_0.
  fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
  fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
  field. }
  apply (Rmult_lt_compat_r (/2)) in tmlb ; [|apply Rinv_0_lt_compat; lra].
  apply (Rmult_lt_compat_r (/2)) in tbub ; [|apply Rinv_0_lt_compat; lra].
  repeat rewrite <- Rinv_eqv in tmlb, tbub.
  assert (0/2 = 0) as id; [lra|rewrite id in tbub; clear id].
  rewrite tm2def in *. clear tm2def.

  set (g := (fun r => 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁)))).
  change (atan2 y₁ x₁ < g r).

  set (g' :=
         (fun r =>
            2 * (((2 * r - y₁) * y₁ / sqrt (x₁² - ((2 * r - y₁) * y₁))
                  - 2*(x₁ - sqrt (x₁² - ((2 * r - y₁) * y₁))))
          / ((2 * r - y₁)² + (x₁ - sqrt (x₁² - ((2 * r - y₁) * y₁)))²)))).

  
  (* set (g' := *)
  (*        -(-2*x₁² + (2*r-y₁)*y₁ + 2*x₁*sqrt (x₁² - (2 * r - y₁) * y₁)) *)
  (*           / (sqrt (x₁² - (2 * r - y₁) * y₁) * 
                 (2*r^2 + x₁² - 3 * r * y₁ + y₁²) *)
  (*              - x₁*(x₁² - (2 * r - y₁) * y₁))). *)
  assert (forall r, 0 <= r -> 
             (2 * r - y₁)² + (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))² <> 0)
    as ssq.
  intros s snneg. intro ssq.
  apply Rplus_sqr_eq_0 in ssq.
  destruct ssq as [att atc].
  assert (y₁ = 2*s) as y1def. {
    apply (Rplus_eq_reg_r (-y₁)).
    setl 0. setr (2 * s - y₁).
    auto. }
  rewrite y1def in y1lt0.
  clear - snneg y1lt0.
  lra.

  assert (forall r, 0 <= r -> is_derive g r (g' r)) as gisder. {
    intros s sgt0. 
    unfold g, g'. auto_derive.
    split; [|split; auto].
    specialize (sqalb s sgt0).
    setr (x₁² - (2 * s - y₁) * y₁).
    assumption.
    specialize (lower s sgt0).
    intro; lra.
    fieldrewrite (x₁² + - ((2 * s + - y₁) * y₁))
                 (x₁² - ((2 * s - y₁) * y₁)).
    
    assert (1 +
            (x₁ + - sqrt (x₁² - ((2 * s - y₁) * y₁))) *
            / (2 * s + - y₁) *
            ((x₁ + - sqrt (x₁² - ((2 * s - y₁) * y₁))) *
             / (2 * s + - y₁) * 1) =
            ((2 * s - y₁)² + (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))²)
              /(2 * s - y₁)²) as denid.
    apply (Rmult_eq_reg_r ((2 * s - y₁)²)).
    setr ((2 * s - y₁)² + (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))²).
    intro. lra.
    setl ((2 * s - y₁)² +
          (x₁ + - sqrt (x₁² - ((2 * s - y₁) * y₁))) *
          ((x₁ + - sqrt (x₁² - ((2 * s - y₁) * y₁))) )) .
    intro. lra.
    unfold Rsqr.
    field.
    intro Argsqrne0.
    apply Rsqr_eq_0 in Argsqrne0.
    lra.
    rewrite denid. clear denid.
    rewrite Rinv_Rdiv;
      [|apply (ssq s sgt0) |intro trmy; apply Rsqr_eq_0 in trmy;
                       specialize (lower s sgt0);
                       lra].
    
    apply (Rmult_eq_reg_r
             ((2 * s - y₁)² + (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))²));
      try assumption.
    setl (2 *
          ((- (- (2 * 1 * y₁) * / (2 * sqrt (x₁² - (2 * s - y₁) * y₁))) *
              ((2 * s - y₁)) + (x₁ + - sqrt (x₁² - (2 * s - y₁) * y₁)) *
                               (- (2 * 1) )))).
    repeat split; try intro; try lra.
    apply sqrt_eq_0 in H. unfold Rsqr in sqalb.
    specialize (sqalb s sgt0).
    clear - sqalb H. lra.
    specialize (sqalb s sgt0).
    left. assumption.
    change ((2 * s - y₁)² +
            (x₁ - sqrt (x₁ * x₁ - (2 * s - y₁) * y₁))² = 0) in H.
    specialize (ssq s sgt0).
    auto.
    setr (2 *
          (((2 * s - y₁) * y₁ / sqrt (x₁² - (2 * s - y₁) * y₁) -
            2 * (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))))).
    repeat split; try intro; try lra.
    specialize (sqalb s sgt0).
    apply sqrt_eq_0 in H; unfold Rsqr in sqalb; lra.
    change ((2 * s - y₁)² +
            (x₁ - sqrt (x₁ * x₁ - (2 * s - y₁) * y₁))² = 0) in H.
    specialize (ssq s sgt0). auto.
    field.
    specialize (sqalb s sgt0).
    intro sne0. apply sqrt_eq_0 in sne0; lra.
    apply (ssq s sgt0). }

  (* show: sign g' r = sign (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))² = 1
     because of the ² *)
  
  assert (forall r, 0 <= r -> sign (g' r) = 1) as sgng'. {
    intros s sgt0.
    unfold g'.
    rewrite sign_mult.
    rewrite sign_eq_pos_den;
      [|
       specialize (Rle_0_sqr (2 * s - y₁)) as trmy1;
       destruct trmy1 as [zlt2rmy1 |zeq2rmy1];
       [|exfalso; symmetry in zeq2rmy1; apply Rsqr_eq_0 in zeq2rmy1;lra ];
       specialize (Rle_0_sqr (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))) as x1mQge0;
       apply Rplus_lt_le_0_compat; try assumption].
    assert (0 < 2) as zlt2; [lra|].
    rewrite (sign_eq_1 _ zlt2).
    rewrite Rmult_1_l.
    apply sign_eq_1.

    apply (Rmult_lt_reg_r (sqrt (x₁² - (2 * s - y₁) * y₁)));
      [apply sqrt_lt_R0; apply sqalb; assumption|
       setl 0; rewrite Rmult_minus_distr_r].
    setr ((2 * s - y₁) * y₁
          + - 2 * (x₁* sqrt (x₁² - (2 * s - y₁) * y₁)
                 - (sqrt (x₁² - (2 * s - y₁) * y₁) *
                    sqrt (x₁² - (2 * s - y₁) * y₁)))).
    intro.
    rewrite <- sqrt_0 in H.
    apply sqrt_inj in H.
    specialize (sqalb s sgt0). unfold Rsqr in sqalb.
    rewrite H in sqalb.
    clear - sqalb. lra.
    left. apply (sqalb); try assumption. right; reflexivity.

    rewrite Rmult_minus_distr_l.
    assert (-2 = -(2)) as id. field. rewrite id at 2. clear id.
    rewrite Ropp_mult_distr_l_reverse.
    assert (2 * (sqrt (x₁² - (2 * s - y₁) * y₁) * sqrt (x₁² - (2 * s - y₁) * y₁)) =
            (sqrt (x₁² - (2 * s - y₁) * y₁) * sqrt (x₁² - (2 * s - y₁) * y₁)) + 
            (x₁² - (2 * s - y₁) * y₁)) as id.
    rewrite sqrt_def; [field| left; apply (sqalb s sgt0)].
    rewrite id. clear id.
    setr ((x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))*(x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))).
    change (0 < (x₁ - sqrt (x₁² - (2 * s - y₁) * y₁))²).
    specialize (xpos s sgt0).
    clear - xpos.
    apply Rlt_0_sqr.
    intro. rewrite H in xpos. clear - xpos.
    lra.  }

  assert (y₁ <> 0) as y1ne0. intro. lra.
  assert (x₁ <> 0) as x1ne0. intro. lra.
  rewrite <- (theta1_req0_thetamax _ _ x1ne0 y1ne0).
  rewrite <- Rsqr_pow2.
  change (g 0 < g r).

  assert (forall r, 0 <= r -> Derive g r = g' r) as Derdef. {
    intros.
    specialize (gisder r0 H).
    apply is_derive_unique in gisder.
    assumption.
  }

  eapply (incr_function_le g 0 r g').
  intros. apply gisder; try assumption.
  intros.
  setoid_rewrite signeq1_eqv in sgng'.
  apply sgng'. assumption. right. reflexivity.
  assumption. right. reflexivity.

  split; try lra.
  unfold θmax, calcθ₁. rewrite cos_0, sin_0.
  fieldrewrite (- (x₁ - 0) * 0 + (y₁ - 0) * 1) (y₁).
  fieldrewrite ((x₁ - 0) * 1 + (y₁ - 0) * 0) (x₁).
  fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).
  unfold θ1, θ2, Q in *.
  
  rewrite <- req in *.
  rewrite atan2_mPI2; try assumption.
  fieldrewrite (- PI / 2 + 2 * PI) (3* PI / 2).
  split. lra.
  rewrite Rsqr_0, Rminus_0_l, Rminus_0_l.
  fieldrewrite (- ((2 * r - y₁) * y₁)) ((2 * r - y₁) * (-y₁)).
  rewrite sqrt_mult; [|left; apply lower; left; assumption|left; lra].
  rewrite <- (sqrt_def (2 * r - y₁)) at 2; [|left; apply lower; left; lra].

  fieldrewrite (- (sqrt (2 * r - y₁) * sqrt (- y₁))
                    /(sqrt (2 * r - y₁) * sqrt (2 * r - y₁)))
               (- (( sqrt (- y₁)) / (sqrt (2 * r - y₁)))).
  intro.
  assert ((2 * r - y₁) = 0) as csq.
  apply sqrt_eq_0. left. apply lower. left. assumption. assumption.
  assert (0 <= r) as rge0. left. assumption.
  specialize (lower _ rge0).
  rewrite csq in lower.
  clear - lower. lra. rewrite atan_opp.
  apply (Rle_lt_trans _ (2 * - (PI/4) + 2 * 1 * PI)). lra.
  rewrite <- atan_1.
  apply (Rplus_lt_reg_r (- 2*1*PI)).
  apply (Rmult_lt_reg_r (/2)).
  apply pos_half_prf.
  setl ( - atan 1).
  setr (- atan (sqrt (- y₁) / sqrt (2 * r - y₁))).
  apply Ropp_lt_contravar.
  apply atan_increasing.
  apply (Rmult_lt_reg_r (sqrt (2 * r - y₁))).
  apply sqrt_lt_R0. apply lower. left. assumption.
  setl (sqrt (-y₁)).

  intro.
  assert ((2 * r - y₁) = 0) as csq.
  apply sqrt_eq_0. left. apply lower. left. assumption. assumption.
  assert (0 <= r) as rge0. left. assumption.
  specialize (lower _ rge0).
  rewrite csq in lower.
  clear - lower. lra.
  rewrite Rmult_1_l.
  apply sqrt_lt_1. left. lra.
  left. apply lower. left. assumption.
  lra.
Qed.



Lemma root_ordering_Q1_rneg:
  forall x₁ y₁ r 
         (rgt0 : r < 0)
         (Q4 : 0 < y₁)
         (rt : 0 <= x₁)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in (* (-PI,0) *)
    let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
    let θ1 := 2 * atan ((x₁ - Q)/(2 * r - y₁)) - 2 * IZR 1 * PI in
    let θ2 := 2 * atan ((x₁ + Q)/(2 * r - y₁)) in
    θ1 < θmax/2 - 2 * PI < θ2 /\ -PI < θ2 < 0 /\ -2*PI < θ1 < -3*PI/2.
Proof.
  intros.

  apply straight_symmetry in phase.
  assert (0 < (-r)) as rgt0';[ lra|].
  rewrite Ropp_0 in phase.

  assert (θmax = - calcθ₁ 0 0 0 x₁ (-y₁)) as tmid.
  unfold θmax, calcθ₁ in *. clear θmax.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert (- (x₁ - 0) * sin 0 + (- y₁ - 0) * cos 0 = - y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (- y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  rewrite atan2_symmetry. lra.
  intro sc. destruct sc as [scx scy]. lra.
  rewrite tmid.
  set (θmax' := calcθ₁ 0 0 0 x₁ (- y₁)) in *.

  set (Q' := sqrt (x₁² - (2 * (-r) - (-y₁)) * (-y₁))) in *.
  assert (Q' = Q) as Q1rel;
    [ unfold Q, Q';
      assert ((x₁² - (2 * - r - - y₁) * - y₁) = (x₁² - (2 * r - y₁) * y₁)) as argeq;
      [lra|]; rewrite argeq; reflexivity|].

  set (θ1' := 2 * atan ((x₁ - Q') / (2 * (-r) - (-y₁))) + 2 * 1 * PI).
  assert (θ1 = -θ1') as t1rel. unfold θ1, θ1'.
  rewrite Q1rel.
  assert ((x₁ - Q) / (2 * - r - - y₁) = (- ((x₁ - Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  set (θ2' := 2 * atan ((x₁ + Q') / (2 * (-r) - (-y₁)))).
  assert (θ2 = -θ2') as t2rel. unfold θ2, θ2'.
  rewrite Q1rel.
  assert ((x₁ + Q) / (2 * - r - - y₁) = (- ((x₁ + Q) / (2 * r - y₁)))).
  field. split; lra. rewrite H.
  rewrite atan_opp. field.

  rewrite t2rel, t1rel.
  enough (θ2' < θmax'/2 + 2*PI < θ1' /\ 0 < θ2' < PI /\ 3*PI/2 < θ1' < 2* PI)
    as [[tmordlb tmordub] [[t1ordlb t1ordub] [t2ordlb t2ordub]]].
  lra.
  apply root_ordering_Q4; try assumption.
  lra.
Qed.

(** We define functions θ1 and θ2 that compute an angular location on
a circle of radius r, such that the line connecting that point with a
point (x₁, y₁) is tangent to the circle. Without loss of generality,
we consider a circle centered at (0,r). *)

Definition θ1 x₁ y₁ r : R :=
  let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
  match (total_order_T 0 r) with
  | inleft (left _) => (* 0 < r *)
    match (total_order_T 0 x₁, total_order_T 0 y₁) with

    | (inleft (left _), inleft (left _))   => (* 0 < x₁, 0 < y₁, Q1 *)
      match (total_order_T 0 (2 * r - y₁)) with
      | inleft (left _) => 2 * atan ((x₁ - Q)/(2 * r - y₁))
      | inleft (right _) => 2 * atan (y₁/(2 * x₁))
      | inright _ => 2 * atan ((x₁ - Q)/(2 * r - y₁))
      end
    | (inleft (right _), inleft (left _))   => (* 0 = x₁, 0 < y₁, Q1 *)
      match (total_order_T 0 (2 * r - y₁)) with
      | inleft (left _) => 2 * atan ((x₁ - Q)/(2 * r - y₁))
      | inleft (right _) => PI
      | inright _ => 2 * atan ((x₁ - Q)/(2 * r - y₁))
      end

    | (inleft (left _), inleft (right _))  => (* 0 < x₁, 0 = y₁ *)
      0
    | (inleft _, inright _)         => (* 0 <= x₁, 0 > y₁, Q4 *)
      2 * atan ((x₁ - Q)/(2 * r - y₁)) + 2 * IZR 1 * PI
    | (inleft (right _), inleft (right _)) => (* 0 = x₁, 0 = y₁ *)
      0
    | (inright _, inleft (left _))         => (* 0 > x₁, 0 < y₁, Q2 *)
      match (total_order_T 0 (2 * r - y₁)) with
      | inleft (left _) =>
        2 * atan ((x₁ - Q)/(2 * r - y₁)) + 2 * IZR 1 * PI (* 2 * r - y₁ > 0 *)
      | inleft (right _) => PI (* 2 * r - y₁ = 0 *)
      | inright _ => 2 * atan ((x₁ - Q)/(2 * r - y₁)) (* 2 * r - y₁ < 0 *)
      end
    | (inright _, inleft (right _))        => (* 0 > x₁, 0 = y₁ *)
      2 * atan ((x₁ - Q)/(2 * r - y₁)) + 2 * IZR 1 * PI
    | (inright _, inright _)               => (* 0 > x₁, 0 > y₁, Q3 *)
      2 * atan ((x₁ - Q)/(2 * r - y₁)) + 2 * IZR 1 * PI
    end
  | inleft (right _) => (* 0 = r *) 0 (* atan2 y x *)
  | inright _ => (* 0 > r *)
    match (total_order_T 0 x₁, total_order_T 0 y₁) with
    | (inleft _, inleft (left _) )  => (* 0 <= x₁, 0 < y₁, Q1 *)
      2 * atan ((x₁ - Q)/(2 * r - y₁)) - 2 * IZR 1 * PI
    | (inleft (left _), inleft (right _))  => (* 0 < x₁, 0 = y₁ *)
      0
    | (inleft (left _), inright _)         => (* 0 < x₁, 0 > y₁, Q4 *)
      match (total_order_T 0 (2 * r - y₁)) with
      | inleft (left _) => 2 * atan ((x₁ - Q)/(2 * r - y₁)) (* 0 < 2 * r - y₁ *)
      | inleft (right _) => 2 * atan (y₁/(2 * x₁)) (* 0 = 2 * r - y₁ *)
      | inright _ => 2 * atan ((x₁ - Q)/(2 * r - y₁)) (* 0 > 2 * r - y₁ *)
      end
    | (inleft (right _), inright _)         => (* 0 = x₁, 0 > y₁, Q4 *)
      match (total_order_T 0 (2 * r - y₁)) with
      | inleft (left _) => 2 * atan ((x₁ - Q)/(2 * r - y₁)) (* 0 < 2 * r - y₁ *)
      | inleft (right _) => - PI (* 0 = 2 * r - y₁ *)
      | inright _ => 2 * atan ((x₁ - Q)/(2 * r - y₁)) (* 0 > 2 * r - y₁ *)
      end
    | (inleft (right _), inleft (right _)) => (* 0 = x₁, 0 = y₁ *)
      0
    | (inright _, inleft (left _))         => (* 0 > x₁, 0 < y₁, Q2 *)
      2 * atan ((x₁ - Q)/(2 * r - y₁)) - 2 * IZR 1 * PI
    | (inright _, inleft (right _))        => (* 0 > x₁, 0 = y₁ *)
      2 * atan ((x₁ - Q)/(2 * r - y₁)) - 2 * IZR 1 * PI
    | (inright _, inright _)               => (* 0 > x₁, 0 > y₁, Q3 *)
      match (total_order_T 0 (2 * r - y₁)) with 
      | inleft (left _) => 2 * atan ((x₁ - Q)/(2 * r - y₁)) (* 2 * r - y₁ > 0 *)
      | inleft (right _) => -PI (* 2 * r - y₁ = 0 *)
      | inright _ => 2 * atan ((x₁ - Q)/(2 * r - y₁)) - 2 * IZR 1 * PI (* 2 * r - y₁ < 0 *)
      end
    end
  end.

Definition θ2 x₁ y₁ r : R :=
  let Q := sqrt (x₁² - (2 * r - y₁) * y₁) in
  match (total_order_T 0 r) with
  | inleft (left _) => (* 0 < r *)
    match (total_order_T 0 x₁, total_order_T 0 y₁) with
    | (inleft _, inleft (left _))   => (* 0 <= x₁, 0 < y₁, Q1 *)
      match (total_order_T 0 (2 * r - y₁)) with
      | inleft (left _) => 2 * atan ((x₁ + Q)/(2 * r - y₁))
      | inleft (right _) => PI
      | inright _ => 2 * atan ((x₁ + Q)/(2 * r - y₁)) + 2 * IZR 1 * PI
      end
    | (inleft (left _), inleft (right _))  => (* 0 < x₁, 0 = y₁ *)
      2 * atan (x₁ / r)
    | (inleft _, inright _)         => (* 0 <= x₁, 0 > y₁, Q4 *)
      2 * atan ((x₁ + Q)/(2 * r - y₁))
    | (inleft (right _), inleft (right _)) => (* 0 = x₁, 0 = y₁ *)
      0 (* invalid position *)
    | (inright _, inleft (left _))         => (* 0 > x₁, 0 < y₁, Q2 *)
      match (total_order_T 0 (2 * r - y₁)) with
      | inleft (left _) =>
        2 * atan ((x₁ + Q)/(2 * r - y₁)) + 2 * IZR 1 * PI (* 2 * r - y₁ > 0 *)
      | inleft (right _) => 2*atan (y₁ / (2 * x₁)) + 2 * IZR 1 * PI (* 2 * r - y₁ = 0 *)
      | inright _ => 2 * atan ((x₁ + Q)/(2 * r - y₁)) + 2 * IZR 1 * PI (* 2 * r - y₁ < 0 *)
      end
    | (inright _, inleft (right _))        => (* 0 > x₁, 0 = y₁ *)
      2 * PI
    | (inright _, inright _)               => (* 0 > x₁, 0 > y₁, Q3 *)
      2 * atan ((x₁ + Q)/(2 * r - y₁))
    end
  | inleft (right _) => (* 0 = r *) 0
  | inright _ => (* 0 > r *)
    match (total_order_T 0 x₁, total_order_T 0 y₁) with
    | (inleft _, inleft (left _) )  => (* 0 <= x₁, 0 < y₁, Q1 *)
      2 * atan ((x₁ + Q)/(2 * r - y₁))
    | (inleft (left _), inleft (right _))  => (* 0 < x₁, 0 = y₁ *)
      2 * atan (x₁ / r)
    | (inleft _, inright _)         => (* 0 <= x₁, 0 > y₁, Q4 *)
      match (total_order_T 0 (2 * r - y₁)) with
      | inleft (left _) => 2 * atan ((x₁ + Q)/(2 * r - y₁)) - 2 * IZR 1 * PI (* 0 < 2 * r - y₁ *)
      | inleft (right _) => -PI (* 0 = 2 * r - y₁ *)
      | inright _ => 2 * atan ((x₁ + Q)/(2 * r - y₁)) (* 0 > 2 * r - y₁ *)
      end
    | (inleft (right _), inleft (right _)) => (* 0 = x₁, 0 = y₁ *)
      0 (* invalid position *)
    | (inright _, inleft (left _))         => (* 0 > x₁, 0 < y₁, Q2 *)
      2 * atan ((x₁ + Q)/(2 * r - y₁))
    | (inright _, inleft (right _))        => (* 0 > x₁, 0 = y₁ *)
      - 2 * PI
    | (inright _, inright _)               => (* 0 > x₁, 0 > y₁, Q3 *)
      match (total_order_T 0 (2 * r - y₁)) with 
      | inleft (left _) => 2 * atan ((x₁ + Q)/(2 * r - y₁)) - 2 * IZR 1 * PI (* 2 * r - y₁ > 0 *)
      | inleft (right _) => 2*atan (y₁ / (2 * x₁)) - 2 * IZR 1 * PI (* 2 * r - y₁ = 0 *)
      | inright _ => 2 * atan ((x₁ + Q)/(2 * r - y₁)) - 2 * IZR 1 * PI (* 2 * r - y₁ < 0 *)
      end
    end
  end.



Lemma root_ordering_rpos_left :
  forall x₁ y₁ r
         (rgt0 : 0 < r)
         (ygt0 : 0 < y₁)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    θ1 x₁ y₁ r < θmax < θ2 x₁ y₁ r.
Proof.
  intros.
  unfold θ1,θ2.
  destruct (total_order_T 0 r).
  destruct s.
  destruct (total_order_T 0 x₁).
  assert (0 <= x₁) as zlex1; [destruct s; [ left; assumption | right; assumption] | ].
  destruct s.
  destruct (total_order_T 0 y₁).
  destruct s.
  destruct (total_order_T 0 (2 * r - y₁)).
  destruct s.
  apply root_ordering_Q1bot; try assumption.
  apply (root_ordering_Q1arm _ _ _ rgt0 e r2 r1 phase).
  apply root_ordering_Q1top; try assumption. 
  exfalso. rewrite <- e in ygt0. clear - ygt0. lra.
  exfalso. clear - ygt0 r2. lra.
  destruct (total_order_T 0 y₁).
  destruct s.
  destruct (total_order_T 0 (2 * r - y₁)).
  destruct s.

  exfalso. apply (straight_std_impl_ineq) in phase.
  rewrite <- e, Rsqr_0, Rplus_0_l, Rsqr_minus in phase.
  apply (Rplus_lt_compat_r (- r²)) in phase.
  rewrite Rplus_opp_r in phase.
  assert (forall x y, x - y = x + - y) as Rminus_Ropp; [intros; lra|].
  rewrite Rminus_Ropp in phase.
  rewrite (Rplus_comm _ (- (2 * y₁ * r))) in phase.
  rewrite Rplus_assoc, Rplus_assoc, Rplus_opp_r, Rplus_0_r,
  <- (Ropp_involutive (y₁²)), <- Ropp_plus_distr, <- Rminus_Ropp in phase.
  rewrite <- Ropp_0 in phase.
  apply Ropp_lt_cancel in phase.
  rewrite Rmult_assoc, Rmult_comm, Rmult_assoc in phase.
  unfold Rsqr in phase.
  rewrite <- Rmult_minus_distr_l, (Rmult_comm _ 2) in phase.
  apply (Rmult_lt_compat_l (y₁)) in r2.
  rewrite Rmult_0_r in r2.
  clear - r2 phase. lra. assumption.

  exfalso. apply (straight_std_impl_ineq) in phase.
  rewrite <- e, Rsqr_0, Rplus_0_l, Rsqr_minus in phase.
  apply (Rplus_lt_compat_r (- r²)) in phase.
  rewrite Rplus_opp_r in phase.
  assert (forall x y, x - y = x + - y) as Rminus_Ropp; [intros; lra|].
  rewrite Rminus_Ropp in phase.
  rewrite (Rplus_comm _ (- (2 * y₁ * r))) in phase.
  rewrite Rplus_assoc, Rplus_assoc, Rplus_opp_r, Rplus_0_r,
  <- (Ropp_involutive (y₁²)), <- Ropp_plus_distr, <- Rminus_Ropp in phase.
  rewrite <- Ropp_0 in phase.
  apply Ropp_lt_cancel in phase.
  rewrite Rmult_assoc, Rmult_comm, Rmult_assoc in phase.
  unfold Rsqr in phase.
  rewrite <- Rmult_minus_distr_l, (Rmult_comm _ 2) in phase.
  rewrite <- e0, Rmult_0_r in phase. 
  clear - phase. lra.

  apply root_ordering_Q1top; try assumption. 
  
  exfalso.
  lra.

  clear - r1 ygt0. lra.

  destruct (total_order_T 0 y₁).
  destruct s.
  destruct (total_order_T 0 (2 * r - y₁)).
  destruct s.

  apply root_ordering_Q2bot; try assumption.
  symmetry in e.
  assert (x₁ <= 0) as x1le0. lra.

  apply (root_ordering_Q2arm _ _ _ rgt0); try assumption.
  apply root_ordering_Q2top; try assumption. left. assumption.

  exfalso. rewrite <- e in ygt0. clear - ygt0. lra.
  exfalso. clear - ygt0 r2. lra.
  exfalso.  rewrite <- e in rgt0. lra.

  clear - rgt0 r0. lra.
Qed.


Lemma root_ordering_rneg_right :
  forall x₁ y₁ r
         (rgt0 : r < 0)
         (ygt0 : y₁ < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    θ2 x₁ y₁ r < θmax < θ1 x₁ y₁ r.
Proof.
  intros.
  unfold θ1,θ2.
  destruct (total_order_T 0 r).

  exfalso. destruct s. clear - rgt0 r0. lra. rewrite <- e in rgt0. clear - rgt0. lra. clear r0.
  destruct (total_order_T 0 x₁).
  assert (0 <= x₁) as zlex1; [destruct s; [ left; assumption | right; assumption] | ].
  destruct s.
  destruct (total_order_T 0 y₁).
  destruct s.
  exfalso. clear - r1 ygt0. lra.
  exfalso. clear - e ygt0. rewrite <- e in ygt0. lra.
  clear r1.
  destruct (total_order_T 0 (2 * r - y₁)).
  destruct s.
  apply root_ordering_Q4top_rneg; try assumption.
  apply (root_ordering_Q4arm_rneg _ _ _ rgt0 e ygt0 r0 phase).
  apply root_ordering_Q4bot_rneg; try assumption. 


  destruct (total_order_T 0 y₁).
  destruct s.
  exfalso. clear - r0 ygt0. lra.
  exfalso. clear - e0 ygt0. rewrite <- e0 in ygt0. lra.
  clear r0.
  destruct (total_order_T 0 (2 * r - y₁)).
  destruct s.
  apply root_ordering_Q4top_rneg; try assumption.

  exfalso. apply (straight_std_impl_ineq) in phase.
  rewrite <- e, Rsqr_0, Rplus_0_l, Rsqr_minus in phase.
  apply (Rplus_lt_compat_r (- r²)) in phase.
  rewrite Rplus_opp_r in phase.
  assert (forall x y, x - y = x + - y) as Rminus_Ropp; [intros; lra|].
  rewrite Rminus_Ropp in phase.
  rewrite (Rplus_comm _ (- (2 * y₁ * r))) in phase.
  rewrite Rplus_assoc, Rplus_assoc, Rplus_opp_r, Rplus_0_r,
  <- (Ropp_involutive (y₁²)), <- Ropp_plus_distr, <- Rminus_Ropp in phase.
  rewrite <- Ropp_0 in phase.
  apply Ropp_lt_cancel in phase.
  rewrite Rmult_assoc, Rmult_comm, Rmult_assoc in phase.
  unfold Rsqr in phase.
  rewrite <- Rmult_minus_distr_l, (Rmult_comm _ 2) in phase.
  rewrite <- e0, Rmult_0_r in phase. 
  clear - phase. lra.

  apply root_ordering_Q4bot_rneg; try assumption. 

  exfalso. apply (straight_std_impl_ineq) in phase.
  rewrite <- e, Rsqr_0, Rplus_0_l, Rsqr_minus in phase.
  apply (Rplus_lt_compat_r (- r²)) in phase.
  rewrite Rplus_opp_r in phase.
  assert (forall x y, x - y = x + - y) as Rminus_Ropp; [intros; lra|].
  rewrite Rminus_Ropp in phase.
  rewrite (Rplus_comm _ (- (2 * y₁ * r))) in phase.
  rewrite Rplus_assoc, Rplus_assoc, Rplus_opp_r, Rplus_0_r,
  <- (Ropp_involutive (y₁²)), <- Ropp_plus_distr, <- Rminus_Ropp in phase.
  rewrite <- Ropp_0 in phase.
  apply Ropp_lt_cancel in phase.
  rewrite Rmult_assoc, Rmult_comm, Rmult_assoc in phase.
  unfold Rsqr in phase.
  rewrite <- Rmult_minus_distr_l, (Rmult_comm _ 2) in phase.
  apply (Rmult_gt_compat_l (-y₁)) in r0.
  rewrite Ropp_mult_distr_l_reverse, Ropp_mult_distr_l_reverse in r0.
  apply Ropp_gt_cancel in r0.
  apply Rgt_lt in r0.
  rewrite Rmult_0_r in r0.
  clear - phase r0. lra. lra.
  
  destruct (total_order_T 0 y₁).
  destruct s.

  exfalso. clear - r1 ygt0. lra.
  exfalso. rewrite <- e in ygt0. clear - ygt0. lra.
  
  destruct (total_order_T 0 (2 * r - y₁)).
  destruct s.

  apply Rgt_lt in r1.
  apply (root_ordering_Q3top_rneg); try assumption. left; assumption.
  symmetry in e.
  apply (root_ordering_Q3arm_rneg _ _ _ rgt0); try assumption. left; assumption.
  apply root_ordering_Q3bot_rneg; try assumption.
Qed.

Lemma root_ordering_rpos_right :
  forall x₁ y₁ r
         (rgt0 : 0 < r)
         (ygt0 : y₁ < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    θ2 x₁ y₁ r < θmax/2 + 2 * PI < θ1 x₁ y₁ r.
Proof.
  intros.
  unfold θ1,θ2.
  destruct (total_order_T 0 r).
  destruct s.
  destruct (total_order_T 0 x₁).
  destruct s.
  destruct (total_order_T 0 y₁).
  destruct s.

  exfalso. clear - r2 ygt0. lra.
  exfalso. rewrite <- e in ygt0. clear - ygt0. lra.
  clear r2.
  apply root_ordering_Q4; try assumption. left. assumption.

  destruct (total_order_T 0 y₁).
  destruct s.
  exfalso. clear - r1 ygt0. lra.
  exfalso. lra.
  clear r1 r0.

  assert (0 <= x₁) as zlex1. right; assumption.
  apply root_ordering_Q4; try assumption.
  destruct (total_order_T 0 y₁).
  destruct s.

  exfalso. clear - r2 ygt0. lra.
  exfalso. rewrite <- e in ygt0. clear - ygt0. lra.
  apply root_ordering_Q3; try assumption. left. assumption.

  exfalso. rewrite <- e in rgt0. clear - rgt0. lra.
  exfalso. clear - r0 rgt0. lra.
Qed.


Lemma root_ordering_rneg_left :
  forall x₁ y₁ r
         (rgt0 : r < 0)
         (ygt0 : 0 < y₁)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    θ1 x₁ y₁ r < θmax/2 - 2 * PI < θ2 x₁ y₁ r.
Proof.
  intros.
  unfold θ1,θ2.
  destruct (total_order_T 0 r).
  destruct s.
  exfalso. clear - r0 rgt0. lra.
  exfalso. rewrite <- e in rgt0. clear - rgt0. lra.
  clear r0.
  
  destruct (total_order_T 0 x₁).
  destruct s.
  destruct (total_order_T 0 y₁).
  destruct s.

  clear r1.
  apply root_ordering_Q1_rneg; try assumption. left. assumption.
  exfalso. rewrite <- e in ygt0. clear - ygt0. lra.
  exfalso. clear - r1 ygt0. lra.
  assert (0 <= x₁) as zlex1. right; assumption.
  destruct (total_order_T 0 y₁).
  destruct s.
  apply root_ordering_Q1_rneg; try assumption. 
  exfalso. lra.
  exfalso. clear - r0 ygt0. lra.

  destruct (total_order_T 0 y₁).
  destruct s.
  clear r1.

  apply root_ordering_Q2_rneg; try assumption. left; assumption.

  exfalso. rewrite <- e in ygt0. clear - ygt0. lra.
  exfalso. clear - r1 ygt0. lra.
Qed.

Lemma root_ordering_rneg_back :
  forall x₁ y₁ r
         (rgt0 : r < 0)
         (yeq0 : y₁ = 0)
         (xle0 : x₁ <= 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    - θmax < θ1 x₁ y₁ r /\ - θmax = - 2*PI.
Proof.
  intros.
  unfold θ1,θ2.
  destruct (total_order_T 0 r).
  destruct s.
  exfalso. clear - r0 rgt0. lra.
  exfalso. rewrite <- e in rgt0. clear - rgt0. lra.
  clear r0.
  destruct (total_order_T 0 x₁).
  destruct s.
  exfalso. clear - r0 xle0. lra.
  destruct (total_order_T 0 y₁).
  destruct s.

  exfalso. rewrite yeq0 in r0. clear - r0. lra.
  exfalso.
  apply straightcond in phase.
  rewrite <- e, <- e0 in phase.
  autorewrite with null in phase.
  lra.
  exfalso. rewrite yeq0 in r0. clear - r0. lra.
  apply Rgt_lt in r0.
  destruct (total_order_T 0 y₁).
  destruct s.
  exfalso. rewrite yeq0 in r1. clear - r1. lra.
  clear e.
  specialize (root_ordering_nxarm_rneg _ _ _ rgt0 yeq0 r0 phase) as [ronxa1 [ronxa2 ronxa3]].
  split; assumption.
  exfalso. rewrite yeq0 in r1. clear - r1. lra.
Qed.

Lemma root_ordering_rpos_back :
  forall x₁ y₁ r
         (rgt0 : 0 < r)
         (yeq0 : y₁ = 0)
         (xle0 : x₁ <= 0)
         (phase : straight r 0 0 0 x₁ y₁),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    θ1 x₁ y₁ r < θmax /\ θmax = 2*PI.
Proof.
  intros.
  unfold θ1,θ2.
  destruct (total_order_T 0 r).
  destruct s.
  clear r0.
  destruct (total_order_T 0 x₁).
  destruct s.
  exfalso. clear - r0 xle0. lra.
  destruct (total_order_T 0 y₁).
  destruct s.

  exfalso. rewrite yeq0 in r0. clear - r0. lra.
  exfalso.
  apply straightcond in phase.
  rewrite <- e, <- e0 in phase.
  autorewrite with null in phase.
  lra.
  exfalso. rewrite yeq0 in r0. clear - r0. lra.
  apply Rgt_lt in r0.
  destruct (total_order_T 0 y₁).
  destruct s.
  exfalso. rewrite yeq0 in r1. clear - r1. lra.
  clear e.
  specialize (root_ordering_nxarm _ _ _ rgt0 yeq0 r0 phase) as [ronxa1 [ronxa2 ronxa3]].
  split; assumption.
  exfalso. rewrite yeq0 in r1. clear - r1. lra.

  exfalso. rewrite <- e in rgt0. clear - rgt0. lra.
  exfalso. clear - r0 rgt0. lra.
Qed.

(* begin hide *)
Lemma thmaxne0 :
  forall x₁ y₁ (sintm2ne0 : ~ (0 <= x₁ /\ y₁ = 0)),
    calcθ₁ 0 0 0 x₁ y₁ <> 0.
Proof.
  intros until 1. intro tmeq0.
  unfold calcθ₁ in tmeq0.

  autorewrite with null in *.
  
  specialize PI_RGT_0 as PIgt0.
  destruct (Rle_dec 0 x₁) as [zlex1 | x1lt0].
  + destruct (Rle_dec 0 y₁) as [zley1 | y1lt0].
    ++ destruct zley1 as [zlty1 | zeqy1].
       +++ destruct zlex1 as [zltx1 | zeqx1].
           ++++ specialize (atan2Q1 _ _ zltx1 zlty1) as [at2lb at2ub]. lra.
           ++++ rewrite <- zeqx1, atan2_PI2 in *; try assumption. lra.
       +++ apply sintm2ne0. symmetry in zeqy1. split; assumption.
    ++ apply Rnot_le_lt in y1lt0.
       destruct zlex1 as [zltx1 | zeqx1].
       specialize (atan2Q4 _ _ zltx1 y1lt0) as [at2lb at2ub]. lra.
       rewrite <- zeqx1, atan2_mPI2 in *; try assumption. lra.
  + apply Rnot_le_lt in x1lt0.
    destruct (Rle_dec 0 y₁) as [zley1 | y1lt0].
    ++ destruct zley1 as [zlty1 | zeqy1].
       specialize (atan2Q2 _ _ x1lt0 zlty1) as [at2lb at2ub]. lra.
       rewrite <- zeqy1, atan2_PI in *; try assumption. lra.
    ++ apply Rnot_le_lt in y1lt0.
       specialize (atan2Q3 _ _ x1lt0 y1lt0) as [at2lb at2ub]. lra.
Qed.


Lemma r_sign_tmp : forall x₁ y₁ θc,
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (sintm2ne0 : ~ (0<=x₁ /\ y₁=0))
           (s : 0 <= θmax)
           (tp : (0 < θmax -> θmax/2 < θc < θmax \/
                              - 2*PI < θc < θmax/2 - 2*PI)),
      let r := (x₁ * sin θc - y₁ * cos θc) /
                       (1 - cos θc) in
    ( 0<θc -> 0 < r) /\ ( θc<0 -> r < 0).
Proof.
  intros.
  specialize PI_RGT_0 as PIgt0.

  assert (θmax = 2 * atan2 y₁ x₁) as tmdef. {
    unfold θmax, calcθ₁.
    assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
    rewrite id. clear id.
    assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
    rewrite id. clear id.
    reflexivity. }

  destruct s as [zlttm |zeqtm].
  + specialize (tp zlttm).
    destruct tp as [tmptcp | tmptcn].
    ++ assert (0 < θc) as tcp. {
         destruct tmptcp as [tclb tcub].
         apply (Rlt_trans _ (θmax / 2)).
         lra. assumption. }
       split.
       +++ intro.
           unfold r.

           assert (θmax <= 2*PI) as tmub. {
             apply (Rmult_le_reg_r (/2)).
             apply Rinv_0_lt_compat. lra.
             setl (θmax / 2). setr PI.
             rewrite tmdef.

             assert (2 * atan2 y₁ x₁ / 2 = atan2 y₁ x₁) as id. field.
             rewrite id. clear id.
             apply atan2_bound.
             intro. destruct H0.
             apply sintm2ne0. split. right. symmetry. assumption. assumption.
           }
           
           
           assert (0 < 1 - cos θc) as zlt1mcosz. {
             specialize (COS_bound θc) as [coszlb coszub].
             apply (Rplus_lt_reg_r (cos θc)). setl (cos θc). setr 1.
             inversion_clear coszub as [coszlt1 |coszeq1]. assumption.
             exfalso.
             
             assert (0 <= θc < 2*PI) as tclt2PI. lra.
             specialize (cosθeq1 _ tclt2PI coszeq1) as cosval.
             lra.
           }
           
           apply (Rmult_lt_reg_r (1 - cos θc)); try assumption.
           setl 0. setr (x₁ * sin θc - y₁ * cos θc).
           intro. lra.
           apply (Rplus_lt_reg_r (y₁ * cos θc)).
           setl (y₁ * cos θc). setr (x₁ * sin θc).
           
           destruct (Rle_dec 0 y₁) as [zley1 |zgty1].
           ++++ destruct zley1 as [zlty1 | zeqy1].
                +++++ destruct (Rlt_dec 0 x₁).
                specialize (atan2Q1 _ _ r0 zlty1) as [trlb trub].
                rewrite tmdef in tmptcp.
                destruct tmptcp as [tclb tcub].
                assert (2 * atan2 y₁ x₁ / 2 = atan2 y₁ x₁) as id. field.
                rewrite id in tclb. clear id.
                apply (Rmult_lt_compat_l 2) in trub; [|lra].
                assert (2 * (PI/2) = PI) as id. field. rewrite id in trub. clear id.
                assert (θc < PI) as tcub'. lra. clear tcub H zlttm tmub tmdef θmax.
                destruct (Rlt_dec θc (PI/2)).
                assert (- (PI/2)< θc) as tclb'. lra.
                specialize (cos_gt_0 _ tclb' r1) as cossign.
                apply (Rmult_lt_reg_r (/ cos θc * / x₁)).
                apply Rmult_lt_0_compat; apply Rinv_0_lt_compat; lra.
                setl (y₁ / x₁). lra.
                setr (sin θc / cos θc). lra.
                change (y₁ / x₁ < tan θc).
                rewrite (atan2_atan_Q1 _ _ r0 zlty1) in trlb, trub, tclb.
                rewrite <- (atan_right_inv (y₁ / x₁)).
                apply tan_increasing. lra. assumption. assumption.

                apply Rnot_lt_le in n.
                destruct n as [tcgtPI2 |tceqPI2].
                assert (θc < 3 * (PI/2)) as tcub''. lra.
                specialize (cos_lt_0 _ tcgtPI2 tcub'') as cossign. clear tcub''.
                apply (Rlt_trans _ 0). clear - cossign zlty1.
                setl (- (y₁ * - cos θc)). rewrite <- Ropp_0.
                apply Ropp_lt_contravar. 
                apply Rmult_lt_0_compat. assumption. lra.
                apply Rmult_lt_0_compat. assumption.
                apply sin_gt_0; assumption.

                rewrite <- tceqPI2 in *.
                rewrite cos_PI2, Rmult_0_r, sin_PI2, Rmult_1_r. assumption.

                apply Rnot_lt_le in n.
                destruct n as [x1lt0 |x1eq0].
                specialize (atan2Q2 _ _ x1lt0 zlty1) as [trlb trub].
                rewrite tmdef in tmptcp.
                destruct tmptcp as [tclb tcub].
                assert (2 * atan2 y₁ x₁ / 2 = atan2 y₁ x₁) as id. field.
                rewrite id in tclb. clear id.

                assert (θc < 2*PI) as tcub'. lra.
                assert (PI/2 < θc) as tclb'. lra.
                destruct (Rlt_dec θc PI).
                specialize (sin_gt_0 _ tcp r0) as sinsign.
                clear H tcp zlttm tmub tmdef θmax.
                assert (θc < 3 * (PI/2)) as tcub''. lra.
                specialize (cos_lt_0 _ tclb' tcub'') as cossign.
                apply (Rmult_lt_reg_r (/ - cos θc * / - x₁)).
                apply Rmult_lt_0_compat; apply Rinv_0_lt_compat; lra.
                setl (y₁ / x₁). lra.
                setr (sin θc / cos θc). lra.
                
                change (y₁ / x₁ < tan θc).
                clear tcub'.
                rewrite (atan2_atan_Q2 _ _ x1lt0 zlty1) in trlb, trub, tclb, tcub.
                rewrite <- (atan_right_inv (y₁ / x₁)).

                assert (θc = θc - INR 1 * PI + INR 1 * PI) as tc. field. rewrite tc. clear tc.
                
                rewrite (tan_period_1 (θc - INR 1 *PI)  1%nat) at 1.
                apply tan_increasing. lra. simpl; lra. simpl; lra.

                unfold INR.
                fieldrewrite (θc - 1 * PI) (-((- θc) + PI)).
                rewrite cos_neg, neg_cos, cos_neg.
                intro; lra.

                apply Rnot_lt_le in n.
                destruct n as [tcgtPI2 |tceqPI2].
                destruct (Rlt_dec θc (3*(PI/2))) as [tcub'' | tclb''].
                

                specialize (cos_lt_0 _ tclb' tcub'') as cossign.
                specialize (sin_lt_0 _ tcgtPI2 tcub') as sinsign. clear tcub'.
                setl (- (y₁ * - cos θc)). setr (- (- x₁ * sin θc)).
                apply Ropp_lt_contravar. 
                apply (Rlt_trans _ 0). clear - sinsign x1lt0.
                rewrite <- Ropp_0.
                setl (- (- x₁ * - sin θc)).
                apply Ropp_lt_contravar. 
                apply Rmult_lt_0_compat. lra. lra.
                apply Rmult_lt_0_compat. assumption. lra.

                apply Rnot_lt_le in tclb''.
                specialize (sin_lt_0 _ tcgtPI2 tcub') as sinsign.
                destruct tclb'' as [tp2lttc | tp2eqtc].
                assert (- (PI / 2) < θc + 2 * IZR (- 1) * PI) as tslb. lra.
                assert (θc + 2 * IZR (- 1) * PI < PI/2) as tsub. lra.
                specialize (cos_gt_0 _ tslb tsub) as cossign.
                rewrite cos_period1 in cossign. clear tslb tsub.

                apply (Rmult_lt_reg_r (/ cos θc * / - x₁)).
                apply Rmult_lt_0_compat; apply Rinv_0_lt_compat; lra.
                setl (- ( y₁ / x₁)). lra.
                setr (- ( sin θc / cos θc)). lra.
                apply Ropp_lt_contravar.
                
                change (tan θc < y₁ / x₁).
                clear tclb'.
                rewrite (atan2_atan_Q2 _ _ x1lt0 zlty1) in trlb, trub, tclb, tcub.
                rewrite <- (atan_right_inv (y₁ / x₁)).

                assert (θc = θc - INR 2 * PI + INR 2 * PI) as tc. field. rewrite tc. clear tc.
                rewrite (tan_period_1 (θc - INR 2 *PI)  2%nat) at 1.
                apply tan_increasing. unfold INR. lra. simpl; lra. simpl; lra.
                unfold INR. 
                fieldrewrite (θc - (1 + 1) * PI) (θc + 2* IZR (-1) * PI).
                rewrite cos_period1. intro. rewrite H0 in cossign. clear - cossign. lra.

                rewrite <- tp2eqtc in *.
                clear tcub' tclb' tcgtPI2 tp2eqtc tcp H sinsign zlt1mcosz.
                rewrite sin_3PI2, cos_3PI2 in *. lra.

                (* PI = thetac *)
                rewrite <- tceqPI2, cos_PI, sin_PI. lra.

                (* x1=0 *)
                rewrite x1eq0 in *.
                apply (Rmult_lt_reg_r (/y₁)).
                apply Rinv_0_lt_compat; lra.
                repeat rewrite Rmult_0_l.
                setl (cos θc). intro. lra.
                rewrite atan2_PI2 in tmdef ; [|assumption].
                assert (2 * (PI/2) = PI) as id. field. rewrite id in tmdef. clear id.
                rewrite tmdef in *.
                destruct tmptcp as [tclb tcub].
                apply cos_lt_0; lra.
                
                +++++ rewrite <- zeqy1, Rmult_0_l.
                destruct (Rle_dec 0 x₁).
                exfalso.
                symmetry in zeqy1. apply sintm2ne0. split; assumption.
                apply Rnot_le_lt in n.
                setr (- x₁ * - sin θc).
                apply Rmult_lt_0_compat. lra.
                assert (θmax = 2 * PI) as tmv. {
                  rewrite tmdef.
                  rewrite <- zeqy1, atan2_PI. reflexivity. assumption. }
                rewrite tmv in tmptcp.
                destruct tmptcp as [tclb tcub].
                assert (2 * PI / 2 = PI) as txt; [field|rewrite txt in tclb].
                rewrite <- Ropp_0.
                apply Ropp_lt_contravar.
                apply sin_lt_0; try assumption.
                  
           ++++ exfalso.
                apply Rnot_le_gt, Rgt_lt in zgty1.
                rewrite tmdef in *.
                clear - zlttm tmub zgty1 PIgt0.

                destruct (total_order_T 0 x₁).
                destruct s.
                specialize (atan2Q4 _ _ r zgty1) as [at2lb at2ub].
                clear - at2ub zlttm. lra.

                rewrite <- e in *. clear e.
                specialize (atan2_mPI2 _ zgty1) as at2v.
                rewrite at2v in zlttm. clear - zlttm PIgt0. lra.

                specialize (atan2Q3 _ _ r zgty1) as [at2lb at2ub].
                clear - at2ub zlttm PIgt0. lra.

       +++ intro. exfalso. clear - H tcp. lra.

    ++ assert (~ (x₁ = 0 /\ y₁ = 0)) as notO. intro. apply sintm2ne0. lra.
       assert (θc < 0) as tcp. {
         destruct tmptcn as [tclb tcub].
         apply (Rlt_trans _ (θmax / 2 - 2 *PI)).
         lra.
         rewrite tmdef.
         fieldrewrite (2 * atan2 y₁ x₁ / 2) (atan2 y₁ x₁).
         specialize (atan2_bound _ _ notO) as [at2lb at2ub].
         lra. }
       split.
       +++ intro. exfalso. clear - H tcp. lra.
           
       +++ intro. clear H.
           unfold r.

           assert (θmax <= 2*PI) as tmub. {
             apply (Rmult_le_reg_r (/2)).
             apply Rinv_0_lt_compat. lra.
             setl (θmax / 2). setr PI.
             rewrite tmdef.

             assert (2 * atan2 y₁ x₁ / 2 = atan2 y₁ x₁) as id. field.
             rewrite id. clear id.
             apply atan2_bound. assumption.
           }
           
           
           assert (0 < 1 - cos θc) as zlt1mcosz. {
             rewrite <- cos_neg.
             specialize (COS_bound (-θc)) as [coszlb coszub].
             apply (Rplus_lt_reg_r (cos (-θc))). setl (cos (-θc)). setr 1.
             inversion_clear coszub as [coszlt1 |coszeq1]. assumption.
             exfalso.
             
             assert (0 <= - θc < 2*PI) as tclt2PI. lra.
             specialize (cosθeq1 _ tclt2PI coszeq1) as cosval.
             lra.
           }
           
           apply (Rmult_lt_reg_r (1 - cos θc)); try assumption.
           setr 0. setl (x₁ * sin θc - y₁ * cos θc).
           intro. lra.
           apply (Rplus_lt_reg_r (y₁ * cos θc)).
           setr (y₁ * cos θc). setl (x₁ * sin θc).
           
           destruct (Rle_dec 0 y₁) as [zley1 |zgty1].
           ++++ destruct zley1 as [zlty1 | zeqy1].
                +++++ destruct (Rlt_dec 0 x₁).
                specialize (atan2Q1 _ _ r0 zlty1) as [trlb trub].
                rewrite tmdef in tmptcn.
                destruct tmptcn as [tclb tcub].
                assert (2 * atan2 y₁ x₁ / 2 = atan2 y₁ x₁) as id. field.
                rewrite id in tcub. clear id.
                apply (Rmult_lt_compat_l 2) in trub; [|lra].
                assert (2 * (PI/2) = PI) as id. field. rewrite id in trub. clear id.
                assert (θc < - 3 *(PI/2) ) as tcub'. lra. clear zlttm tmub tmdef θmax.
                assert ((θc + 2 * INR 1 * PI) < (PI/2)) as tcsub'. unfold INR. lra.
                assert (- (PI/2) < (θc + 2 * INR 1 * PI)) as tcslb'. unfold INR. lra.
                specialize (cos_gt_0 _ tcslb' tcsub') as cossign. clear tcslb' tcsub'.

                rewrite cos_period in cossign.
                
                apply (Rmult_lt_reg_r (/ cos θc * / x₁)).
                apply Rmult_lt_0_compat; apply Rinv_0_lt_compat; lra.
                setr (y₁ / x₁). lra.
                setl (sin θc / cos θc). lra.
                change (tan θc < y₁ / x₁).
                rewrite (atan2_atan_Q1 _ _ r0 zlty1) in trlb, trub, tcub.
                rewrite <- (atan_right_inv (y₁ / x₁)).

                rewrite <- (tan_period_1 _ 2);
                  [|intro costc0; rewrite costc0 in cossign;
                    clear - cossign; lra].
                apply tan_increasing; try (unfold INR; lra).

                apply Rnot_lt_le in n.
                destruct n as [x1lt0 |x1eq0].
                assert (θc < - PI) as tcub''. lra.
                rewrite tmdef in tmptcn.
                destruct tmptcn as [tclb tcub].
                assert (-(PI/2) < θc + 2 * 1 * PI) as tcelb. lra.
                assert (0 < θc + 2 * 1 * PI) as tcelb'. lra.
                assert (θc + 2 * 1 * PI < PI) as tceub. lra.
                specialize (sin_gt_0 _ tcelb' tceub) as sinsign.
                rewrite sin_period1 in sinsign.
                destruct (Rlt_dec (θc + 2 * 1 * PI) (PI/2)).
                specialize (cos_gt_0 _ tcelb r0) as cossign. clear tcelb tceub.
                rewrite cos_period1 in cossign.
                apply (Rlt_trans _ 0). clear - sinsign x1lt0.
                setl (- (- x₁ * sin θc)). rewrite <- Ropp_0.
                apply Ropp_lt_contravar. 
                apply Rmult_lt_0_compat. lra. assumption.
                apply Rmult_lt_0_compat; assumption.

                apply Rnot_lt_le in n.
                destruct n as [tcegtPI2 | tceeqPI2].
                assert (θc + 2 * 1 * PI < 3 * (PI/2)) as tceub'. lra.
                specialize (cos_lt_0 _ tcegtPI2 tceub') as cossign. 
                rewrite cos_period1 in cossign.

                
                apply (Rmult_lt_reg_r (/ - cos θc * / - x₁)).
                apply Rmult_lt_0_compat; apply Rinv_0_lt_compat; lra.
                setr (y₁ / x₁). lra.
                setl (sin θc / cos θc). lra.
                
                change (tan θc < y₁ / x₁).
                rewrite (atan2_atan_Q2 _ _ x1lt0 zlty1) in *.
                rewrite <- (atan_right_inv (y₁ / x₁)).

                
                rewrite <- (tan_period_1 (θc)  1%nat) at 1.
                apply tan_increasing. unfold INR. lra.
                unfold INR. lra. simpl; lra.
                intro; lra.

                rewrite <- (cos_period _ 1), <- (sin_period _ 1).
                unfold INR.
                rewrite <- tceeqPI2, cos_PI2, sin_PI2. lra.
                
                (* x1=0 *)
                rewrite x1eq0 in *.
                apply (Rmult_lt_reg_r (/y₁)).
                apply Rinv_0_lt_compat; lra.
                repeat rewrite Rmult_0_l.
                setr (cos θc). intro. lra.
                rewrite atan2_PI2 in tmdef ; [|assumption].
                assert (2 * (PI/2) = PI) as id. field.
                rewrite id in tmdef. clear id.
                rewrite tmdef in *.
                destruct tmptcn as [tclb tcub].
                rewrite <- (cos_period _ 1). unfold INR.
                apply cos_gt_0; lra.
                
                +++++ rewrite <- zeqy1, Rmult_0_l in *.
                destruct (Rle_dec 0 x₁).
                exfalso.
                symmetry in zeqy1. apply sintm2ne0.
                split; [assumption|reflexivity].
                
                apply Rnot_le_lt in n.
                assert (θmax = 2 * PI) as tmv. {
                  rewrite tmdef.
                  rewrite atan2_PI. reflexivity. assumption. }
                setl (- (- x₁ * sin θc)). rewrite <- Ropp_0.
                apply Ropp_lt_contravar.
                apply Rmult_lt_0_compat. lra.

                rewrite tmv in tmptcn.
                destruct tmptcn as [tclb tcub].
                assert (2 * PI / 2 - 2 * PI = - PI) as txt;
                  [field|rewrite txt in tcub].
                rewrite <- (sin_period _ 1).
                apply sin_gt_0; unfold INR; lra.
                  
           ++++ exfalso.
                apply Rnot_le_gt, Rgt_lt in zgty1.
                rewrite tmdef in *.
                clear - zlttm tmub zgty1 PIgt0.

                destruct (total_order_T 0 x₁).
                destruct s.
                specialize (atan2Q4 _ _ r zgty1) as [at2lb at2ub].
                clear - at2ub zlttm. lra.

                rewrite <- e in *. clear e.
                specialize (atan2_mPI2 _ zgty1) as at2v.
                rewrite at2v in zlttm. clear - zlttm PIgt0. lra.

                specialize (atan2Q3 _ _ r zgty1) as [at2lb at2ub].
                clear - at2ub zlttm PIgt0. lra.

  +  exfalso. apply (thmaxne0 _ _ sintm2ne0).
     symmetry.
     unfold θmax in zeqtm.
     assumption.
Qed.


Lemma r_sign_tmn : forall x₁ y₁ θc,
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (sintm2ne0 : ~ (0<=x₁ /\ y₁=0))
           (s : θmax < 0)
           (tn : (θmax < θc < θmax/2 \/
                  θmax/2 + 2*PI < θc < 2*PI)),
      let r := (x₁ * sin θc - y₁ * cos θc) /
                       (1 - cos θc) in
    ( 0<θc -> 0 < r) /\ ( θc<0 -> r < 0).
Proof.
  intros.
  assert (θmax = 2 * atan2 y₁ x₁) as tmdef.
  unfold θmax, calcθ₁ in *.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id in *. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id in *. clear id. reflexivity.

  set (θmax' := calcθ₁ 0 0 0 x₁ (-y₁)).
  assert (θmax' = 2 * atan2 (-y₁) x₁) as tm'def.
  unfold θmax', calcθ₁ in *.
  assert (- (x₁ - 0) * sin 0 + (- y₁ - 0) * cos 0 = - y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id in *. clear id.
  assert ((x₁ - 0) * cos 0 + (- y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id in *. clear id. reflexivity.

  destruct (Req_dec y₁ 0) as [y1eq0 |y1ne0].
  rewrite y1eq0 in *.
  rewrite Ropp_0 in *.
  rewrite tmdef in *.
  clear tm'def tmdef θmax θmax' y1eq0.
  assert (x₁ < 0) as x1lt0.
  apply Rnot_le_lt. intro.
  apply sintm2ne0. split; [assumption|reflexivity].
  rewrite (atan2_PI) in *; try assumption.
  clear - s. specialize PI_RGT_0. lra.
  
  assert (θmax' = - θmax) as tmrel. rewrite tm'def, tmdef.

  rewrite atan2_symmetry.
  fieldrewrite (- - y₁) (y₁). lra.
  intro notnx. destruct notnx as [x1lt0 ny1eq0].
  apply Ropp_eq_0_compat in ny1eq0.
  rewrite Ropp_involutive in ny1eq0.
  apply y1ne0. assumption.

  assert (0 <= θmax') as s'. lra.
  set (θc' := - θc).
  set (r' := (x₁ * sin θc' - (-y₁) * cos θc') / (1 - cos θc')).
  assert (θmax' / 2 < θc' < θmax' \/
          - 2 * PI < θc' < θmax' / 2 - 2 * PI ) as tp.
  destruct tn as [[tcnl tcnu] | [tcpl tcpu]].
  left. rewrite tmrel. unfold θc'. split; lra.
  right. rewrite tmrel. unfold θc'. split; lra.

  assert ((0 < θc' -> 0 < r') /\ (θc' < 0 -> r' < 0)) as r'ine.
  assert ( ~ (0 <= x₁ /\ (-y₁) = 0)) as sintm2ne0'.
  intro notpx. destruct notpx as [zlex1 ny1eq0]. apply sintm2ne0. split. assumption. lra.
  assert (0 < θmax' -> θmax' / 2 < θc' < θmax' \/ -2 * PI < θc' < θmax' / 2 - 2 * PI) as tpq.
  intros. assumption.
  apply (r_sign_tmp x₁ (-y₁) θc' sintm2ne0' s' tpq).
  destruct r'ine as [zlttc tclt0].
  destruct (Rlt_dec 0 θc') as [zlttc' | zgetc'].
  specialize (zlttc zlttc'). clear tclt0.
  unfold r' in zlttc.
  unfold θc' in zlttc', zlttc.
  rewrite <- Ropp_0 in zlttc'.
  apply Ropp_lt_contravar in zlttc'.
  repeat rewrite Ropp_involutive in zlttc'.
  split. intro zlttc2. exfalso. clear - zlttc' zlttc2. lra.
  intro tmp. clear tmp. unfold r.
  rewrite sin_neg, cos_neg in zlttc .
  clear - zlttc. lra.

  apply Rnot_lt_le in zgetc'.
  rename tclt0 into r'lt0.
  destruct zgetc' as [tc'lt0 | tc'eq0].
  specialize (r'lt0 tc'lt0). clear zlttc.
  unfold r' in r'lt0.
  unfold θc' in r'lt0, tc'lt0.
  rewrite <- Ropp_0 in tc'lt0.
  apply Ropp_lt_contravar in tc'lt0.
  repeat rewrite Ropp_involutive in tc'lt0.
  split.
  intro. clear H. unfold r.
  rewrite sin_neg, cos_neg in r'lt0.
  clear - r'lt0. lra.
  intro tclt0. exfalso. clear - tc'lt0 tclt0. lra.

  exfalso.
  assert (θc = 0) as tceq0.
  unfold θc' in tc'eq0. lra.
  rewrite tceq0 in *.
  destruct tn as [a | b].
  clear - a.
  destruct a.
  lra.
  
  rewrite tmdef in *.
  clear - b s y1ne0.
  assert (~(x₁= 0 /\ y₁ = 0)) as notO.
  intro notO. apply y1ne0. destruct notO as [x1ne0 y1ne0']. assumption.
  specialize (atan2_bound _ _ notO) as [atl atu].
  lra.
Qed.  

(* end hide *)
Lemma r_sign : forall x₁ y₁ θc,
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (sintm2ne0 : ~ (0<=x₁ /\ y₁=0))
           (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI)) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      let r := (x₁ * sin θc - y₁ * cos θc) /
                       (1 - cos θc) in
    ( 0<θc -> 0 < r) /\ ( θc<0 -> r < 0).
Proof.
  intros.
  destruct tcrng as [tmp tmn].
  destruct (Rle_dec 0 θmax).
  apply r_sign_tmp; try assumption.
  apply Rnot_le_lt in n.
  specialize (tmn n).
  apply r_sign_tmn; try assumption.
Qed.


Lemma theta1_rng :
  forall x₁ y₁ r
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (- 2 * PI < θ1 x₁ y₁ r < 2 * PI).
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  assert (2 * PI > 0) as tpigt0; [lra|].

  unfold θ1.

  destruct (total_order_T 0 (2 * r - y₁))  as [[zltarm |zeqarm] |zgtarm].
  ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
                set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
                try (split; lra).
              +++++ split. lra.
              assert (A < 0) as alt0. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (-0). setl (- ((2 * r - y₁) * - y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; lra.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  lra. unfold Rsqr.
                  apply Rmult_lt_0_compat; assumption. }
                
                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa; try (left; assumption).
                apply Rlt_minus in sa.
                unfold A.
                apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                setr 0.
                setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                  [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                assumption. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
                set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *.

              +++++ split; lra.
              +++++ split; lra.
              +++++ split. lra.
              unfold A in *. clear A.
              rewrite <- zeqx1, Rminus_0_l in *.
              set (A := ((- sqrt (0² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).

              assert (A < 0) as zlta. {
                assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                  rewrite Rsqr_0, Rminus_0_l.
                  setr ((2 * r - y₁) * - y₁).
                  apply Rmult_lt_0_compat; [assumption| lra].
                }
                apply sqrt_lt_1 in inq ; [ | right; reflexivity | left; assumption].
                rewrite sqrt_0 in inq.
                apply Ropp_lt_contravar in inq.
                rewrite Ropp_0 in inq.
                unfold A.
                apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                setr 0.
                setl (- sqrt (0² - (2 * r - y₁) * y₁));
                  [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                assumption. }
              apply atan_increasing in zlta.
              rewrite atan_0 in zlta.
              lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                in *.
              assert (A < 0) as alt0. {
                assert ((x₁² - (2 * r - y₁) * y₁) < x₁²) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setl 0. setr ((2 * r - y₁) * y₁).
                  apply Rmult_lt_0_compat; assumption.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in ssa;
                  [|right; reflexivity| left; assumption].
                rewrite sqrt_0 in ssa.
                unfold A.
                apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                setr 0.
                setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                  [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (-PI/2 < atan A) in atl.
              clear atu.
              split; lra.
              +++++ specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
              set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *.
              assert (A < 0) as alt0. {
                unfold A.
                rewrite <- zeqy1, Rminus_0_r, Rmult_0_r, Rminus_0_r.
                apply (Rmult_lt_reg_r (2*r)); try lra.
                setr (0). setl (x₁ - sqrt x₁²); try assumption.
                rewrite sqrt_Rsqr_abs, Rabs_left.
                lra.
                assumption.
              }

              split. lra.
              apply atan_increasing in alt0.
              rewrite atan_0 in alt0.
              lra.
              
              +++++ specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
                set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *.
                split. lra.
                
                assert (A < 0) as alt0. {
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setr 0.
                  setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sqge0.
                  lra.
                }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                lra.
                
     +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split ; lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     try (split; lra).

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     try (split; lra).

  ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
                     split; lra).
              +++++ symmetry in zeqarm.
              apply Rminus_diag_uniq in zeqarm.
              rewrite <- zeqarm in *.
              fieldrewrite (2 * r / (2 * x₁)) (r / x₁); try lra.
              assert (0 < r / x₁) as agt0.
              apply (Rmult_lt_reg_r (x₁)); try assumption.
              setr r. lra. setl 0. assumption.
              apply atan_increasing in agt0.
              rewrite atan_0 in agt0.
              specialize (atan_bound (r/x₁)) as [atl atu].
              split; lra.

         ++++ exfalso. unfold straight, Tcx, Tcy in phase.
              rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
              sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
              <- zeqx1, Rsqr_0, Rplus_0_l, Rsqr_minus in phase.
              apply (Rplus_lt_compat_r (- r²)) in phase.
              rewrite Rplus_opp_r in phase.
              assert (0 < - y₁ * (2 * r- y₁ )) as phase1. {
                  clear - phase.
                  setr (y₁² + r² - 2 * y₁ * r + - r²).
                  assumption. }
              rewrite <- zeqarm in phase1.
              lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
                set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *; lra.
     +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
              set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
              split; lra).
              +++++ symmetry in zeqarm.
              apply Rminus_diag_uniq_sym in zeqarm.
              rewrite zeqarm in *.
              fieldrewrite (2 * r / (2 * x₁)) (r / x₁). lra.
              specialize (atan_bound (r/x₁)) as [atl atu];
              set (A := r/x₁) in *;
              split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
                set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
                split; lra).

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; lra. 

  ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; try lra.
              +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                 / (2 * r - y₁))) in *.
              assert (0 < A) as zlta. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (- 0). setl (-(- (2 * r - y₁) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_involutive.
                  apply Ropp_lt_contravar.
                  rewrite Ropp_0.
                  lra.
                  apply Rmult_lt_0_compat; assumption.
                }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa; [| left;lra].

                apply Rlt_minus in sa.
                unfold A.
                apply (Rmult_lt_reg_r (- (2 * r - y₁))); try lra.
                setl 0.
                setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))) ;
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                lra. }

              apply atan_increasing in zlta.
              apply (Rmult_lt_compat_l 2) in zlta; [|lra].
              rewrite atan_0, Rmult_0_r in zlta.
              specialize (atan_bound (A)) as [atl atu].
              clear atl.
              split; lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).
     +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     try (split; lra).
              +++++ assert (0 < A) as zlta. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁) ) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (- 0). setl (-(- (2 * r - y₁) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_involutive.
                  apply Ropp_lt_contravar.
                  rewrite Ropp_0.
                  lra.
                  apply Rmult_lt_0_compat; assumption.
                }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa; [| left;lra].

                apply Rlt_minus in sa.
                unfold A.
                apply (Rmult_lt_reg_r (- (2 * r - y₁))); try lra.
                setl 0.
                setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))) ;
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                lra. }

              apply atan_increasing in zlta.
              apply (Rmult_lt_compat_l 2) in zlta; [|lra].
              rewrite atan_0, Rmult_0_r in zlta.
              clear atl.
              split; lra.
              
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     try (split; lra).
              +++++ assert (0 < A) as zlta. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁) ) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (- 0). setl (-(- (2 * r - y₁) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  rewrite <- zeqx1, Rsqr_0.
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_0.
                  apply Ropp_lt_contravar.
                  lra.
                }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa; [| right;lra].

                apply Rlt_minus in sa.
                unfold A.
                apply (Rmult_lt_reg_r (- (2 * r - y₁))); try lra.
                setl 0.
                setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))) ;
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                lra. }

              apply atan_increasing in zlta.
              apply (Rmult_lt_compat_l 2) in zlta; [|lra].
              rewrite atan_0, Rmult_0_r in zlta.
              clear atl.
              split; lra.
              
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *.
              +++++  assert (0 < A) as alt0. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁²)).
                  setl 0. setr ((- (2 * r - y₁) * y₁)).
                  apply Rmult_lt_0_compat; lra.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                apply (Rlt_trans x₁) in sa; [|lra].
                apply Rlt_Rminus in sa.
                unfold A.

                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setl 0.
                setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)));
                  [ intro an0; rewrite an0 in zgtarm; clear - zgtarm; lra|].
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              change (atan A<PI/2) in atu.
              clear atl.
              split; lra.
              +++++ assert (0 < A) as alt0. {
                unfold A.
                rewrite <- zeqy1, Rminus_0_r, Rmult_0_r, Rminus_0_r.
                apply (Rmult_lt_reg_r (2*- r)); try lra.
                setl (0). setr (- (x₁ - sqrt x₁²)); try lra.
                rewrite sqrt_Rsqr_abs, Rabs_left.
                lra.
                assumption.
              }

              split. 
              apply atan_increasing in alt0.
              rewrite atan_0 in alt0.
              lra.
              lra.

              +++++  assert (0 < A) as alt0. {

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in ssa;
                  [|right; reflexivity|left; assumption].
                rewrite sqrt_0 in ssa.
                apply Ropp_lt_contravar in ssa.
                rewrite Ropp_0 in ssa.
                apply (Rplus_lt_compat_l x₁) in ssa.
                apply (Rlt_trans _ _ 0) in ssa; [|lra].
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setl 0.
                setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)));
                  [ intro an0; rewrite an0 in zgtarm; clear - zgtarm; lra|].
                clear - ssa.
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              change (atan A<PI/2) in atu.
              clear atl.
              split; lra.

Qed.


Lemma theta1_rsgn_lim :
  forall x₁ y₁ r
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (0 < r -> 0 <= θ1 x₁ y₁ r)/\(r < 0 -> θ1 x₁ y₁ r <= 0).
Proof.
    intros.
    specialize PI_RGT_0 as pigt0.
    assert (2 * PI > 0) as tpigt0; [lra|].

    unfold θ1.

    destruct (total_order_T 0 (2 * r - y₁))  as [[zltarm |zeqarm] |zgtarm].
    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (0 < A) as alt0. {
                  assert ((x₁² - (2 * r - y₁) * y₁) < x₁²) as sa. {
                    apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                    setl 0. setr ((2 * r - y₁) * y₁).
                    apply Rmult_lt_0_compat; assumption.
                  }

                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in sa;
                    [|left; assumption|apply Rle_0_sqr].
                  rewrite sqrt_Rsqr_abs, Rabs_right in sa; try (left; lra).
                  apply Rlt_minus in sa.
                  
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setl 0.
                  setr (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                  lra. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (-PI/2 < atan A) in atl.
                clear atu.
                split; lra.
                +++++ split; intros; lra.
                +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (A < 0) as alt0. {
                  assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                    apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                    setr 0. setl (-((2 * r - y₁) * - y₁)).
                    rewrite <- Ropp_0.
                    apply Ropp_lt_contravar.
                    apply Rmult_lt_0_compat; [ assumption|lra].
                  }

                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in sa;
                    [|apply Rle_0_sqr|left; assumption].
                  rewrite sqrt_Rsqr_abs, Rabs_right in sa; try lra.
                  apply Rlt_minus in sa.

                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setr 0.
                  setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                  assumption. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (-PI/2 < atan A) in atl.
                clear atu.
                split; lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exfalso. unfold straight, Tcx, Tcy in phase.
                rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                <- zeqx1, Rsqr_0, Rplus_0_l, Rsqr_minus in phase.
                apply (Rplus_lt_compat_r (- r²)) in phase.
                rewrite Rplus_opp_r in phase.
                assert (0 < - y₁ * (2 * r- y₁ )) as phase1. {
                  clear - phase.
                  setr (y₁² + r² - 2 * y₁ * r + - r²).
                  assumption. }
                apply (Rmult_lt_compat_l (y₁)) in zltarm; try assumption.
                rewrite Rmult_0_r in zltarm.
                clear - phase1 zltarm.
                lra.
                +++++ exfalso.
                apply straightcond in phase.
                rewrite <- zeqx1, <- zeqy1 in *.
                autorewrite with null in phase.
                lra.
                +++++ specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
              rewrite <- zeqx1, Rminus_0_l in *.
              set (A := sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
              assert (0 < A) as zlta. {
                assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                  rewrite Rsqr_0, Rminus_0_l.
                  setr ((2 * r - y₁) * - y₁).
                  apply Rmult_lt_0_compat; [assumption | lra ].
                }
                apply sqrt_lt_1 in inq ; [ | right; reflexivity | left; assumption].
                rewrite sqrt_0 in inq.

                unfold A.
                apply (Rmult_lt_reg_r ((2 * r - y₁)));[assumption|].
                setl 0.
                setr (sqrt (0² - (2 * r - y₁) * y₁));
                  [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                assumption. }
              apply atan_increasing in zlta.
              rewrite atan_0 in zlta.
              split; lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (A < 0) as alt0. {
                  assert ((x₁² - (2 * r - y₁) * y₁) < x₁²) as sa. {
                    apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                    setl 0. setr ((2 * r - y₁) * y₁).
                    apply Rmult_lt_0_compat; assumption.
                  }

                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in ssa;
                    [|right; reflexivity|left; assumption].
                  rewrite sqrt_0 in ssa.
                  apply Ropp_lt_contravar in ssa.
                  apply (Rplus_lt_compat_l x₁) in ssa.
                  apply (Rlt_trans _ _ 0) in ssa ; [|lra].
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setr 0.
                  setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                  lra. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (-PI/2 < atan A) in atl.
                clear atu.
                split; lra.
                +++++ specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                 / (2 * r - y₁)))) as [atl atu].
                set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (A < 0) as alt0. {
                unfold A.
                rewrite <- zeqy1, Rminus_0_r, Rmult_0_r, Rminus_0_r.
                apply (Rmult_lt_reg_r (2*r)); try lra.
                setr (0). setl ((x₁ - sqrt x₁²)); try lra.
                rewrite sqrt_Rsqr_abs, Rabs_left; [| assumption].
                lra.
              }

              split. 
              apply atan_increasing in alt0.
              rewrite atan_0 in alt0.
              lra.
              lra.


              +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (A<0) as alt0. {
                  assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                    apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                    setr 0. setl (-((2 * r - y₁) * - y₁)).
                    rewrite <- Ropp_0.
                    apply Ropp_lt_contravar.
                    apply Rmult_lt_0_compat; [assumption|lra].
                  }
                  
                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in ssa;
                    [|right; reflexivity|left; assumption].
                  rewrite sqrt_0 in ssa.
                  apply Ropp_lt_contravar in ssa.
                  apply (Rplus_lt_compat_l x₁) in ssa.
                  apply (Rlt_trans _ _ 0) in ssa; [|lra].
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setr 0.
                  setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                  lra. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (-PI/2 < atan A) in atl.
                clear atu.
                split; lra.

       +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (0 < A) as zlta. {
                  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sqp.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); [assumption|].
                  setl 0.
                  setr (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                  lra. }

                apply atan_increasing in zlta.
                apply (Rmult_lt_compat_l 2) in zlta; [|lra].
                rewrite atan_0, Rmult_0_r in zlta.
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (atan A< PI/2) in atu.
                clear atl.
                split; lra.
                +++++ lra.
                +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (A < 0) as zlta. {
                  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sqp.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); [assumption|].
                  setr 0.
                  setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                  apply Rlt_minus.
                  rewrite <- (Rabs_right x₁), <- sqrt_Rsqr_abs at 1; [|left; assumption].
                  apply sqrt_lt_1; [apply Rle_0_sqr | |].
                  left.
                  apply Rlt_Rminus.
                  apply (Rlt_trans _ 0).
                  setl (-((2 * r - y₁) * - y₁)). setr (-0).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; lra.
                  unfold Rsqr.
                  apply Rmult_lt_0_compat; assumption.
                  apply (Rplus_lt_reg_r (- x₁²)).
                  setl 0.
                  setr ((2 * r - y₁) * - y₁).
                  apply Rmult_lt_0_compat; [ assumption|lra].
                }

                apply atan_increasing in zlta.
                apply (Rmult_lt_compat_l 2) in zlta; [|lra].
                rewrite atan_0, Rmult_0_r in zlta.
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (atan A< PI/2) in atu.
                clear atl.
                split; lra.
                
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                 / (2 * r - y₁)))) as [atl atu].
                rewrite <- zeqx1, Rminus_0_l in *.
                set (A := sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
                assert (0 < A) as zlta. {
                  assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                    rewrite Rsqr_0, Rminus_0_l.
                    setr ((2 * r - y₁) * - y₁).
                    apply Rmult_lt_0_compat; [assumption| lra].
                  }
                  apply sqrt_lt_1 in inq ;
                       [ | right; reflexivity | left; assumption].
                  rewrite sqrt_0 in inq.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setl 0.
                  setr (sqrt (0² - (2 * r - y₁) * y₁));
                    [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                  assumption. }
                apply atan_increasing in zlta.
                rewrite atan_0 in zlta.
                split; lra.
                +++++ lra.
                +++++ specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                 / (2 * r - y₁)))) as [atl atu].
                unfold Rsqr in *.
                rewrite <- zeqx1, Rminus_0_l, Rmult_0_r, Rminus_0_l in *.
                set (A := - sqrt (- ((2 * r - y₁) * y₁)) / (2 * r - y₁)) in *.
                assert (A < 0) as zlta. {
                  assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                    rewrite Rsqr_0, Rminus_0_l.
                    setr ((2 * r - y₁) * - y₁).
                    apply Rmult_lt_0_compat; [assumption| lra].
                  }
                  apply sqrt_lt_1 in inq ;
                       [ | right; reflexivity | left; assumption].
                  unfold Rsqr in inq.
                  rewrite sqrt_0, Rmult_0_r, Rminus_0_l in inq.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setr 0.
                  setl (- sqrt (- ((2 * r - y₁) * y₁)));
                    [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                  lra. }
                apply atan_increasing in zlta.
                rewrite atan_0 in zlta.
                split; lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (A < 0) as alt0. {
                  assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                    apply (Rplus_lt_reg_r (- x₁²)).
                    setl 0. setr ((2 * r - y₁) * - y₁).
                    apply Rmult_lt_0_compat; [assumption|lra].
                  }

                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in ssa;
                    [|right; reflexivity|left; assumption].
                  rewrite sqrt_0 in ssa.
                  apply Ropp_lt_contravar in ssa.
                  apply (Rplus_lt_compat_l x₁) in ssa.
                  apply (Rlt_trans _ _ 0) in ssa; [|lra].
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setr 0.
                  setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                    [ intro an0; rewrite an0 in zltarm; clear - zltarm; lra|].
                  clear - ssa.
                  lra. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (atan A<PI/2) in atu.
                clear atl.
                split; lra.
                +++++ lra.
                +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (A < 0) as alt0. {
                  assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                    apply (Rplus_lt_reg_r (- x₁²)).
                    setl 0. setr ((2 * r - y₁) * - y₁).
                    apply Rmult_lt_0_compat; [assumption|lra].
                  }

                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in ssa;
                    [|right; reflexivity|left; assumption].
                  rewrite sqrt_0 in ssa.
                  apply Ropp_lt_contravar in ssa.
                  apply (Rplus_lt_compat_l x₁) in ssa.
                  apply (Rlt_trans _ _ 0) in ssa; [|lra].
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setr 0.
                  setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                    [ intro an0; rewrite an0 in zltarm; clear - zltarm; lra|].
                  clear - ssa.
                  lra. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (atan A<PI/2) in atu.
                clear atl.
                split; lra.
    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; try lra.
              +++++ symmetry in zeqarm.
              apply Rminus_diag_uniq_sym in zeqarm.
              rewrite zeqarm.
              fieldrewrite (2 * r / (2 * x₁)) (r / x₁);
                [intro x1eq0; clear - x1eq0 zltx1; lra|].
              assert (0 < r / x₁) as an. {
                apply (Rmult_lt_reg_r (x₁)); [lra|].
                setr (r); [intro x1eq0; clear - x1eq0 zltx1; lra|].
                rewrite Rmult_0_l.
                assumption. }
              set (A:=r / x₁) in *.
              apply atan_increasing in an.
              apply (Rmult_lt_compat_l 2) in an; [|lra].
              rewrite atan_0, Rmult_0_r in an.
              specialize (atan_bound (A)) as [atl atu].
              clear atu.
              split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; try lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; lra.

     +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; try lra.
              +++++ symmetry in zeqarm.
              apply Rminus_diag_uniq_sym in zeqarm.
              rewrite zeqarm.
              fieldrewrite (2 * r / (2 * x₁)) (r / x₁);
                [intro x1eq0; clear - x1eq0 zltx1; lra|].
              assert (r / x₁ < 0) as an. {
                apply (Rmult_lt_reg_r (x₁)); [lra|].
                setl (r); [intro x1eq0; clear - x1eq0 zltx1; lra|].
                rewrite Rmult_0_l.
                assumption. }
              set (A:=r / x₁) in *.
              apply atan_increasing in an.
              apply (Rmult_lt_compat_l 2) in an; [|lra].
              rewrite atan_0, Rmult_0_r in an.
              specialize (atan_bound (A)) as [atl atu].
              clear atu.
              split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; try lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ exfalso.
              symmetry in zeqarm.
              apply Rminus_diag_uniq in zeqarm.
              symmetry in zeqarm.
              rewrite zeqarm in zlty1.
              clear - zlty1 zgtr.
              lra.
              +++++ lra.

              +++++ lra. 
    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                 / (2 * r - y₁))) in *.
              assert (0 < A) as zlta. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (- 0). setl (-(- (2 * r - y₁) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_involutive.
                  apply Ropp_lt_contravar.
                  rewrite Ropp_0.
                  lra.
                  apply Rmult_lt_0_compat; assumption.
                }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa; [| left;lra].

                assert (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁) < 0) as nps. {
                  lra. }
                unfold A.
                apply (Rmult_lt_reg_r (- (2 * r - y₁))); try lra.
                setl 0.
                setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))) ;
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                lra. }

              apply atan_increasing in zlta.
              apply (Rmult_lt_compat_l 2) in zlta; [|lra].
              rewrite atan_0, Rmult_0_r in zlta.
              specialize (atan_bound (A)) as [atl atu].
              clear atu.
              split; lra.
              +++++ lra.
              +++++ exfalso.
              apply Rgt_lt, Rminus_lt in zgtarm.
              clear - zgtarm zgty1 zltr.
              lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
              rewrite <- zeqx1, Rminus_0_l in *.
              set (A := - sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
              assert (0 < A) as zlta. {
                assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                  rewrite Rsqr_0, Rminus_0_l.
                  setr (- (2 * r - y₁) * y₁).
                  apply Rmult_lt_0_compat; [lra | assumption].
                }
                apply sqrt_lt_1 in inq ; [ | right; reflexivity | left; assumption].
                rewrite sqrt_0 in inq.

                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁)));[lra|].
                setl 0.
                setr (sqrt (0² - (2 * r - y₁) * y₁));
                  [intro ae0; rewrite ae0 in zgtarm; clear - zgtarm; lra|].
                lra. }
              apply atan_increasing in zlta.
              rewrite atan_0 in zlta.
              split; lra.
              +++++ lra.
              +++++ exfalso.
              apply Rgt_lt,Rminus_lt in zgtarm.
              clear - zgtarm zgty1 zltr.
              lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                in *.
              assert (0 < A) as alt0. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (-0). setl (-( (- (2 * r - y₁)) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_involutive.
                  apply Ropp_lt_contravar.
                  rewrite Ropp_0.
                  lra.
                  setr (- x₁ * - x₁).
                  apply Rmult_lt_0_compat; lra.
                }

                apply Rlt_Rminus in ssa.

                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                apply Rlt_minus in sa.
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setl 0.
                setr (- x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (-PI/2 < atan A) in atl.
              clear atu.
              split; lra.
              +++++ lra.
              +++++ exfalso.
              apply Rgt_lt, Rminus_lt in zgtarm.
              clear - zgtarm zgty1 zltr.
              lra. 
     +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                in *.
              assert (0 < A) as alt0. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (-0). setl (-( (- (2 * r - y₁)) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_involutive.
                  apply Ropp_lt_contravar.
                  rewrite Ropp_0.
                  lra.
                  apply Rmult_lt_0_compat; lra.
                }

                apply Rlt_Rminus in ssa.

                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa;
                  [|left; assumption].
                apply Rlt_minus in sa.
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setl 0.
                setr (- x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (-PI/2 < atan A) in atl.
              change (atan A < PI/2) in atu.
              split; lra.
              +++++ split; intros; lra.
              +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                in *.
              assert (A < 0) as alt0. {
                assert ((x₁² - (2 * r - y₁) * y₁)< x₁²) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setl (0). setr ((- (2 * r - y₁)) * -y₁).
                  apply Rmult_lt_0_compat; lra.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.

                apply sqrt_lt_1 in sa;
                  [|left; assumption|apply Rle_0_sqr].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa;
                  [|left; assumption].

                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setr (-0).
                setl (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)));
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                apply Ropp_lt_contravar.
                lra. }
              
              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (-PI/2 < atan A) in atl.
              clear atu.
              split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
              rewrite <- zeqx1, Rminus_0_l in *.
              set (A := sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
              assert (A < 0) as zlta. {
                assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                  rewrite Rsqr_0, Rminus_0_l.
                  setr (- (2 * r - y₁) * y₁).
                  apply Rmult_lt_0_compat; [lra | assumption].
                }
                apply sqrt_lt_1 in inq ; [ | right; reflexivity | left; assumption].
                rewrite sqrt_0 in inq.

                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁)));[lra|].
                setr 0.
                setl (- sqrt (0² - (2 * r - y₁) * y₁));
                  [intro ae0; rewrite ae0 in zgtarm; clear - zgtarm; lra|].
                lra. }
              apply atan_increasing in zlta.
              rewrite atan_0 in zlta.
              split; lra.
              +++++ lra.
              +++++ exfalso. unfold straight, Tcx, Tcy in phase.
                rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                <- zeqx1, Rsqr_0, Rplus_0_l, Rsqr_minus in phase.
                apply (Rplus_lt_compat_r (- r²)) in phase.
                rewrite Rplus_opp_r in phase.
                assert (0 < - y₁ * (2 * r- y₁ )) as phase1. {
                  clear - phase.
                  setr (y₁² + r² - 2 * y₁ * r + - r²).
                  assumption. }
                apply (Rmult_lt_compat_l (-y₁)) in zgtarm; [|lra].
                rewrite Rmult_0_r in zgtarm.
                clear - phase1 zgtarm.
                lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *.
              assert (0 < A) as alt0. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁²)).
                  setl 0. setr ((-(2 * r - y₁) * y₁)).
                  apply Rmult_lt_0_compat; lra.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in ssa;
                  [|right; reflexivity|left; assumption].
                rewrite sqrt_0 in ssa.
                apply Ropp_lt_contravar in ssa.
                apply (Rplus_lt_compat_l x₁) in ssa.
                apply (Rlt_trans _ _ 0) in ssa; [|lra].
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setl 0.
                setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)));
                  [ intro an0; rewrite an0 in zgtarm; clear - zgtarm; lra|].
                clear - ssa.
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (atan A<PI/2) in atu.
              clear atl.
              split; lra.
              +++++ specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                                 / (2 * r - y₁)))) as [atl atu].
                set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (0 < A) as alt0. {
                unfold A.
                rewrite <- zeqy1, Rminus_0_r, Rmult_0_r, Rminus_0_r.
                apply (Rmult_lt_reg_r (2*- r)); try lra. 
                setl (0). setr (- (x₁ - sqrt x₁²)); try lra.
                rewrite sqrt_Rsqr_abs, Rabs_left; [| assumption].
                lra.
              }

              split. 
              apply atan_increasing in alt0.
              rewrite atan_0 in alt0.
              lra.
              lra.

              +++++ set (A := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *.
              assert (0 < A) as alt0. {
                assert ((x₁² - (2 * r - y₁) * y₁) < x₁²) as sa. {
                  apply (Rplus_lt_reg_r (- x₁²)).
                  setr 0. setl (-(- (2 * r - y₁) * - y₁)).
                  rewrite <- Ropp_0.
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; lra.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in ssa;
                  [|right; reflexivity|left; assumption].
                rewrite sqrt_0 in ssa.
                apply Ropp_lt_contravar in ssa.
                apply (Rplus_lt_compat_l x₁) in ssa.
                apply (Rlt_trans _ _ 0) in ssa; [|lra].
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setl 0.
                setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)));
                  [ intro an0; rewrite an0 in zgtarm; clear - zgtarm; lra|].
                clear - ssa.
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (atan A<PI/2) in atu.
              clear atl.
              split; lra.
Qed.

Lemma theta1_rsgn_bnd :
  forall x₁ y₁ r
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (0 < r -> 0 <= θ1 x₁ y₁ r < 2 * PI)/\
    (r < 0 -> - 2 * PI < θ1 x₁ y₁ r <= 0).
Proof.
  intros.
  specialize (theta1_rng _ _ _ rne0 phase) as [tlb tub].
  specialize (theta1_rsgn_lim _ _ _ rne0 phase) as [zltrc rlt0c].
  destruct (Rlt_dec 0 r) as [zltr |rle0].
  + specialize (zltrc zltr). split; lra.
  + apply Rnot_lt_le in rle0.
    destruct rle0 as [rlt0 | req0] ; [|exfalso; apply rne0; lra].
    specialize (rlt0c rlt0).
    lra.
Qed.

Lemma theta2_rng :
  forall x₁ y₁ r
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (- 2 * PI <= θ2 x₁ y₁ r <= 2 * PI).
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  assert (2 * PI > 0) as tpigt0; [lra|].

  unfold θ2.

  destruct (total_order_T 0 (2 * r - y₁))  as [[zltarm |zeqarm] |zgtarm].
  ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
                specialize (atan_bound (x₁ / r)) as [al au];
              set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
              split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
                set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
                split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                in *.
              assert (A < 0) as alt0. {
                assert ((x₁² - (2 * r - y₁) * y₁) < x₁²) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setl 0. setr ((2 * r - y₁) * y₁).
                  apply Rmult_lt_0_compat; assumption.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|left; assumption|apply Rle_0_sqr].
                rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                apply Rlt_minus in sa.
                rewrite minus_neg, Rplus_comm in sa.
                unfold A.
                apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                setr 0.
                setl (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                  [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                assumption. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (-PI/2 < atan A) in atl.
              clear atu.
              split; lra.
              +++++ split; lra.
              +++++ specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
                set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
                  split; lra.
     +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                 / (2 * r - y₁))) in *.
              assert (0 < A) as zlta. {
                specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sqp.
                unfold A.
                apply (Rmult_lt_reg_r (2 * r - y₁)); [assumption|].
                setl 0.
                setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                  [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                apply Rplus_lt_le_0_compat; assumption. }

              apply atan_increasing in zlta.
              apply (Rmult_lt_compat_l 2) in zlta; [|lra].
              rewrite atan_0, Rmult_0_r in zlta.
              specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (atan A< PI/2) in atu.
              clear atl.
              split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).
              +++++ specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
              rewrite <- zeqx1, Rplus_0_l in *.
              set (A := sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
              assert (0 < A) as zlta. {
                assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                  rewrite Rsqr_0, Rminus_0_l.
                  setr ((2 * r - y₁) * - y₁).
                  apply Rmult_lt_0_compat; [assumption| lra].
                }
                apply sqrt_lt_1 in inq ; [ | right; reflexivity | left; assumption].
                rewrite sqrt_0 in inq.
                unfold A.
                apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                setl 0.
                setr (sqrt (0² - (2 * r - y₁) * y₁));
                  [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                assumption. }
              apply atan_increasing in zlta.
              rewrite atan_0 in zlta.
              split; lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                in *.
              assert (0 < A) as alt0. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁²)).
                  setl 0. setr ((2 * r - y₁) * - y₁).
                  apply Rmult_lt_0_compat; [assumption|lra].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                apply Rlt_minus in sa.
                apply Ropp_lt_contravar in sa.
                rewrite Ropp_0 in sa.
                unfold A.
                apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                setl 0.
                setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                  [ intro an0; rewrite an0 in zltarm; clear - zltarm; lra|].
                clear - sa.
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (atan A<PI/2) in atu.
              clear atl.
              split; lra.
  ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
              set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
              split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
                set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
                split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
              set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
              split; lra).
              +++++ symmetry in zeqarm.
              apply Rminus_diag_uniq_sym in zeqarm.
              rewrite zeqarm.
              fieldrewrite (2 * r / (2 * x₁)) (r / x₁);
                [intro x1eq0; clear - x1eq0 zgtx1; lra|].
              assert (r / x₁ < 0) as an. {
                apply (Rmult_lt_reg_r (- x₁)); [lra|].
                setl (-r); [intro x1eq0; clear - x1eq0 zgtx1; lra|].
                rewrite Rmult_0_l.
                lra. }
              set (A:=r / x₁) in *.
              apply atan_increasing in an.
              apply (Rmult_lt_compat_l 2) in an; [|lra].
              rewrite atan_0, Rmult_0_r in an.
              specialize (atan_bound (A)) as [atl atu].
              clear atu.
              split; lra.
     +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
              set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
              split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
                set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
                split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu];
              set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *;
              split; lra).
              +++++ symmetry in zeqarm.
              apply Rminus_diag_uniq_sym in zeqarm.
              rewrite zeqarm.
              fieldrewrite (2 * r / (2 * x₁)) (r / x₁);
                [intro x1eq0; clear - x1eq0 zgtx1; lra|].
              assert (0<r / x₁ ) as an. {
                apply (Rmult_lt_reg_r (-x₁)); [lra|].
                setr (-r); [intro x1eq0; clear - x1eq0 zgtx1; lra|].
                rewrite Rmult_0_l.
                lra. }
              set (A:=r / x₁) in *.
              apply atan_increasing in an.
              apply (Rmult_lt_compat_l 2) in an; [|lra].
              rewrite atan_0, Rmult_0_r in an.
              specialize (atan_bound (A)) as [atl atu].
              clear atl.
              split; lra.
  ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                 / (2 * r - y₁))) in *.
              assert (A<0) as zlta. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (- 0). setl (-(- (2 * r - y₁) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_involutive.
                  apply Ropp_lt_contravar.
                  rewrite Ropp_0.
                  lra.
                  apply Rmult_lt_0_compat; assumption.
                }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa; [| left;lra].

                assert (0 < x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) as nps. {
                  apply Rplus_lt_le_0_compat.
                  assumption.
                  apply (Rle_trans _ x₁); left; assumption.
                }
                unfold A.
                apply (Rmult_lt_reg_r (- (2 * r - y₁))); try lra.
                setr 0.
                setl (- (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))) ;
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                lra. }

              apply atan_increasing in zlta.
              apply (Rmult_lt_compat_l 2) in zlta; [|lra].
              rewrite atan_0, Rmult_0_r in zlta.
              specialize (atan_bound (A)) as [atl atu].
              clear atu.
              split; lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).
              +++++ specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
              rewrite <- zeqx1, Rplus_0_l in *.
              set (A := sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
              assert (A < 0) as zlta. {
                assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                  rewrite Rsqr_0, Rminus_0_l.
                  setr (- (2 * r - y₁) * y₁).
                  apply Rmult_lt_0_compat; [lra | assumption].
                }
                apply sqrt_lt_1 in inq ; [ | right; reflexivity | left; assumption].
                rewrite sqrt_0 in inq.

                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁)));[lra|].
                setr 0.
                setl (- sqrt (0² - (2 * r - y₁) * y₁));
                  [intro ae0; rewrite ae0 in zgtarm; clear - zgtarm; lra|].
                lra. }
              apply atan_increasing in zlta.
              rewrite atan_0 in zlta.
              split; lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                in *.
              assert (A < 0) as alt0. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (-0). setl (-( (- (2 * r - y₁)) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_involutive.
                  apply Ropp_lt_contravar.
                  rewrite Ropp_0.
                  lra.
                  setr (- x₁ * - x₁).
                  apply Rmult_lt_0_compat; lra.
                }

                apply Rlt_Rminus in ssa.

                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                apply Rlt_minus in sa.
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setr 0.
                setl (- x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                assumption. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (-PI/2 < atan A) in atl.
              clear atu.
              split; lra.
     +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     specialize (atan_bound (x₁ / r)) as [al au];
                     set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     specialize (atan_bound (x₁ / r)) as [al au];
                     set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                try (specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                / (2 * r - y₁)))) as [atl atu];
                     set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *;
                     split; lra).
              +++++  set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *.
              assert (0 < A) as alt0. {
                assert ((x₁² - (2 * r - y₁) * y₁) < x₁²) as sa. {
                  apply (Rplus_lt_reg_r (- x₁²)).
                  setr 0. setl (-(- (2 * r - y₁) * - y₁)).
                  rewrite <- Ropp_0.
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; lra.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|left; assumption|apply Rle_0_sqr].
                rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                apply Rlt_minus in sa.
                apply Ropp_lt_contravar in sa.
                rewrite Ropp_0 in sa.
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setl 0.
                setr (- (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)));
                  [ intro an0; rewrite an0 in zgtarm; clear - zgtarm; lra|].
                clear - sa.
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (atan A<PI/2) in atu.
              clear atl.
              split; lra.
Qed.


Lemma theta2_rsgn_lim :
  forall x₁ y₁ r
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (0 < r -> 0 < θ2 x₁ y₁ r)/\(r < 0 -> θ2 x₁ y₁ r < 0).
Proof.
    intros.
    specialize PI_RGT_0 as pigt0.
    assert (2 * PI > 0) as tpigt0; [lra|].
    specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as nO.
    
    unfold θ2.

    destruct (total_order_T 0 (2 * r - y₁))  as [[zltarm |zeqarm] |zgtarm].
    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (0 < A) as alt0. {
                  assert ((x₁² - (2 * r - y₁) * y₁) < x₁²) as sa. {
                    apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                    setl 0. setr ((2 * r - y₁) * y₁).
                    apply Rmult_lt_0_compat; assumption.
                  }

                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in sa;
                    [|left; assumption|apply Rle_0_sqr].
                  rewrite sqrt_Rsqr_abs, Rabs_right in sa; try (left; lra).
                  apply Rlt_minus in sa.
                  
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setl 0.
                  setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                  apply Rplus_lt_le_0_compat; try assumption.
                  apply sqrt_pos. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (-PI/2 < atan A) in atl.
                clear atu.
                split; lra.
                +++++ split; [intro zltr2|intro rlt0; lra].
                assert (0 < x₁ / r) as ap. {
                  apply (Rmult_lt_reg_r r); [assumption|].
                  setl 0. setr x₁; assumption. }
                apply Rmult_lt_0_compat; [lra|].
                rewrite <- atan_0.
                apply atan_increasing.
                assumption.
                +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (0 < A) as alt0. {
                  assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                    apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                    setr 0. setl (-((2 * r - y₁) * - y₁)).
                    rewrite <- Ropp_0.
                    apply Ropp_lt_contravar.
                    apply Rmult_lt_0_compat; [ assumption|lra].
                  }

                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in sa;
                    [|apply Rle_0_sqr|left; assumption].
                  rewrite sqrt_Rsqr_abs, Rabs_right in sa; try lra.
                  apply Rlt_minus in sa.

                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setl 0.
                  setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                  apply Rplus_lt_le_0_compat; try assumption.
                  apply sqrt_pos. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (-PI/2 < atan A) in atl.
                clear atu.
                split; lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exfalso. unfold straight, Tcx, Tcy in phase.
                rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                <- zeqx1, Rsqr_0, Rplus_0_l, Rsqr_minus in phase.
                apply (Rplus_lt_compat_r (- r²)) in phase.
                rewrite Rplus_opp_r in phase.
                assert (0 < - y₁ * (2 * r- y₁ )) as phase1. {
                  clear - phase.
                  setr (y₁² + r² - 2 * y₁ * r + - r²).
                  assumption. }
                apply (Rmult_lt_compat_l (y₁)) in zltarm; try assumption.
                rewrite Rmult_0_r in zltarm.
                clear - phase1 zltarm.
                lra.
                +++++ exfalso. apply nO; split; lra.
                +++++ specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
              rewrite <- zeqx1, Rplus_0_l in *.
              set (A := sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
              assert (0 < A) as zlta. {
                assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                  rewrite Rsqr_0, Rminus_0_l.
                  setr ((2 * r - y₁) * - y₁).
                  apply Rmult_lt_0_compat; [assumption | lra ].
                }
                apply sqrt_lt_1 in inq ; [ | right; reflexivity | left; assumption].
                rewrite sqrt_0 in inq.

                unfold A.
                apply (Rmult_lt_reg_r ((2 * r - y₁)));[assumption|].
                setl 0.
                setr (sqrt (0² - (2 * r - y₁) * y₁));
                  [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                assumption. }
              apply atan_increasing in zlta.
              rewrite atan_0 in zlta.
              split; lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (A < 0) as alt0. {
                  assert ((x₁² - (2 * r - y₁) * y₁) < x₁²) as sa. {
                    apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                    setl 0. setr ((2 * r - y₁) * y₁).
                    apply Rmult_lt_0_compat; assumption.
                  }

                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in sa;
                    [|left; assumption|apply Rle_0_sqr].
                  rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                  apply Rlt_minus in sa.
                  rewrite minus_neg, Rplus_comm in sa.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setr 0.
                  setl (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                  assumption. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (-PI/2 < atan A) in atl.
                clear atu.
                split; lra.
                +++++ lra.
                +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (0 < A) as alt0. {
                  assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                    apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                    setr 0. setl (-((2 * r - y₁) * - y₁)).
                    rewrite <- Ropp_0.
                    apply Ropp_lt_contravar.
                    apply Rmult_lt_0_compat; [assumption|lra].
                  }
                  
                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in sa;
                    [|apply Rle_0_sqr|left; assumption].
                  rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                  apply Rlt_minus in sa.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setl 0.
                  setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ctr; rewrite ctr in zltarm; clear - zltarm; lra|].
                  lra. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (-PI/2 < atan A) in atl.
                clear atu.
                split; lra.

       +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (0 < A) as zlta. {
                  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sqp.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); [assumption|].
                  setl 0.
                  setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                  apply Rplus_lt_le_0_compat; assumption. }

                apply atan_increasing in zlta.
                apply (Rmult_lt_compat_l 2) in zlta; [|lra].
                rewrite atan_0, Rmult_0_r in zlta.
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (atan A< PI/2) in atu.
                clear atl.
                split; lra.
                +++++ lra.
                +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (0 < A) as zlta. {
                  specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sqp.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); [assumption|].
                  setl 0.
                  setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                    [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                  apply Rplus_lt_le_0_compat; assumption. }

                apply atan_increasing in zlta.
                apply (Rmult_lt_compat_l 2) in zlta; [|lra].
                rewrite atan_0, Rmult_0_r in zlta.
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (atan A< PI/2) in atu.
                clear atl.
                split; lra.
                
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                 / (2 * r - y₁)))) as [atl atu].
                rewrite <- zeqx1, Rplus_0_l in *.
                set (A := sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
                assert (0 < A) as zlta. {
                  assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                    rewrite Rsqr_0, Rminus_0_l.
                    setr ((2 * r - y₁) * - y₁).
                    apply Rmult_lt_0_compat; [assumption| lra].
                  }
                  apply sqrt_lt_1 in inq ;
                       [ | right; reflexivity | left; assumption].
                  rewrite sqrt_0 in inq.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setl 0.
                  setr (sqrt (0² - (2 * r - y₁) * y₁));
                    [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                  assumption. }
                apply atan_increasing in zlta.
                rewrite atan_0 in zlta.
                split; lra.
                +++++ lra.
                +++++ specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                                 / (2 * r - y₁)))) as [atl atu].
                rewrite <- zeqx1, Rplus_0_l in *.
                set (A := sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
                assert (0 < A) as zlta. {
                  assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                    rewrite Rsqr_0, Rminus_0_l.
                    setr ((2 * r - y₁) * - y₁).
                    apply Rmult_lt_0_compat; [assumption| lra].
                  }
                  apply sqrt_lt_1 in inq ;
                       [ | right; reflexivity | left; assumption].
                  rewrite sqrt_0 in inq.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setl 0.
                  setr (sqrt (0² - (2 * r - y₁) * y₁));
                    [intro ae0; rewrite ae0 in zltarm; clear - zltarm; lra|].
                  assumption. }
                apply atan_increasing in zlta.
                rewrite atan_0 in zlta.
                split; lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (0 < A) as alt0. {
                  assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                    apply (Rplus_lt_reg_r (- x₁²)).
                    setl 0. setr ((2 * r - y₁) * - y₁).
                    apply Rmult_lt_0_compat; [assumption|lra].
                  }

                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in sa;
                    [|apply Rle_0_sqr|left; assumption].
                  rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                  apply Rlt_minus in sa.
                  apply Ropp_lt_contravar in sa.
                  rewrite Ropp_0 in sa.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setl 0.
                  setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                    [ intro an0; rewrite an0 in zltarm; clear - zltarm; lra|].
                  clear - sa.
                  lra. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (atan A<PI/2) in atu.
                clear atl.
                split; lra.
                +++++ lra.
                +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                   / (2 * r - y₁))) in *.
                assert (0 < A) as alt0. {
                  assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                    apply (Rplus_lt_reg_r (- x₁²)).
                    setl 0. setr ((2 * r - y₁) * - y₁).
                    apply Rmult_lt_0_compat; [assumption|lra].
                  }

                  assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                    unfold straight, Tcx, Tcy in phase.
                    rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                    sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                    Rsqr_minus in phase.
                    apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                    setl r².
                    setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                    assumption. }

                  apply Rlt_Rminus in ssa.
                  apply sqrt_lt_1 in sa;
                    [|apply Rle_0_sqr|left; assumption].
                  rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                  apply Rlt_minus in sa.
                  apply Ropp_lt_contravar in sa.
                  rewrite Ropp_0 in sa.
                  unfold A.
                  apply (Rmult_lt_reg_r (2 * r - y₁)); try assumption.
                  setl 0.
                  setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁));
                    [ intro an0; rewrite an0 in zltarm; clear - zltarm; lra|].
                  clear - sa.
                  lra. }

                apply atan_increasing in alt0.
                apply (Rmult_lt_compat_l 2) in alt0; [|lra].
                rewrite atan_0, Rmult_0_r in alt0.
                specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                           / (2 * r - y₁)))) as [atl atu].
                change (atan A<PI/2) in atu.
                clear atl.
                split; lra.
    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ symmetry in zeqarm.
              apply Rminus_diag_uniq_sym in zeqarm.
              rewrite zeqarm.
              fieldrewrite (2 * r / (2 * x₁)) (r / x₁);
                [intro x1eq0; clear - x1eq0 zgtx1; lra|].
              assert (r / x₁ < 0) as an. {
                apply (Rmult_lt_reg_r (- x₁)); [lra|].
                setl (-r); [intro x1eq0; clear - x1eq0 zgtx1; lra|].
                rewrite Rmult_0_l.
                lra. }
              set (A:=r / x₁) in *.
              apply atan_increasing in an.
              apply (Rmult_lt_compat_l 2) in an; [|lra].
              rewrite atan_0, Rmult_0_r in an.
              specialize (atan_bound (A)) as [atl atu].
              clear atu.
              split; lra.
              +++++ lra.
              +++++ exfalso.
              symmetry in zeqarm.
              apply Rminus_diag_uniq in zeqarm.
              symmetry in zeqarm.
              rewrite zeqarm in zgty1.
              clear - zgty1 zltr.
              lra.
     +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1]; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ exfalso.
              symmetry in zeqarm.
              apply Rminus_diag_uniq in zeqarm.
              symmetry in zeqarm.
              rewrite zeqarm in zlty1.
              clear - zlty1 zgtr.
              lra.
              +++++ lra.
              +++++ symmetry in zeqarm.
              apply Rminus_diag_uniq_sym in zeqarm.
              rewrite zeqarm.
              fieldrewrite (2 * r / (2 * x₁)) (r / x₁);
                [intro x1eq0; clear - x1eq0 zgtx1; lra|].
              assert (0<r / x₁ ) as an. {
                apply (Rmult_lt_reg_r (-x₁)); [lra|].
                setr (-r); [intro x1eq0; clear - x1eq0 zgtx1; lra|].
                rewrite Rmult_0_l.
                lra. }
              set (A:=r / x₁) in *.
              apply atan_increasing in an.
              apply (Rmult_lt_compat_l 2) in an; [|lra].
              rewrite atan_0, Rmult_0_r in an.
              specialize (atan_bound (A)) as [atl atu].
              clear atl.
              split; lra.
    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                 / (2 * r - y₁))) in *.
              assert (A<0) as zlta. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (- 0). setl (-(- (2 * r - y₁) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_involutive.
                  apply Ropp_lt_contravar.
                  rewrite Ropp_0.
                  lra.
                  apply Rmult_lt_0_compat; assumption.
                }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa; [| left;lra].

                assert (0 < x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) as nps. {
                  apply Rplus_lt_le_0_compat.
                  assumption.
                  apply (Rle_trans _ x₁); left; assumption.
                }
                unfold A.
                apply (Rmult_lt_reg_r (- (2 * r - y₁))); try lra.
                setr 0.
                setl (- (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))) ;
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                lra. }

              apply atan_increasing in zlta.
              apply (Rmult_lt_compat_l 2) in zlta; [|lra].
              rewrite atan_0, Rmult_0_r in zlta.
              specialize (atan_bound (A)) as [atl atu].
              clear atu.
              split; lra.
              +++++ lra.
              +++++ exfalso.
              apply Rgt_lt, Rminus_lt in zgtarm.
              clear - zgtarm zgty1 zltr.
              lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
              rewrite <- zeqx1, Rplus_0_l in *.
              set (A := sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
              assert (A < 0) as zlta. {
                assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                  rewrite Rsqr_0, Rminus_0_l.
                  setr (- (2 * r - y₁) * y₁).
                  apply Rmult_lt_0_compat; [lra | assumption].
                }
                apply sqrt_lt_1 in inq ; [ | right; reflexivity | left; assumption].
                rewrite sqrt_0 in inq.

                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁)));[lra|].
                setr 0.
                setl (- sqrt (0² - (2 * r - y₁) * y₁));
                  [intro ae0; rewrite ae0 in zgtarm; clear - zgtarm; lra|].
                lra. }
              apply atan_increasing in zlta.
              rewrite atan_0 in zlta.
              split; lra.
              +++++ lra.
              +++++ exfalso.
              apply Rgt_lt,Rminus_lt in zgtarm.
              clear - zgtarm zgty1 zltr.
              lra.

         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                in *.
              assert (A < 0) as alt0. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (-0). setl (-( (- (2 * r - y₁)) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_involutive.
                  apply Ropp_lt_contravar.
                  rewrite Ropp_0.
                  lra.
                  setr (- x₁ * - x₁).
                  apply Rmult_lt_0_compat; lra.
                }

                apply Rlt_Rminus in ssa.

                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                apply Rlt_minus in sa.
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setr 0.
                setl (- x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                assumption. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (-PI/2 < atan A) in atl.
              clear atu.
              split; lra.
              +++++ lra.
              +++++ exfalso.
              apply Rgt_lt, Rminus_lt in zgtarm.
              clear - zgtarm zgty1 zltr.
              lra. 
     +++ exfalso; apply rne0; rewrite <- zeqr; reflexivity.
     +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                in *.
              assert (A < 0) as alt0. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setr (-0). setl (-( (- (2 * r - y₁)) * y₁)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; [lra|assumption].
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  apply (Rlt_trans _ 0).
                  setl (- ((-(2 * r - y₁)) * y₁)).
                  rewrite <- Ropp_involutive.
                  apply Ropp_lt_contravar.
                  rewrite Ropp_0.
                  lra.
                  apply Rmult_lt_0_compat; lra.
                }

                apply Rlt_Rminus in ssa.

                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa;
                  [|left; assumption].
                apply Rlt_minus in sa.
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setr 0.
                setl (- x₁ - sqrt (x₁² - (2 * r - y₁) * y₁));
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (-PI/2 < atan A) in atl.
              clear atu.
              split; lra.
              +++++ split; [intro zltr; lra|intro rlt0].
                assert (x₁ / r < 0 ) as ap. {
                  apply (Rmult_lt_reg_r (-r)); [lra|].
                  setr 0. setl (-x₁). auto. lra. }
                setl (- (2 * (- atan (x₁ / r)))).
                rewrite <- Ropp_0.
                apply Ropp_lt_contravar.
                apply Rmult_lt_0_compat; [lra|].
                rewrite <- Ropp_0.
                apply Ropp_lt_contravar.
                rewrite <- atan_0.
                apply atan_increasing.
                assumption.
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                in *.
              assert (A < 0) as alt0. {
                assert ((x₁² - (2 * r - y₁) * y₁)< x₁²) as sa. {
                  apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                  setl (0). setr ((- (2 * r - y₁)) * -y₁).
                  apply Rmult_lt_0_compat; lra.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.

                apply sqrt_lt_1 in sa;
                  [|left; assumption|apply Rle_0_sqr].
                rewrite sqrt_Rsqr_abs, Rabs_right in sa;
                  [|left; assumption].
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setr (-0).
                setl (- (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)));
                  [intro ctr; rewrite ctr in zgtarm; clear - zgtarm; lra|].
                apply Ropp_lt_contravar. 
                apply Rplus_lt_le_0_compat; try assumption.
                apply sqrt_pos. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (-PI/2 < atan A) in atl.
              clear atu.
              split; lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                               / (2 * r - y₁)))) as [atl atu].
              rewrite <- zeqx1, Rplus_0_l in *.
              set (A := sqrt (0² - (2 * r - y₁) * y₁) / (2 * r - y₁)) in *.
              assert (A < 0) as zlta. {
                assert (0 < (0² - (2 * r - y₁) * y₁)) as inq. {
                  rewrite Rsqr_0, Rminus_0_l.
                  setr (- (2 * r - y₁) * y₁).
                  apply Rmult_lt_0_compat; [lra | assumption].
                }
                apply sqrt_lt_1 in inq ; [ | right; reflexivity | left; assumption].
                rewrite sqrt_0 in inq.

                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁)));[lra|].
                setr 0.
                setl (- sqrt (0² - (2 * r - y₁) * y₁));
                  [intro ae0; rewrite ae0 in zgtarm; clear - zgtarm; lra|].
                lra. }
              apply atan_increasing in zlta.
              rewrite atan_0 in zlta.
              split; lra.
              +++++ lra.
              +++++ exfalso. unfold straight, Tcx, Tcy in phase.
                rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                <- zeqx1, Rsqr_0, Rplus_0_l, Rsqr_minus in phase.
                apply (Rplus_lt_compat_r (- r²)) in phase.
                rewrite Rplus_opp_r in phase.
                assert (0 < - y₁ * (2 * r- y₁ )) as phase1. {
                  clear - phase.
                  setr (y₁² + r² - 2 * y₁ * r + - r²).
                  assumption. }
                apply (Rmult_lt_compat_l (-y₁)) in zgtarm; [|lra].
                rewrite Rmult_0_r in zgtarm.
                clear - phase1 zgtarm.
                lra.
         ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *.
              assert (A < 0) as alt0. {
                assert (x₁² < (x₁² - (2 * r - y₁) * y₁)) as sa. {
                  apply (Rplus_lt_reg_r (- x₁²)).
                  setl 0. setr ((-(2 * r - y₁) * y₁)).
                  apply Rmult_lt_0_compat; lra.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|apply Rle_0_sqr|left; assumption].
                rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                apply Rlt_minus in sa.
                apply Ropp_lt_contravar in sa.
                rewrite Ropp_0 in sa.
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setr 0.
                setl (- (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)));
                  [ intro an0; rewrite an0 in zgtarm; clear - zgtarm; lra|].
                clear - sa.
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (atan A<PI/2) in atu.
              clear atl.
              split; lra.
              +++++ lra.
              +++++ set (A := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                  / (2 * r - y₁))) in *.
              assert (0 < A) as alt0. {
                assert ((x₁² - (2 * r - y₁) * y₁) < x₁²) as sa. {
                  apply (Rplus_lt_reg_r (- x₁²)).
                  setr 0. setl (-(- (2 * r - y₁) * - y₁)).
                  rewrite <- Ropp_0.
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; lra.
                }

                assert ((2 * r - y₁) * y₁ < x₁²) as ssa. {
                  unfold straight, Tcx, Tcy in phase.
                  rewrite Rplus_0_l, Rplus_0_l, Rplus_0_r,
                  sin_PI2, cos_PI2, Rmult_0_r, Rmult_1_r, Rminus_0_r,
                  Rsqr_minus in phase.
                  apply (Rplus_lt_reg_r (r² - (2 * r - y₁) * y₁)).
                  setl r².
                  setr (x₁² + (y₁² + r² - 2 * y₁ * r)).
                  assumption. }

                apply Rlt_Rminus in ssa.
                apply sqrt_lt_1 in sa;
                  [|left; assumption|apply Rle_0_sqr].
                rewrite sqrt_Rsqr_abs, Rabs_left in sa; try assumption.
                apply Rlt_minus in sa.
                apply Ropp_lt_contravar in sa.
                rewrite Ropp_0 in sa.
                unfold A.
                apply (Rmult_lt_reg_r (-(2 * r - y₁))); try lra.
                setl 0.
                setr (- (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)));
                  [ intro an0; rewrite an0 in zgtarm; clear - zgtarm; lra|].
                clear - sa.
                lra. }

              apply atan_increasing in alt0.
              apply (Rmult_lt_compat_l 2) in alt0; [|lra].
              rewrite atan_0, Rmult_0_r in alt0.
              specialize (atan_bound (((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))
                                         / (2 * r - y₁)))) as [atl atu].
              change (atan A<PI/2) in atu.
              clear atl.
              split; lra.
Qed.

Lemma theta2_rsgn_bnd :
  forall x₁ y₁ r
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (0 < r -> 0 < θ2 x₁ y₁ r <= 2 * PI)/\
    (r < 0 -> - 2 * PI <= θ2 x₁ y₁ r < 0).
Proof.
  intros.
  specialize (theta2_rng _ _ _ rne0 phase) as [tlb tub].
  specialize (theta2_rsgn_lim _ _ _ rne0 phase) as [zltrc rlt0c].
  destruct (Rlt_dec 0 r) as [zltr |rle0].
  + specialize (zltrc zltr). split; lra.
  + apply Rnot_lt_le in rle0.
    destruct rle0 as [rlt0 | req0] ; [|exfalso; apply rne0; lra].
    specialize (rlt0c rlt0).
    lra.
Qed.

(* begin hide *)
Lemma k_deriv_sign_lin :
  forall x₁ y₁ r z
         (rne0 : r <> 0)
         (phase :  straight r 0 0 0 x₁ y₁)
         (xne0 : x₁ <> 0)
         (Ane0 : 2 * r - y₁ = 0),
    z = 2 * atan ( y₁ / (2 * x₁)) \/ z = PI ->
    sign (κ' x₁ y₁ r z) = 0.
Proof.
  intros until 4.
  intro z2d.

  destruct z2d as [z2d |zPI].
  + assert (-PI < z < PI) as zrng. {
      specialize (atan_bound ( y₁ / (2*x₁))) as [atl atu].
      lra. }
    
    rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase), Ane0, Rmult_0_l, Rminus_0_l.
    rewrite sign_mult.
    apply Rmult_eq_0_compat_l.
    unfold sign.
    destruct (total_order_T 0 (- (2 * x₁ * tan (z / 2)) + y₁)).
    destruct s.
    
    exfalso.
    rewrite z2d in r0.
    assert (2 * atan (y₁ / (2 * x₁)) / 2 = atan (y₁ / (2 * x₁))) as id. field.
    rewrite id in r0. clear id.
    rewrite atan_right_inv in r0.
    assert (- (2 * x₁ * (y₁ / (2 * x₁))) + y₁ = 0) as id.
    field. assumption. rewrite id in r0. clear - r0. lra.
    reflexivity.
    
    exfalso.
    rewrite z2d in r0. 
    assert (2 * atan (y₁ / (2 * x₁)) / 2 = atan (y₁ / (2 * x₁))) as id. field.
    rewrite id in r0. clear id.
    rewrite atan_right_inv in r0.
    assert (- (2 * x₁ * (y₁ / (2 * x₁))) + y₁ = 0) as id.
    field. assumption. rewrite id in r0. clear - r0. lra.
  + rewrite zPI.
    rewrite k_deriv_sign_PI; try assumption.
    fieldrewrite (- y₁ + r * 2) (2 * r - y₁).
    rewrite Ane0, Rmult_0_r.
    apply sign_0.
Qed.


Lemma k_deriv_sign_lin_xeq0 :
  forall x₁ y₁ r z
         (rne0 : r <> 0)
         (phase :  straight r 0 0 0 x₁ y₁)
         (xeq0 : x₁ = 0)
         (Ane0 : 2 * r - y₁ = 0)
         (zrng :-PI < z < PI),
    sign (κ' x₁ y₁ r z) <> 0.
Proof.
  intros.
  rewrite (k_deriv_sign_rng _ _ _ _ zrng rne0 phase),
  Ane0, Rmult_0_l, Rminus_0_l,
  xeq0, Rmult_0_r, Rmult_0_l, Ropp_0, Rplus_0_l.
  rewrite sign_mult.
  intro smz.
  apply Rmult_integral in smz.
  destruct smz as [rz | y1z].
  unfold sign in rz.
  destruct (total_order_T 0 r);
    [destruct s|]; lra.
  unfold sign in y1z.
  destruct (total_order_T 0 y₁);
    [destruct s|]; lra.
Qed.


Lemma condstraight : forall r x y,
    (2 * r * y < x² + y²) -> straight r 0 0 0 x y.
Proof.
  intros.
  unfold straight, Tcy, Tcx.
  rewrite Rplus_0_r, sin_PI2, cos_PI2, Rmult_0_r,
  Rplus_0_l, Rplus_0_l, Rminus_0_r, Rmult_1_r.
  rewrite Rsqr_minus.
  apply (Rplus_lt_reg_r (-r²)).
  setl 0. setr (x² + y² - 2 * y * r).
  lra.
Qed.
  

Ltac qmL :=
  match goal with
  | zd : ?z = 2 * atan ((?x - sqrt ((?x)² - ?arm * ?y)) / ?arm) +
              2 * IZR ?m * PI |- _ =>
    rewrite (k'_periodic _ _ _ (-m%Z));
    apply (k_deriv_sign_quad);
    [assumption| assumption| lra|left; rewrite opp_IZR, zd; field]
  | zd : ?z = 2 * atan ((?x + sqrt ((?x)² - ?arm * ?y)) / ?arm) +
              2 * IZR ?m * PI |- _ =>
    rewrite (k'_periodic _ _ _ (-m%Z));
    apply (k_deriv_sign_quad);
    [assumption| assumption| lra|right; rewrite opp_IZR, zd; field]
  | zd : ?z = 2 * atan ((?x + sqrt ((?x)² - ?arm * ?y)) / ?arm) +
              2 * 1 * PI + 2 * IZR ?m * PI |- _ =>
    rewrite (k'_periodic _ _ _ (-(m+1)%Z));
    apply (k_deriv_sign_quad);
    [assumption| assumption| lra|right; rewrite opp_IZR, plus_IZR, zd; field]
  | zd : ?z = 2 * atan ((?x + sqrt ((?x)² - ?arm * ?y)) / ?arm) -
              2 * 1 * PI + 2 * IZR ?m * PI |- _ =>
    rewrite (k'_periodic _ _ _ (1-m)%Z);
    apply (k_deriv_sign_quad);
    [assumption| assumption| lra|right; rewrite minus_IZR, zd; field]
  | zd : ?z = 2 * atan ((?x - sqrt ((?x)² - ?arm * ?y)) / ?arm) +
              2 * 1 * PI + 2 * IZR ?m * PI |- _ =>
    rewrite (k'_periodic _ _ _ (-(m+1)%Z));
    apply (k_deriv_sign_quad);
    [assumption| assumption| lra|left; rewrite opp_IZR, plus_IZR, zd; field]
  | zd : ?z = 2 * atan ((?x - sqrt ((?x)² - ?arm * ?y)) / ?arm) -
              2 * 1 * PI + 2 * IZR ?m * PI |- _ =>
    rewrite (k'_periodic _ _ _ (1-m)%Z);
    apply (k_deriv_sign_quad);
    [assumption| assumption| lra|left; rewrite minus_IZR, zd; field]
  | id : ?z = 0 + 2 * IZR ?m * PI,
    zeqy : 0 = ?y,
    phase : straight ?r 0 0 0 ?x ?y |- _ =>
    rewrite id;
    rewrite <- k'_periodic;
    rewrite k_deriv_sign_0; try assumption;
    rewrite <- zeqy, Rmult_0_r;
    apply sign_0
  | id : ?z = 2 * PI + 2 * IZR ?m * PI,
    zeqy : 0 = ?y,
    phase : straight ?r 0 0 0 ?x ?y |- _ =>
    rewrite id;
    fieldrewrite (2 * PI + 2 * IZR m * PI) (0 + 2 * (IZR m + IZR 1) * PI);
    rewrite <- plus_IZR;
    rewrite <- k'_periodic;
    rewrite k_deriv_sign_0; try assumption;
    rewrite <- zeqy, Rmult_0_r;
    apply sign_0
  | id : ?z = -2 * PI + 2 * IZR ?m * PI,
    zeqy : 0 = ?y,
    phase : straight ?r 0 0 0 ?x ?y |- _ =>
    rewrite id;
    fieldrewrite (-2 * PI + 2 * IZR m * PI) (0 + 2 * (IZR m - IZR 1) * PI);
    rewrite <- minus_IZR;
    rewrite <- k'_periodic;
    rewrite k_deriv_sign_0; try assumption;
    rewrite <- zeqy, Rmult_0_r;
    apply sign_0
  | phase : straight ?r 0 0 0 ?x ?y,
    zeqx : 0 = ?x,
    zeqa : 0 = 2 * ?r - ?y |- _ => 
    exfalso;
    clear - phase zeqa zeqx;
    apply straightcond in phase;
    symmetry in zeqa;
    apply Rminus_diag_uniq in zeqa;
    symmetry in zeqa, zeqx;
    rewrite zeqx, zeqa, Rsqr_0, Rplus_0_l in phase;
    change ((2 * r)² < (2 * r)²) in phase;
    lra
  | phase : straight ?r 0 0 0 ?x ?y,
    zd : ?z = 2 * atan (?y / (2 * ?x)) + 2 * IZR ?m * PI,
    rne0 : ?r <> 0 |- _ => 
    rewrite (k'_periodic _ _ _ (-m%Z)), opp_IZR;
    apply (k_deriv_sign_lin _ _ _ _ rne0 phase); try lra
  | phase : straight ?r 0 0 0 ?x ?y,
    zd : ?z = 2 * atan (?y / (2 * ?x)) +
              2 * IZR 1 * PI + 2 * IZR ?m * PI,
    rne0 : ?r <> 0 |- _ => 
    rewrite (k'_periodic _ _ _ (-(m+1)%Z)), opp_IZR, plus_IZR;
    apply (k_deriv_sign_lin _ _ _ _ rne0 phase); try lra
  | phase : straight ?r 0 0 0 ?x ?y,
    zd : ?z = 2 * atan (?y / (2 * ?x)) -
              2 * IZR 1 * PI + 2 * IZR ?m * PI,
    rne0 : ?r <> 0 |- _ => 
    rewrite (k'_periodic _ _ _ (1-m)%Z), minus_IZR;
    apply (k_deriv_sign_lin _ _ _ _ rne0 phase); try lra
  | phase : straight ?r 0 0 0 ?x ?y,
    zd : ?z = PI + 2 * IZR ?m * PI,
    rne0 : ?r <> 0 |- _ => 
    rewrite (k'_periodic _ _ _ (-m%Z)), opp_IZR;
    apply (k_deriv_sign_lin _ _ _ _ rne0 phase); try lra
  | phase : straight ?r 0 0 0 ?x ?y,
    zd : ?z = - PI + 2 * IZR ?m * PI,
    rne0 : ?r <> 0 |- _ =>
    assert (z = PI + 2 * IZR (m-1) * PI) as id;
    [rewrite minus_IZR, zd; field | qmL]
  | phase : straight ?r 0 0 0 ?x ?y,
    zd : ?z = 2 * atan (?x / ?r) + 2 * IZR ?m * PI,
    zeq0 : 0 = ?y,
    rne0 : ?r <> 0 |- _ =>
    rewrite zd;
    rewrite <- k'_periodic;
    apply (k_deriv_sign_quad);
    [assumption|assumption|lra|right];
    rewrite <- zeq0, Rmult_0_r, Rminus_0_r, Rminus_0_r, sqrt_Rsqr;
    [fieldrewrite ((x + x) / (2 * r)) (x / r);
     [assumption| field]
    |left; assumption]
  (* | _ => idtac *)
  end.

Ltac dqmL :=
  let zlt := fresh "zlt" in
  let zeq := fresh "zeq" in
  let zgt := fresh "zgt" in 
  match goal with
  | H : ?z = match ?P with _ => _ end + _ \/ _ |- _ =>
    destruct P as [[zlt|zeq]|zgt]; dqmL
  | zd : ?z = ?A \/ ?z = ?B |- _ =>
    destruct zd as [zd|zd]; qmL
  end.

Theorem theta1_theta2_k_deriv: forall (x y r z :R) (m:Z),
       r <> 0 ->
       straight r 0 0 0 x y ->
       z = θ1 x y r + 2 * IZR m * PI \/
       z = θ2 x y r + 2 * IZR m * PI -> 
       sign (κ' x y r z) = 0.
Proof.
  intros *.
  intros rne0 phase zd.
  unfold θ1,θ2 in *.
  destruct (total_order_T 0 r) as [[zltr|zeqr]|zgtr].
  + dqmL.
  + clear - rne0 zeqr; lra.
  + dqmL.
Qed.

(* end hide *)
Lemma k_deriv_k2 : forall x y r z
      (rne0 : r <> 0)
      (phase :  straight r 0 0 0 x y),
      sign (κ' x y r z) = 0 -> 
      exists n, κ₂ x y r z = z + IZR n * PI.
Proof.
  intros.

  specialize PI_RGT_0 as pigt0.
  assert (2 * PI > 0) as tpigt0. lra.
  
  unfold κ' in H.
  rewrite sign_eq_pos_den in H.
  + rewrite signeq0_eqv in H.
    assert (sin z * (x - r * sin z) = cos z * (y - r * (1 - cos z))) as EQ1.
    { apply (Rmult_eq_reg_l r _ _); lra. }
    clear H.
    unfold κ₂.
    assert (exists m, -PI < z + 2 * (IZR m) * PI <= PI) as BD1.
    { specialize (inrange_mT2T2 z _ tpigt0) as [k [rl ru]].
      assert (IZR k * (2 * PI) = 2 * IZR k * PI) as id.
      field. rewrite id in rl,ru. clear id.
      exists k.
      split ;lra. }
    inversion_clear BD1 as [m BD2].
    destruct (Req_dec (cos z) 0) as [coseq0 | cosneq0].
    ++ specialize (coseq0_sinneq0 _ coseq0) as sinneq0.
       rewrite coseq0, Rmult_0_l in EQ1.
       destruct (Rmult_integral _ _ EQ1) as [TMP| x1eq0]; [contradiction| setoid_rewrite x1eq0].
       specialize (straight_std_impl_ineq _ _ _ phase) as TMP1.
       assert (0 < (x - r)*(x + r) + (y - r)²) as phase'.
       { rewrite Rsqr_minus_plus; lra. }
       clear TMP1.
       assert ( z + 2 * IZR m * PI = PI/2 \/  z + 2 * IZR m * PI = -(PI/2)) as zval.
       { rewrite <-(cos_period1 _ m) in coseq0.
         rewrite <- Ropp_div.
         apply cosθeq0; auto.
       }
       clear sinneq0.
       assert (y - r <> 0) as INEQ1.
       { destruct zval as [zval|zval]; rewrite <- (sin_period1 _ m), zval in x1eq0;
           [|rewrite sin_neg in x1eq0]; rewrite sin_PI2 in x1eq0;
             [| rewrite Ropp_mult_distr_r_reverse, minus_neg in x1eq0];
             rewrite Rmult_1_r in x1eq0; rewrite x1eq0 in *;
               [rewrite Rmult_0_l in *| rewrite Rmult_0_r in *];
               rewrite Rplus_0_l in *; apply Rsqr_gt_0_0 in phase'; auto.
       }
       setoid_rewrite coseq0; setoid_rewrite Rminus_0_r; setoid_rewrite Rmult_1_r.
       destruct (total_order_T 0 (y - r)) as [[ymrlt0 | ymreq0] | ymrgt0].
       +++ destruct zval.
           ++++ exists (2 * m)%Z; rewrite atan2_PI2; auto.
                rewrite mult_IZR; lra.
           ++++ exists (2 * m + 1)%Z; rewrite atan2_PI2; auto.
                rewrite plus_IZR, mult_IZR; lra.
       +++ exfalso; symmetry in ymreq0; contradiction.
       +++ apply Rgt_lt in ymrgt0; destruct zval.
           ++++ exists (2 * m - 1)%Z; rewrite atan2_mPI2; auto.
                rewrite minus_IZR, mult_IZR; lra.
           ++++ exists (2 * m)%Z; rewrite atan2_mPI2; auto.
                rewrite mult_IZR; lra.
    ++ assert ((y - r * (1 - cos z)) = ((((x - r * sin z)) * (/(cos z)))) * sin z) as EQ2.
       { apply (Rmult_eq_reg_l (cos z)); auto.
         repeat rewrite <- Rmult_assoc.
         rewrite Rinv_r_simpl_m; lra.
       }
       setoid_rewrite EQ2.
       assert (x - r * sin z = ((x - r * sin z) * / cos z) * cos z) as EQ3.
       { rewrite Rmult_assoc, Rinv_l. lra.  assumption. }
       setoid_rewrite EQ3 at 2.
       destruct (total_order_T 0 ((x - r * sin z) * / (cos z))) as [[valgt0 | valeq0] | vallt0].
       +++ exists (2 * m)%Z.
           rewrite <- (sin_period1 z m), <- (cos_period1 z m) in *.
           rewrite atan2_left_inv; auto.
           rewrite mult_IZR; reflexivity.
       +++ exfalso.
           specialize (Rinv_neq_0_compat _ cosneq0) as NEQ1.
           symmetry in valeq0.
           destruct (Rmult_integral _ _ valeq0) as [CONTR1 | CONTR2]; exfalso; auto.
           rewrite CONTR1, Rmult_0_r in EQ1.
           symmetry in EQ1.
           destruct (Rmult_integral _ _ EQ1) as [CONTR2 | CONTR3]; exfalso; auto.
           specialize (straightcond _ _ _ phase) as phase''.
           assert (x = r * sin z) as CONTR1'.
           { lra. }
           clear CONTR1.
           assert (y = r * (1 - cos z)) as CONTR3'.
           { lra. }
           clear CONTR3.
           rewrite CONTR1', CONTR3' in phase''.
           clear CONTR1' CONTR3'.
           assert ((r * sin z)² + (r * (1 - cos z))² = 2 * r * (r * (1 - cos z))) as CONTR.
           { fieldrewrite ((r * sin z)² + (r * (1 - cos z))²) (r² * (1 - 2 * cos z + ((sin z)² + (cos z)²))).
             rewrite sin2_cos2.
             unfold Rsqr; lra.
           }
           rewrite CONTR in phase''.
           lra.
       +++ apply Rgt_lt in vallt0.
           destruct (Rlt_le_dec 0 (z + 2 * IZR m * PI)) as [zgt0 | zle0].
           ++++ exists (2 * m - 1)%Z.
                rewrite <-(sin_period1 _ m) at 2.
                rewrite <-(cos_period1 _ m) at 3.
                rewrite atan2_left_inv_neg_pos, minus_IZR, mult_IZR; lra.
           ++++ exists (2 * m + 1)%Z.
                rewrite <-(sin_period1 _ m) at 2.
                rewrite <-(cos_period1 _ m) at 3.
                rewrite atan2_left_inv_neg_npos, plus_IZR, mult_IZR; lra.
  + specialize (str_noton _ _ _ phase z) as NOTON.
    assert (0 <= (y - r * (1 - cos z))² + (x - r * sin z)²) as LETARGET.
    { apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
    destruct LETARGET as [LETARGET | CONTR]; auto.
    exfalso.
    symmetry in CONTR.
    destruct (Rplus_sqr_eq_0 _ _ CONTR) as [CONTR1 CONTR2].
    rewrite CONTR1, CONTR2 in NOTON; apply NOTON; split; auto.
Qed.



Lemma theta1_theta2_k2 :
  forall m x₁ y₁ r θ
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    θ = θ1 x₁ y₁ r + 2 * IZR m * PI \/
    θ = θ2 x₁ y₁ r + 2 * IZR m * PI ->
    exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR n * PI.
Proof.
  intros until 2.
  intros roots.
  apply k_deriv_k2; try assumption.
  eapply theta1_theta2_k_deriv; try eassumption.
Qed.
(* begin hide *)

Ltac shweq k :=
  match goal with
  | |- _ => exists (-k)%Z;
            rewrite opp_IZR;
            left;
            field
  | |- _ => exists (-k)%Z;
            rewrite opp_IZR;
            right;
            field
  | |- _ => exists (-k-1)%Z;
            right;
            rewrite minus_IZR, opp_IZR;
            field
  | |- _ => exists (-k-1)%Z;
            left;
            rewrite minus_IZR, opp_IZR;
            field
  | |- _ => exists (-k +1)%Z;
            right;
            rewrite plus_IZR, opp_IZR;
            field
  | |- _ => exists (-k +1)%Z;
            left;
            rewrite plus_IZR, opp_IZR;
            field
  | e : 0 = ?y, zltx : 0 < ?x |-
    context [sqrt (?x² - (2 * ?r - ?y) * ?y) ] =>
    rewrite <- e;
    arn;
    rewrite sqrt_Rsqr;
    [|lra];
    rewrite Rminus_eq_0;
    fieldrewrite (0 / (2 * r)) 0;
    [assumption|
     rewrite atan_0; arn]; shweq k
  | e : 0 = ?y, e0 : 0 = ?x |-
    context [sqrt (?x² - (2 * ?r - ?y) * ?y) ] =>
    rewrite <- e, <- e0;
    arn;
    fieldrewrite (0 / (2 * r)) 0;
    [lra|
     rewrite atan_0;
     arn]; shweq k
  | e : 0 = ?y, e0 : 0 < ?x |-
    context [sqrt (?x² - (2 * ?r - ?y) * ?y) ] =>
    rewrite <- e;
    arn;
    rewrite sqrt_Rsqr;
    [|lra];
    fieldrewrite ((x+x)/(2*r)) (x/r);
    [lra|]; shweq k
  | e : 0 = ?y, e0 : 0 > ?x |-
    context [sqrt (?x² - (2 * ?r - ?y) * ?y) ] =>
    rewrite <- e;
    arn;
    rewrite Rsqr_neg;
    rewrite sqrt_Rsqr;
    [|lra];
    fieldrewrite ((x+ - x)/(2*r)) (0);
    [lra|rewrite atan_0];
    arn; shweq k
  end.

Ltac kpt1t2h1 k :=
  let s := fresh "s" in
  let e := fresh "e" in
  match goal with
  | |- _ => destruct total_order_T as [s | e];
            [destruct s|]; try lra; kpt1t2h1 k
  | |- _ => shweq k
  | |- _ => idtac
  end.


(* end hide *)
Lemma k_prime_theta1_theta2 :
  forall x y r θ
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x y)
         (ksg0 : sign (κ' x y r θ) = 0),
  exists (n:Z), θ = θ1 x y r + 2 * IZR n * PI \/
                θ = θ2 x y r + 2 * IZR n * PI.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  assert (2 * PI > 0) as tpigt0. lra.
  specialize (inrange_mT2T2 θ _ tpigt0) as [k [tl th]].
  set (z := θ + IZR k * (2 * PI)) in *.
  assert (θ = z - 2 * IZR k * PI) as tdef; [unfold z; lra |].
  assert (- PI < z <= PI) as [zh zl]; [split; lra|].

  destruct zl as [ltpi | eqpi].
  + assert (- PI < z < PI) as zrng; try lra.
    rewrite (k'_periodic _ _ _ (k)%Z) in ksg0.
    rewrite tdef in ksg0.
    assert (z - 2 * IZR k * PI + 2 * IZR k * PI = z) as zid. lra.
    rewrite zid in ksg0. clear zid.

    destruct (Req_dec (2 * r - y) 0) as [a|na].
    ++ apply (k_deriv_sign_lin2 _ _ _ _ zrng rne0 phase a)
        in ksg0 as [ksg0 xne0].
       apply (Rmult_eq_compat_l 2) in ksg0.
       assert (2 * (z / 2) = z) as id;
         [field| rewrite id in ksg0; clear id].
       rewrite tdef.
       rewrite ksg0.
       unfold θ1, θ2.
       kpt1t2h1 k.
      
    ++ apply (k_deriv_sign_quad2 _ _ _ _ zrng rne0 phase na)
        in ksg0 as [ksg0 |ksg0];
       apply (Rmult_eq_compat_l 2) in ksg0;
       assert (2 * (z / 2) = z) as id;
       [field| rewrite id in ksg0; clear id|
        field| rewrite id in ksg0; clear id ];
       rewrite tdef;
       rewrite ksg0;
       unfold θ1, θ2.

       kpt1t2h1 k.
       kpt1t2h1 k.

  + rewrite (k'_periodic _ _ _ k) in ksg0.
    rewrite (Rmult_comm 2) in ksg0.
    rewrite Rmult_assoc in ksg0.
    change (sign (κ' x y r z) = 0) in ksg0.
    rewrite eqpi in ksg0.
    
    rewrite k_deriv_sign_PI in ksg0; try assumption.
    rewrite signeq0_eqv in ksg0.
    apply straightcond in phase.
    assert (y = 2 * r) as yeq2r. {
      apply (Rplus_eq_reg_r (-y)).
      apply (Rmult_eq_reg_r (r)); try assumption.
      symmetry.
      lrag ksg0. }
    clear ksg0.
    rewrite tdef.
    rewrite eqpi.
    clear eqpi tdef.

    assert (x <> 0) as xne0. {
      intro xeq0.
      rewrite xeq0, yeq2r in phase.
      autorewrite with null in phase.
      change ((2 * r)² < (2 * r)²) in phase.
      lra. }
    clear phase.

    unfold θ1, θ2.

    kpt1t2h1 k.
Qed.
