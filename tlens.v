(* begin hide *)
Require Import Reals.
Require Import Ranalysis5.
Require Import FunctionalExtensionality.
Require Import Coquelicot.Coquelicot.
Require Import Omega.
Require Import Lia.
Require Import Lra.
Require Import atan2.
Require Import ttyp.
Require Import tdyn.
Require Import util.
Require Import strt.
Require Import strt2.
Require Import incr_function_le_ep.

Import Lra.
Open Scope R_scope.
Set Bullet Behavior "Strict Subproofs".

Ltac comp :=
  match goal with
  | ateq0 : atan ?A = 0, a3gt0 : 0 < ?A |- False => 
    apply atan_increasing in a3gt0;
    rewrite atan_0 in a3gt0;
    rewrite ateq0 in a3gt0;
    lra
  | ateq0 : atan ?A = 0, a3gt0 : ?A < 0|- False => 
    apply atan_increasing in a3gt0;
    rewrite atan_0 in a3gt0;
    rewrite ateq0 in a3gt0;
    lra
  | tceq0 : 2 * atan ((?x₁ - sqrt (?x₁² - (2 * ?r - ?y₁) * ?y₁))
                        / (2 * ?r - ?y₁)) + 2 * 1 * PI = 0 |- False => 
           specialize (atan_bound ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                     / (2 * r - y₁))) as [atl atu];
           set (A := atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                             / (2 * r - y₁))) in *;
           lra
  | tceq0 : 2 * atan ((?x₁ - sqrt (?x₁² - (2 * ?r - ?y₁) * ?y₁))
                        / (2 * ?r - ?y₁)) - 2 * 1 * PI = 0 |- False => 
           specialize (atan_bound ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                                     / (2 * r - y₁))) as [atl atu];
           set (A := atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                             / (2 * r - y₁))) in *;
           lra
  end.

Ltac setA :=
  let A := fresh "A" in
  match goal with
  | |- exists q : Z, atan2 (?y - ?r * (1 - cos (2 * ?a))) (?x - ?r * sin (2 * ?a)) =
                     (2 * ?a) + 2 * IZR q * PI =>
    set (A := a);
    unfold atan2;
    destruct (pre_atan2 (y - r * (1 - cos (2*A)))
                        (x - r * sin (2*A))) as
        [θ [[tlb tub] [xd yd]]];
    set (M := sqrt ((y - r * (1 - cos (2 * A)))² + (x - r * sin (2 * A))²)) in *
  end.

(* start of general library *)
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

Lemma Rinv_eqv : forall n,
    n/2 = n * / 2.
Proof.
  intros. field.
Qed.

Lemma Rinv_neqv : forall n,
    -n/2 = - n * / 2.
Proof.
  intros. field.
Qed.

Lemma Rinv_ideqv : forall n,
    n/2*2 = n.
Proof.
  intros. field.
Qed.

Lemma Rabs_arg_neg : forall x,
    Rabs x = - x -> x <= 0.
Proof.
  intros.
  unfold Rabs in H.
  destruct (Rcase_abs x);
    [left; assumption|right; lra].
Qed.

Lemma atan2_atan_Q1Q4 : forall dx dy : R,
    0 < dx -> atan2 dy dx = atan (dy / dx).
Proof.
  intros.
  destruct (total_order_T dy 0).
  destruct s.
  + apply atan2_atan_Q4; try assumption.
  + rewrite e.
    rewrite atan2_0; try assumption.
    fieldrewrite (0 / dx) 0. lra.
    rewrite atan_0. reflexivity.
  + apply atan2_atan_Q1; try assumption.
Qed.

Lemma nna : forall r t,
    0 < r * t < Rabs r * 2 * PI ->
    0 <= r * t.
Proof.
  intros.
  destruct H.
  left; assumption.
Qed.

(* sum of squares is nonzero when both components are not
simultaneously zero *)
Lemma posss : forall x y (nO : ~ (x = 0 /\ y = 0)),
    0 < x² + y².
Proof.
  intros.
  specialize (Rle_0_sqr x) as mx2ge0.
  specialize (Rle_0_sqr y) as my2ge0.
  destruct mx2ge0 as [mx2lt0 | mx2eq0];
    destruct my2ge0 as [my2lt0 | my2eq0].
  apply Rplus_lt_0_compat; assumption.
  rewrite <- my2eq0.
  arn; assumption.
  rewrite <- mx2eq0.
  arn; assumption.
  exfalso; apply nO.
  symmetry in mx2eq0, my2eq0.
  apply Rsqr_eq_0 in mx2eq0.
  apply Rsqr_eq_0 in my2eq0.
  split; assumption.
Qed.

Lemma require_turn : forall x y,
    atan2 y x <> 0 ->
    ~ (0 < x /\ y = 0).
Proof.
  intros *. intro at2ne0.
  intros [zltx yeq0].
  apply at2ne0.
  rewrite yeq0.
  rewrite atan2_0; [reflexivity | assumption].
Qed.

Lemma path_cos_id : forall θ₀ r,
    r <> 0 ->
    0 = r * (cos θ₀ + - cos (Rabs r * PI / r + θ₀)) ->
    0 = cos θ₀.
Proof.
  intros *. intro rnez.
  destruct (Rle_dec 0 r).
  inversion_clear r0; [|exfalso; subst ;auto].
  rewrite Rabs_pos_eq; [|left; auto].
  fieldrewrite (r * PI / r + θ₀) (θ₀ + PI). auto.
  rewrite neg_cos.
  fieldrewrite (r * (cos θ₀ + - - cos θ₀)) ((2 * r) * cos θ₀).
  assert (0 = 2 * r*0) as zeqr0. field. rewrite zeqr0 at 1. clear zeqr0.
  intros yeq.
  apply Rmult_eq_reg_l in yeq; auto.

  apply Rnot_le_lt in n.
  rewrite Rabs_left; [| assumption].
  fieldrewrite (-r * PI / r + θ₀) (- (- θ₀ + PI)). auto.
  rewrite cos_neg, neg_cos, cos_neg.
  fieldrewrite (r * (cos θ₀ + - - cos θ₀)) ((2 * r) * cos θ₀).
  assert (0 = 2 * r*0) as zeqr0. field. rewrite zeqr0 at 1. clear zeqr0.
  intros yeq.
  apply Rmult_eq_reg_l in yeq; auto.
Qed.

Lemma path_sin_id : forall θ₀ r,
    r <> 0 ->
    0 = r * (- sin θ₀ + sin (Rabs r * PI / r + θ₀)) ->
    0 = sin θ₀.
Proof.
  intros *. intro rnez.
  destruct (Rle_dec 0 r).
  inversion_clear r0; [|exfalso; subst ;auto].
  rewrite Rabs_pos_eq; [|left; auto].
  fieldrewrite (r * PI / r + θ₀) (θ₀ + PI). auto.
  rewrite neg_sin.
  fieldrewrite (r * (- sin θ₀ + - sin θ₀)) ((- 2 * r) * sin θ₀).
  assert (0 = - 2 * r*0) as zeqr0. field. rewrite zeqr0 at 1. clear zeqr0.
  intros yeq.
  apply Rmult_eq_reg_l in yeq;
    [| apply Rmult_integral_contrapositive_currified; [discrR | auto]].
  assumption.

  apply Rnot_le_lt in n.
  rewrite Rabs_left; [| assumption].
  fieldrewrite (-r * PI / r + θ₀) (- (- θ₀ + PI)). auto.
  rewrite sin_neg, neg_sin, sin_neg.
  fieldrewrite (r * (-sin  θ₀ + - - - sin θ₀)) ((- 2 * r) * sin θ₀).
  assert (0 = - 2 * r*0) as zeqr0. field. rewrite zeqr0 at 1. clear zeqr0.
  intros yeq.
  apply Rmult_eq_reg_l in yeq; [assumption | intro; lra].
Qed.

Lemma rot1_rot2 : forall dx dy X Y θ₀,
  (dy - (X * sin θ₀ + Y * cos θ₀))² + (dx - (X * cos θ₀ - Y * sin θ₀))² =
  (- dx * sin θ₀ + dy * cos θ₀ - Y)² + (dx * cos θ₀ + dy * sin θ₀ - X)².
Proof.
  intros.
  setl (dx² + dy²
        + X² * ((sin θ₀)² + (cos θ₀)²)
        + Y² * ((sin θ₀)² + (cos θ₀)²)
          - 2 * dy * X * (sin θ₀) - 2 * dy * Y * (cos θ₀)
          - 2 * dx * X * (cos θ₀) + 2 * dx * Y * (sin θ₀)).

  setr (dx² * ((sin θ₀)²+ (cos θ₀)²)
        + dy² * ((sin θ₀)² + (cos θ₀)²)
        + X² + Y²
        + 2 * Y * dx * (sin θ₀) - 2 * Y * dy * (cos θ₀)
          - 2 * X * dx * (cos θ₀) - 2 * X * dy * (sin θ₀)
       ).
  rewrite sin2_cos2.
  field.
Qed.

Lemma rxlate : forall x₀ y₀ θ₀ x₁ y₁ θc,
  ((x₁ - x₀) * sin (θ₀ + θc) - (y₁ - y₀) * cos (θ₀ + θc)) / (1 - cos θc) 
  = (((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) * sin θc -
     (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) * cos θc)
      / (1 - cos θc).
Proof.
  intros.
  rewrite sin_plus, cos_plus, Rmult_plus_distr_l, Rmult_minus_distr_l.
  fieldrewrite ((x₁ - x₀) * (sin θ₀ * cos θc) + (x₁ - x₀) * (cos θ₀ * sin θc)
                - ((y₁ - y₀) * (cos θ₀ * cos θc) - (y₁ - y₀) * (sin θ₀ * sin θc)))
               (((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ ) * sin θc
                - ((- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) * cos θc)).
  reflexivity.
Qed.

Lemma atan2_rot1_rot2 : forall x y X Y θ φ
    (nO : ~ (x * cos θ + y * sin θ - X = 0 /\ - x * sin θ + y * cos θ - Y = 0)),
    (exists q:Z,
        atan2 (- x * sin θ + y * cos θ - Y)
              (x * cos θ + y * sin θ - X) = φ + 2 * IZR q * PI)
        ->
        exists k : Z,
          atan2 (y - (X * sin θ + Y * cos θ))
                (x - (X * cos θ - Y * sin θ)) = θ + φ + 2 * IZR k * PI.
Proof.
  intros *. intro.
  intros [q at2].
  apply (atan2_rotation _ _ θ) in at2; try assumption.
  destruct at2 as [n sw].
  assert (((x * cos θ + y * sin θ - X) * sin θ +
           (- x * sin θ + y * cos θ - Y) * cos θ) =
          (y * ((sin θ)² + (cos θ)²) -
           (X * sin θ + Y * cos θ))) as id;
    [unfold Rsqr; field| rewrite id in sw; clear id].
  
  assert ((x * cos θ + y * sin θ - X) * cos θ -
           (- x * sin θ + y * cos θ - Y) * sin θ =
          x * ((sin θ)² + (cos θ)²) -
          (X * cos θ - Y * sin θ)) as id;
    [unfold Rsqr; field| rewrite id in sw; clear id].
  rewrite sin2_cos2, Rmult_1_r, Rmult_1_r in sw.
  exists (q + n)%Z.
  rewrite sw, plus_IZR.
  lra.
Qed.

Lemma notid_rot :
  forall θ₀ x₀ y₀ x₁ y₁ (nO : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0)),
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    ~ (x = 0 /\ y = 0).
Proof.
  intros.
  intros [xeq0 yeq0].
    unfold x in xeq0.
    unfold y in yeq0.
    set (dx := x₁ - x₀) in *.
    set (dy := y₁ - y₀) in *.
    destruct (Req_dec (cos θ₀) 0).
    + rewrite H in *.
      apply coseq0_sinneq0 in H.
      autorewrite with null in *.
      rewrite <- (Rmult_0_l (sin θ₀)) in yeq0.
      apply Rmult_eq_reg_r in yeq0; try assumption.
      apply Ropp_eq_0_compat in yeq0.
      rewrite Ropp_involutive in yeq0.
      rewrite <- (Rmult_0_l (sin θ₀)) in xeq0.
      apply Rmult_eq_reg_r in xeq0; try assumption.
      apply nO.
      split; assumption.
    + assert (dx = 0) as dxeq0. {
        rewrite <- (Rmult_1_r dx), <- (sin2_cos2 θ₀), Rplus_comm.
        rewrite Rmult_plus_distr_l.
        apply (Rmult_eq_reg_r (/ cos θ₀)).
        rewrite Rmult_plus_distr_r.
        arn.
        setl (dx * cos θ₀ + (dx * sin θ₀ / cos θ₀) * sin θ₀).
        assumption.
        assert (dy = dx * sin θ₀ / cos θ₀) as dyd. {
          apply (Rmult_eq_reg_r (cos θ₀)); try assumption.
          apply Rminus_diag_uniq.
          rewrite <- pm, Rplus_comm.
          lrag yeq0. }
        rewrite <- dyd.
        assumption.
        zltab. }
      rewrite dxeq0 in *.
      autorewrite with null in *.
      rewrite <- (Rmult_0_l (cos θ₀)) in yeq0.
      apply Rmult_eq_reg_r in yeq0; try assumption.
      apply nO.
      split; auto.
Qed.

Lemma x_minus_sin_x_pos :
  forall x (xgt0 : 0 < x),
    0 < x - sin x.
Proof.
  assert (derivable (fun x => x - sin x)) as Q1.
  { unfold derivable; intros.
    auto_derive; auto. }
  assert (forall (n : Z), (2 * (IZR n) * PI < 2 * (IZR (n + 1) * PI))) as Q2.
  { intros; rewrite Rmult_assoc.
    apply Rmult_lt_compat_l; [lra|].
    apply Rmult_lt_compat_r; [apply PI_RGT_0|].
    apply IZR_lt; lia.
  }
  assert (forall (n : Z) (y : R), 2 * (IZR n) * PI < y < 2 * (IZR (n + 1) * PI)
                                  -> 0 < derive_pt (fun x => x - sin x) y (Q1 y)) as Q3.
  { intros.
    rewrite Derive_Reals.
    assert (Derive (fun x : R => x - sin x) y = 1 - cos y) as P1.
    { apply is_derive_unique.
      auto_derive; auto; lra. }
    rewrite P1.
    destruct (COS_bound y) as [cub clb].
    clear cub.
    destruct (Rle_lt_or_eq_dec _ _ clb); try lra.
    assert (0 < y + 2 * IZR (-n) * PI) as P3.
    { rewrite Ropp_Ropp_IZR; lra. }
    assert (y + 2 * IZR (-n) * PI < 2 * PI) as P4.
    { rewrite plus_IZR in H; rewrite Ropp_Ropp_IZR ; lra. }
    rewrite <- (cos_period1 y (- n)) in e.
    apply (cos_eq_1_2PI_0 (y + 2 * IZR (-n) * PI)) in e; lra.
  }
  assert (forall (n : Z) (x y : R), (2 * (IZR n) * PI <= x <= 2 * (IZR (n + 1) * PI)
                                     -> 2 * (IZR n) * PI <= y <= 2 * (IZR (n + 1) * PI)
                                     -> x < y
                                     -> (fun z => z - sin z) x < (fun z => z - sin z) y)) as Q4.
  intro n.
  eapply derive_increasing_interv; eauto.
  intros.
  assert (exists (k : Z), 2 * IZR k * PI <= x <= 2 * (IZR (k + 1) * PI)) as Q5.
  { destruct (inrange_0T x _ Rgt_2PI_0) as [k [LBND UBND]].
    exists (-k)%Z; split; [| rewrite plus_IZR]; rewrite Ropp_Ropp_IZR; lra.
  }
  destruct Q5 as [k BND].
  assert (2 * IZR k * PI <= 2 * IZR k * PI <= 2 * (IZR (k + 1) * PI)) as Q6.
  { lra. }
  specialize BND as BND'.
  destruct BND' as [LBND' UBND'].
  assert (0 <= k)%Z as Q5.
  { assert (2 * (IZR 0) * PI < x) as P1.
    { lra. }
    eapply Rlt_le_trans in UBND'; eauto.
    rewrite Rmult_assoc in UBND'.
    apply Rmult_lt_reg_l in UBND'; [|lra].
    apply Rmult_lt_reg_r in UBND'; [|apply PI_RGT_0].
    apply lt_IZR in UBND'; lia.
  }
  destruct (Rle_lt_or_eq_dec _ _ LBND') as [LTB | LEB]; clear LBND' UBND'.
  + specialize (Q4 _ _ _ Q6 BND LTB); simpl in Q4.
    rewrite <- (Rplus_0_l (2 * IZR k * PI)), sin_period1,
    sin_0, Rplus_0_l, Rminus_0_r in Q4.
    apply IZR_le in Q5.
    assert (2 * 0 * PI <= 2 * (IZR k) * PI) as Q7.
    { repeat rewrite Rmult_assoc. apply Rmult_le_compat_l; [lra|].
      apply Rmult_le_compat_r;[specialize PI_RGT_0; lra | assumption].
    }
    apply Rle_lt_trans with (r2 := 2 * IZR k * PI); lra.
  + rewrite <- Rplus_0_l in LEB at 1.
    rewrite <- LEB at 2; rewrite sin_period1, sin_0; lra.
Qed.

Lemma r_std_deriv :
  forall x y z,
    cos z <> 1 -> 
    is_derive (fun θ:R => (x * sin θ - y * cos θ)
                            / (1 - cos θ))
              z ((x * cos z +  y * sin z) / (1 + - cos z) -
                 (x * sin z - y * cos z) * sin z / (1 - cos z)²).
Proof.
  intros.
  auto_derive.
  lra.
  setl ((x * cos z + y * sin z) / (1 + - cos z) -
        (x * sin z - y * cos z) * sin z / (1 - cos z)²).
  lra.
  reflexivity.
Qed.

Lemma r_std_deriv_sign :
  forall x y z,
    cos z <> 1 ->
    sign (Derive (fun θ => (x * sin θ - y * cos θ)
                             / (1 - cos θ)) z)
    = sign (x * (cos z - 1) + y * sin z).
Proof.
  intros.
  assert (0 < 1 - cos z) as oczp. {
    apply (Rplus_lt_reg_r (cos z)).
    setr 1.
    arn.
    specialize (COS_bound z) as [l h].
    destruct h.
    assumption.
    exfalso. lra. }

  assert (0 < (1 - cos z)²) as oczp2. {
    unfold Rsqr. zltab. }
  
  specialize (r_std_deriv x y z H) as drs.
  apply is_derive_unique in drs.
  rewrite drs. clear drs.
  unfold sign.
  destruct total_order_T;
    destruct total_order_T;
    try reflexivity; try destruct s;
      try (destruct s0; try reflexivity);
      exfalso.

  + assert (0 = (x * cos z + y * sin z) / (1 + - cos z) -
              (x * sin z - y * cos z) * sin z / (1 - cos z)²)
      as id. {
      apply (Rmult_eq_reg_r ((1 - cos z)²)).
      arn.
      setr ((x * cos z - x * ((sin z)²+(cos z)²) + y * sin z)).
      lra.
      rewrite sin2_cos2.
      rewrite e.
      field.
      lra. }
    lra.
    
  + assert (0 = x * (cos z - 1) + y * sin z)
      as id. {
      rewrite <- (sin2_cos2 z).
      apply (Rmult_eq_reg_r (/ (1 - cos z)²)).
      lrag e.
      zltab. }
    lra.
    
  + assert (0 > (x * cos z + y * sin z) / (1 + - cos z) -
              (x * sin z - y * cos z) * sin z / (1 - cos z)²)
    as id. {
      apply (Rmult_lt_reg_r ((1 - cos z)²)).
      lra.
      arn.
      apply Rgt_lt in r.
      setl ((x * cos z - x * ((sin z)²+(cos z)²) + y * sin z)).
      lra.
      rewrite sin2_cos2.
      lrag r.  }
    lra.
    
  + assert (0 = x * (cos z - 1) + y * sin z)
      as id. {
      rewrite <- (sin2_cos2 z).
      apply (Rmult_eq_reg_r (/ (1 - cos z)²)).
      lrag e.
      zltab. }
    lra.
    
  + assert (0 > x * (cos z - 1) + y * sin z)
      as id. {
      rewrite <- (sin2_cos2 z).
      apply Rlt_gt.
      apply (Rmult_lt_reg_r (/ (1 - cos z)²)).
      zltab.
      apply Rgt_lt.
      setl 0.
      lra.
      setr ((x * cos z + y * sin z) / (1 + - cos z) -
            (x * sin z - y * cos z) * sin z / (1 - cos z)²).
      lra.
      assumption. }
    lra.
    
  + assert (0 = (x * cos z + y * sin z) / (1 + - cos z) -
                (x * sin z - y * cos z) * sin z / (1 - cos z)²)
      as id. {
      apply (Rmult_eq_reg_r ((1 - cos z)²)).
      arn.
      setr ((x * cos z - x * ((sin z)²+(cos z)²) + y * sin z)).
      lra.
      rewrite sin2_cos2.
      rewrite e.
    field.
    lra. }
    lra.
Qed.

Lemma r_std_2deriv :
  forall x y z,
    cos z <> 1 -> 
    is_derive (fun θ:R => (x * cos θ +  y * sin z) / (1 - cos θ) -
                          (x * sin θ - y * cos z) * sin z / (1 - cos θ)²) z
              (- x * sin z * / (1 - cos z)
               - 2 * x * cos z * sin z * / (1 - cos z)²
               - y * sin z * sin z * / (1 - cos z)²
               + 2 * x * sin z * (sin z)² * / (1 - cos z) * / (1 - cos z)²
                 - 2 * y * cos z * (sin z)² * / (1 - cos z) * / (1 - cos z)²).
Proof.
  intros.

  assert (0 < 1 - cos z) as oczp. {
    apply (Rplus_lt_reg_r (cos z)).
    setr 1.
    arn.
    specialize (COS_bound z) as [l h].
    destruct h.
    assumption.
    exfalso. lra. }

  assert (0 < (1 - cos z)²) as oczp2. {
    unfold Rsqr. zltab. }

  auto_derive.
  split; try lra.
  rewrite pm.
  split.
  intro.
  lra.
  constructor.


  setl (- x * sin z * / (1 - cos z)
        - 2 * x * cos z* sin z * / (1 - cos z)²
        - y * sin z * sin z * / (1 - cos z)² 
        + 2 * x * sin z* (sin z)² * / (1 - cos z) * / (1 - cos z)²
          - 2 * y * cos z* (sin z)² * /(1 - cos z) * / (1 - cos z)²) ;
    [lra|reflexivity].
Qed.

Lemma th2_num_sign: forall x y,
    0 < y ->
    0 < x + sqrt(x² + y).
Proof.
  intros.
  assert (Rabs x < sqrt (Rsqr x + y)) as P. {
    rewrite <- sqrt_Rsqr_abs.
    apply sqrt_lt_1_alt.
    split; [apply Rle_0_sqr|].
    rewrite <- (Rplus_0_l (Rsqr x)), <- Rlt_minus_r.
    fieldrewrite (0 + x² + y - x²) (y); auto. }
  assert (- Rabs x <= Rabs x) as P0. {
    specialize (Rabs_pos x) as P0.
    - apply (Rle_trans _ 0 _); auto.
      destruct P0;[left|right]; try lra. }
  rewrite <- (Rplus_opp_r x).
  apply Rplus_lt_compat_l.
  destruct (Rle_lt_dec 0 x) as [NNeg | P1].
  - rewrite Rabs_pos_eq in *; auto.
    apply (Rle_lt_trans _ x _); auto.
  - rewrite Rabs_left in *; auto.
Qed.

Lemma thmaxnePIimpl : forall x y,
    calcθ₁ 0 0 0 x y <> 2 * PI -> ~ (x < 0 /\ y = 0).
Proof.
  intros.
  intros [xle0 yeq0].
  apply H.
  unfold calcθ₁.
  arn.
  apply (Rmult_eq_reg_r (/ 2)); try lra.
  setl (atan2 y x).
  setr (PI).
  rewrite yeq0.
  apply atan2_PI.
  assumption.
Qed.


Lemma thmaxne0impl : forall x y,
    calcθ₁ 0 0 0 x y <> 0 -> ~ (0 < x /\ y = 0).
Proof.
  intros.
  intros [xle0 yeq0].
  apply H.
  unfold calcθ₁.
  arn.
  apply (Rmult_eq_reg_r (/ 2)); try lra.
  setl (atan2 y x).
  setr (0).
  rewrite yeq0.
  apply atan2_0.
  assumption.
Qed.

(* end of general library *)

Lemma tcrng_form2 : forall (x₀ y₀ x₁ y₁ θ₀ θc : R),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tcrng : (θmax/2 < θc < θmax \/
                     - 2*PI < θc < θmax/2 - 2*PI \/
                     θmax < θc < θmax/2 \/
                     θmax/2 + 2*PI < θc < 2*PI)),
      (0 < θmax -> (θmax/2 < θc < θmax \/
                    - 2*PI < θc < θmax/2 - 2*PI)) /\
      (θmax < 0 -> (θmax < θc < θmax/2 \/
                    θmax/2 + 2*PI < θc < 2*PI)) /\ (θmax <> 0).
Proof.
  intros.
  destruct tcrng as [[pll plh] | [[nll nlh] |
                                  [[nrl nrh] |[prl prh]]]].
  destruct (total_order_T 0 θmax);
    [destruct s|] ; lra.
  destruct (total_order_T 0 θmax);
    [destruct s|] ; lra.
  destruct (total_order_T 0 θmax);
    [destruct s|] ; lra.
  destruct (total_order_T 0 θmax);
    [destruct s|] ; lra.
Qed.

Lemma turn_eqv : forall (x₀ y₀ x₁ y₁ θ₀ θc : R),
    let x := (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ in
    let y := - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (ctmne1 : cos θmax <> 1),
      θmax <> 0 /\ θmax <> 2 * PI.
Proof.
  intros.
  unfold θmax,calcθ₁ in *. clear θmax.
  change (cos (2 * atan2 y x) <> 1) in ctmne1.
  change (2 * atan2 y x <> 0 /\ 2 * atan2 y x <> 2 * PI).
  split.
  intro at2eq0.
  apply ctmne1. clear ctmne1.
  rewrite at2eq0 in *.
  apply cos_0.
  intro at2eq0.
  apply ctmne1. clear ctmne1.
  rewrite at2eq0 in *.
  apply cos_2PI.
Qed.

(* Given a ottb path segment constructed using Hx and Hy of length D
from (x0,y0) to (x1,y1), if D is less than a certain amount, we are
still turning. *)
Lemma ottb_distance_turning : forall (D:nonnegreal) (x₀ y₀ x₁ y₁ r θ₀ θc:R)
    rtp
    (P : path_segment D (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp)
                      (mkpt x₀ y₀) (mkpt x₁ y₁)),
    0 <= D <= r*θc ->
    turning r θ₀ x₀ y₀ x₁ y₁.
Proof.
  intros until 1. intros Dthorder.
  assert (0 <= r * θc < 2 * Rabs r * PI) as zlerthcle2rPI.
  { lra. }

  unfold turning.
  inversion zlerthcle2rPI as [zlerthc thclt2rPI].
  inversion Dthorder as [zleD Dlerthc].
  inversion_clear P.
  injection bbnd. intros Hxdef Hydef.
  clear bbnd.
  rewrite <- Hxdef, <- Hydef.
  unfold Hx,Hy,Tcx,Tcy, extension_cont.
  destruct (Rle_dec (nonneg D) (r * θc)).
  + unfold Hxarc, Hyarc.

    unfold Rsqr.
  
    fieldrewrite
      ((r * sin (nonneg D / r + θ₀) - r * sin θ₀ + x₀ - (x₀ + r * cos (PI / 2 + θ₀))) *
       (r * sin (nonneg D / r + θ₀) - r * sin θ₀ + x₀ - (x₀ + r * cos (PI / 2 + θ₀))) +
       (- r * cos (nonneg D / r + θ₀) + r * cos θ₀ + y₀ - (y₀ + r * sin (PI / 2 + θ₀))) *
       (- r * cos (nonneg D / r + θ₀) + r * cos θ₀ + y₀ - (y₀ + r * sin (PI / 2 + θ₀))))
               
      (r*r * (
         (sin (nonneg D / r + θ₀) - sin θ₀ + - cos (PI / 2 + θ₀)) *
         (sin (nonneg D / r + θ₀) - sin θ₀ + - cos (PI / 2 + θ₀)) +
         (- cos (nonneg D / r + θ₀) + cos θ₀ - sin (PI / 2 + θ₀)) *
         (- cos (nonneg D / r + θ₀) + cos θ₀ - sin (PI / 2 + θ₀)))).

    rewrite <- cos_sin.
    rewrite <- sin_cos.
    fieldrewrite
      ((sin (nonneg D / r + θ₀) - sin θ₀ + sin θ₀) *
       (sin (nonneg D / r + θ₀) - sin θ₀ + sin θ₀) +
       (- cos (nonneg D / r + θ₀) + cos θ₀ - cos θ₀) *
       (- cos (nonneg D / r + θ₀) + cos θ₀ - cos θ₀))
    
      ((sin (nonneg D / r + θ₀)) *
       (sin (nonneg D / r + θ₀)) +
       (- cos (nonneg D / r + θ₀)) *
       (- cos (nonneg D / r + θ₀))).
  
    assert
      ((sin (nonneg D / r + θ₀))² + (cos (nonneg D / r + θ₀))² =
       (sin (nonneg D / r + θ₀) * sin (nonneg D / r + θ₀) +
        - cos (nonneg D / r + θ₀) * - cos (nonneg D / r + θ₀))).
    unfold Rsqr. field. rewrite <- H.
    rewrite sin2_cos2. field.

    + exfalso. apply n. assumption.
Qed.

(* Given a ottb path segment constructed using Hx and Hy of length D
from (x0,y0) to (x1,y1), if we are still turning, D is within certain
bounds. *)
Lemma ottb_turning_distance : forall (D:nonnegreal) (x₀ y₀ x₁ y₁ r θ₀ θc:R)
    rtp
    (P : path_segment D (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp) (mkpt x₀ y₀) (mkpt x₁ y₁)),
    turning r θ₀ x₀ y₀ x₁ y₁ ->
    0 <= D <= r*θc.
Proof.
  intros.

  addzner.
  inversion_clear P.
  unfold turning, Tcx, Tcy in H.
  injection bbnd. intros.
  clear abnd bbnd.
  rewrite <- H0, <- H1 in H.
  clear H0 H1.
  clear pzbydist contx conty.
  unfold Hx, Hy, extension_cont in H.
  destruct (Rle_dec 0 (r * θc));
  [|exfalso; apply Rnot_le_gt in n; lra].
  destruct (Rle_dec (nonneg D) (r * θc)).
  + split. destruct D. simpl in *. assumption. assumption.

  + exfalso.
    unfold Hxlin, Hylin, Hxarc, Hyarc in H.
    rewrite <- cos_sin in H.
    assert (r * θc / r + θ₀ = θc + θ₀). field.
    intro; subst; apply zner; reflexivity.
    rewrite H0 in H. clear H0.
    assert (r * cos (PI / 2 + θ₀) = - r * (sin (θ₀))).
    rewrite (sin_cos θ₀).
    field.
    rewrite H0 in H. clear H0.
    assert (((nonneg D - r * θc) * cos (θ₀ + θc) + (r * sin (θc + θ₀) - r * sin θ₀ + x₀) -
                                                   (x₀ + - r * sin θ₀))² +
            ((nonneg D - r * θc) * sin (θ₀ + θc) + (- r * cos (θc + θ₀) + r * cos θ₀ + y₀) -
                                                   (y₀ + r * cos θ₀))² =
            (nonneg D - r * θc)² * ((sin (θ₀ + θc))² + (cos (θ₀ + θc))²)
            + r² * ((sin (θc + θ₀))² + (cos (θc + θ₀))²)
            + 2*r*(nonneg D - r * θc) *
              ( sin (θc + θ₀) *cos (θ₀ + θc) - 
                cos (θc + θ₀)* sin (θ₀ + θc)));
      [unfold Rsqr; field|].
    rewrite H0 in H. clear H0.
    repeat rewrite sin2_cos2 in H.
    rewrite <- sin_minus in H.
    assert ((θc + θ₀ - (θ₀ + θc)) = 0). field. rewrite H0 in H. clear H0.
    rewrite sin_0 in H.
    apply (Rplus_eq_compat_l (-(r²))) in H.
    assert (- r² + ((nonneg D - r * θc)² * 1 + r² * 1 + 2 * r * (nonneg D - r * θc) * 0) =
            (nonneg D - r * θc)²). field. rewrite H0 in H. clear H0.
    assert (- r² + r² = 0). field. rewrite H0 in H. clear H0.
    apply n.
    apply (Rplus_le_reg_l (- r * θc)).
    setr 0. setl (nonneg D - r * θc).
    rewrite <- Rsqr_0 in H.
    apply Rsqr_inj in H.
    rewrite <- H. right. reflexivity.
    right. reflexivity.
    apply Rnot_le_gt in n.
    left. lra.
Qed.

Lemma ottb_turning_le180 :
  forall (D:nonnegreal) (x₀ y₀ x₁ y₁ r θ₀ θc:R) rtp
         (zlerthcle2rPI : 0 <= r * θc < 2 * Rabs r * PI)
         (P : path_segment D (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    0 <= D <= r*θc ->
    0 < D < Rabs r * PI ->
    0 < (x₁ - x₀)*cos(θ₀) + (y₁ - y₀)*sin(θ₀).
Proof.
  intros.
  
  addzner.
  inversion P.
  injection bbnd. intros Hydef Hxdef.
  rewrite <- Hydef, <- Hxdef.
  clear pzbydist bbnd abnd contx conty Hxdef Hydef.
  unfold Hx, Hy, extension_cont.
  destruct (Rle_dec(nonneg D) (r * θc)).
  unfold Hxarc, Hyarc.
  fieldrewrite
    ((r * sin (nonneg D / r + θ₀) - r * sin θ₀ + x₀ - x₀) * cos θ₀ +
     (- r * cos (nonneg D / r + θ₀) + r * cos θ₀ + y₀ - y₀) * sin θ₀)
    (r * (sin (nonneg D / r + θ₀)* cos θ₀
          - cos (nonneg D / r + θ₀) * sin θ₀)).
  rewrite <- sin_minus.
  destruct (Rle_dec 0 r).
  inversion_clear r1.
  apply Rmult_lt_0_compat. assumption.
  apply sin_gt_0.
  fieldrewrite (nonneg D / r + θ₀ - θ₀) (nonneg D / r).
  intro; subst; apply zner; reflexivity.
  apply (Rmult_lt_reg_l r). assumption.
  setl 0. setr (nonneg D).
  auto.
  inversion H0. assumption.
  setl (nonneg D / r).
  auto.
  apply (Rmult_lt_reg_l r). assumption.
  setl (nonneg D).
  auto.
  inversion H0.
  rewrite Rabs_pos_eq in H3.
  assumption.
  left. assumption.

  exfalso.
  subst.
  auto.

  apply Rnot_le_lt in n.

  setl (r * 0). auto. 
  apply Rmult_lt_gt_compat_neg_l. assumption.
  fieldrewrite (nonneg D / r + θ₀ - θ₀) (nonneg D / r). auto.
  apply sin_lt_0_var.

  assert (/ r < 0) as rinvlt0.
  apply Rinv_lt_0_compat; assumption.
  setl (/ r * (- r * PI)). auto.
  setr (/ r * nonneg D). auto.
  apply Rmult_lt_gt_compat_neg_l. assumption.
  inversion_clear H0.
  rewrite Rabs_left in H2. assumption.
  assumption.

  assert (/ r < 0) as rinvlt0.
  apply Rinv_lt_0_compat; assumption.
  setl (/ r * (nonneg D)). auto.
  setr (/ r * 0). auto.
  apply Rmult_lt_gt_compat_neg_l. assumption.
  inversion_clear H0. assumption.

  exfalso. apply n.
  inversion H. assumption.
Qed.

Lemma ottb_turning_gt180 :
  forall (D:nonnegreal) (x₀ y₀ x₁ y₁ r θ₀ θc:R) rtp
         (zlerthcle2rPI : 0 <= r * θc < 2 * Rabs r * PI)
         (P : path_segment D (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    0 <= D <= r*θc ->
    Rabs r * PI < D < 2 * Rabs r * PI ->
    (x₁ - x₀)*cos(θ₀) + (y₁ - y₀)*sin(θ₀) < 0.
Proof.
  intros.

  addzner.
  inversion P.
  injection bbnd. intros Hydef Hxdef.
  rewrite <- Hydef, <- Hxdef.
  clear pzbydist bbnd abnd contx conty Hxdef Hydef.
  unfold Hx, Hy, extension_cont.
  destruct (Rle_dec(nonneg D) (r * θc)).
  unfold Hxarc, Hyarc.
  fieldrewrite ((r * sin (nonneg D / r + θ₀) - r * sin θ₀ + x₀ - x₀) * cos θ₀ +
                (- r * cos (nonneg D / r + θ₀) + r * cos θ₀ + y₀ - y₀) * sin θ₀)
               (r * (sin (nonneg D / r + θ₀)* cos θ₀
                     - cos (nonneg D / r + θ₀) * sin θ₀)).
  rewrite <- sin_minus.
  destruct (Rle_dec 0 r).
  inversion_clear r1.
  setr (r * 0).
  apply (Rmult_lt_compat_l r). assumption.
  fieldrewrite (nonneg D / r + θ₀ - θ₀) (nonneg D / r).
  auto.
  inversion_clear H0.
  rewrite Rabs_pos_eq in H2,H3.
  apply sin_lt_0.
  apply (Rmult_lt_reg_l r). assumption.
  setr (nonneg D). auto. assumption.
  apply (Rmult_lt_reg_l r). assumption.
  setl (nonneg D). auto. setr (2*r*PI). assumption.
  left. assumption. left. assumption.

  exfalso. auto.

  apply Rnot_le_lt in n.
  assert (/ r < 0) as rinvlt0.
  apply Rinv_lt_0_compat; assumption.

  assert (0 < / - r) as zltinvoppr.
  apply Rinv_0_lt_compat.
  apply Ropp_0_gt_lt_contravar. assumption.
  
  setr (r * 0). auto. 
  apply Rmult_lt_gt_compat_neg_l. assumption.
  fieldrewrite (nonneg D / r + θ₀ - θ₀) (- (nonneg D / - r)). auto.

  rewrite sin_antisym.
  apply Ropp_0_gt_lt_contravar.
  apply Rlt_gt.

  apply sin_lt_0.

  setl (/ - r * (- r * PI)). auto.
  setr (/ - r * nonneg D). auto.
  apply Rmult_lt_compat_l. assumption.
  inversion_clear H0. rewrite Rabs_left in H1. assumption.
  assumption.

  setl (/ - r * (nonneg D)). auto.
  setr (/ - r * (2*- r*PI)). auto.
  apply Rmult_lt_compat_l. assumption.
  inversion_clear H0.
  rewrite Rabs_left in H2.
  assumption.
  assumption.

  exfalso. apply n.
  inversion H. assumption.
Qed.

(* Distance traveled implies we are on the straight part of the path. *)
Lemma ottb_distance_straight :
  forall (D:nonnegreal) (x₀ y₀ x₁ y₁ r θ₀ θc:R) rtp
         (P : path_segment D (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    r*θc < D -> 
    straight r θ₀ x₀ y₀ x₁ y₁. 
Proof.
  intros.
  addzner.

  unfold turning.
  inversion_clear P.
  injection bbnd. intros Hydef Hxdef.
  unfold straight, Tcx, Tcy.
  rewrite <- Hxdef, <- Hydef.
  unfold Hx, Hy, extension_cont.
  destruct (Rle_dec (nonneg D) (r * θc)).
  exfalso. lra. clear n.
  unfold Hxlin, Hylin, Hxarc, Hyarc, Tcx, Tcy.

  assert (((nonneg D - r * θc) * cos (θ₀ + θc) + (r * sin (r * θc / r + θ₀) - r * sin θ₀ + x₀) -
                                                 (x₀ + r * cos (PI / 2 + θ₀))) =
          ((nonneg D - r * θc) * cos (θ₀ + θc) + r * sin (r * θc / r + θ₀) - r * sin θ₀ +
                                                   r * - cos (PI / 2 + θ₀))).
  field. rewrite H0. clear H0.
  assert (((nonneg D - r * θc) * sin (θ₀ + θc) + (- r * cos (r * θc / r + θ₀) + r * cos θ₀ + y₀) -
                                                 (y₀ + r * sin (PI / 2 + θ₀))) =
          ((nonneg D - r * θc) * sin (θ₀ + θc) + - r * cos (r * θc / r + θ₀) + r * cos θ₀ -
                                                 r * sin (PI / 2 + θ₀))).
  field. rewrite H0. clear H0.
  assert ((r * θc / r + θ₀) = (θ₀ + θc)). field.
  intro; subst; apply zner; reflexivity.
  rewrite H0. clear H0.
  rewrite <- cos_sin.
  rewrite <- sin_cos.
  assert (((nonneg D - r * θc) * cos (θ₀ + θc) + r * sin (θ₀ + θc) - r * sin θ₀ + r * sin θ₀) =
         ((nonneg D - r * θc) * cos (θ₀ + θc) + r * sin (θ₀ + θc))).
  field. rewrite H0. clear H0.
  assert (((nonneg D - r * θc) * sin (θ₀ + θc) + - r * cos (θ₀ + θc) + r * cos θ₀ - r * cos θ₀) =
          ((nonneg D - r * θc) * sin (θ₀ + θc) + - r * cos (θ₀ + θc))).
  field. rewrite H0. clear H0.
  unfold Rsqr.
  assert (((nonneg D - r * θc) * cos (θ₀ + θc) + r * sin (θ₀ + θc)) *
          ((nonneg D - r * θc) * cos (θ₀ + θc) + r * sin (θ₀ + θc)) +
          ((nonneg D - r * θc) * sin (θ₀ + θc) + - r * cos (θ₀ + θc)) *
          ((nonneg D - r * θc) * sin (θ₀ + θc) + - r * cos (θ₀ + θc)) =
          (((nonneg D - r * θc)² + r²) * ((sin (θ₀ + θc))² + (cos (θ₀ + θc))²))).
  unfold Rsqr.
  field. rewrite H0. clear H0.
  assert (r * r = r²). unfold Rsqr. field. rewrite H0. clear H0.
  rewrite sin2_cos2.
  apply (Rplus_gt_reg_l (- r²)).
  setr 0. setl ((D - r * θc)²).
  apply Rlt_gt.
  setl (0²).
  apply Rsqr_lt_abs_1.
  rewrite Rabs_R0.
  rewrite Rabs_right. lra. left. lra.
Qed.

(* end hide *)

(* begin hide *)

Lemma thms : forall (x₁ y₁ : R),
    (calcθ₁ 0 0 0 x₁ y₁ = 2 * atan2 y₁ x₁).
Proof.
  intros.
  unfold calcθ₁ in *.
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
  rewrite id in *. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
  rewrite id in *. clear id. reflexivity.
Qed.

Lemma tmne0 : forall θ₀ x₀ y₀ x₁ y₁
    (notO : ~ ((x₁-x₀) = 0 /\ (y₁-y₀) = 0)),
  let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
  θmax <> 0 -> 
  ~ exists n, atan2 (y₁-y₀) (x₁-x₀) = θ₀ + 2 * IZR n * PI.
Proof.
  intros *.
  intro notO. intro.
  intro tmne0.
  intros [n spc].
  apply tmne0.
  unfold atan2 in spc.
  destruct (pre_atan2 (y₁ - y₀) (x₁ - x₀)) as [x [xrng [yd xd]]].
  subst.
  rewrite sin_period1 in yd.
  rewrite cos_period1 in xd.
  set (L := sqrt ((y₁ - y₀)² + (x₁ - x₀)²)) in *.
  unfold θmax, calcθ₁.
  apply (Rmult_eq_reg_r (/2)); [|apply Rinv_neq_0_compat; discrR].
  setr 0.
  setl (atan2 (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)
              ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)).

  fieldrewrite (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)
               ((x₁ - x₀) * - sin θ₀ + (y₁ - y₀) * cos θ₀).
  fieldrewrite ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
               ((x₁ - x₀) * cos θ₀ - (y₁ - y₀) * - sin θ₀).
  rewrite <- sin_neg, <- cos_neg.
  setr (θ₀ + (- θ₀) + 2 * IZR 0 * PI).
  unfold atan2.
  destruct (pre_atan2 ((x₁ - x₀) * sin (- θ₀) + (y₁ - y₀) * cos (- θ₀))
                      ((x₁ - x₀) * cos (- θ₀) - (y₁ - y₀) * sin (- θ₀)))
    as [b [brng [xd2 yd2]]].
  set (L' := sqrt
               (((x₁ - x₀) * sin (- θ₀) + (y₁ - y₀) * cos (- θ₀))² +
                ((x₁ - x₀) * cos (- θ₀) - (y₁ - y₀) * sin (- θ₀))²)) in *.
  assert (L = L') as leq. {
    unfold L, L'.
    rewrite sin_neg, cos_neg.
    fieldrewrite (((x₁ - x₀) * - sin θ₀ + (y₁ - y₀) * cos θ₀)² +
                  ((x₁ - x₀) * cos θ₀ - (y₁ - y₀) * - sin θ₀)²)
                 ((x₁ - x₀)² * ((sin θ₀)²+(cos θ₀)²)
                  + (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²)).
    rewrite sin2_cos2.
    apply f_equal. field.
  }
  rewrite <- leq in *.
  rewrite xd, yd in xd2.
  rewrite xd, yd in yd2.
  rewrite sin_neg, cos_neg in xd2, yd2.
  setr 0.

  assert (cos b = 1) as cbeq1. {
    symmetry.
    apply (Rmult_eq_reg_l L).
    rewrite <- (sin2_cos2 θ₀).
    fieldrewrite (L * ((sin θ₀)² + (cos θ₀)²))
                 (L * cos θ₀ * cos θ₀ - L * sin θ₀ * - sin θ₀).
    assumption.
    intro Leq0. unfold L in Leq0.
    rewrite <- sqrt_0 in Leq0.
    specialize (Rle_0_sqr (y₁ - y₀)) as zleyd.
    specialize (Rle_0_sqr (x₁ - x₀)) as zlexd.
    apply sqrt_inj in Leq0;
      [|apply Rplus_le_le_0_compat; assumption|right; reflexivity].

    destruct zleyd as [zltyd| zeqyd].
    specialize (Rplus_lt_le_0_compat _ _ zltyd zlexd) as zlts.
    clear - Leq0 zlts. lra.
    destruct zlexd as [zltxd| zeqxd]. lra.
    symmetry in zeqyd, zeqxd.
    apply Rsqr_eq_0 in zeqyd.
    apply Rsqr_eq_0 in zeqxd.
    apply notO.
    split; assumption.
  }
  destruct brng as [blb bub].
  destruct (Rle_dec 0 b).
  assert (b < 2*PI). lra.
  apply cosθeq1; try assumption. split; assumption.
  apply Rnot_le_lt in n0.
  apply Ropp_lt_contravar in n0.
  rewrite Ropp_0 in n0.
  apply Ropp_lt_contravar in blb.
  rewrite Ropp_involutive in blb.
  assert (0 <= -b) as zlenb. left; assumption.
  assert (-b < 2*PI) as nblt2pi. lra.
  rewrite <- cos_neg in cbeq1.
  rewrite <- (Ropp_involutive 0).
  rewrite <- (Ropp_involutive b).
  apply Ropp_eq_compat.
  rewrite Ropp_0.
  apply cosθeq1; try assumption. split; assumption.
Qed.

(* Conditions for which a choice of θc and the expression for r have the same sign. *)
Lemma ottb_r_thetac_lb_s :
  forall (x₁ y₁ θc : R)
         (nO : ~ (0 <= x₁ /\ y₁ = 0)),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI)) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      let r := (x₁ * sin θc - y₁ * cos θc) /
                       (1 - cos θc) in
      0 < r * θc.
Proof.
  intros.
  specialize (r_sign _ _ _ nO tcrng) as [rslt rsgt].
  unfold r in rslt, rsgt.
  change (0 < θc -> 0 < r) in rslt.
  change (θc < 0 -> r < 0) in rsgt.
  destruct (Rlt_dec 0 θc).
  specialize (rslt r0).
  apply Rmult_lt_0_compat; assumption.

  apply Rnot_lt_le in n.
  destruct n as [tclt0 |tceq0].
  specialize (rsgt tclt0).
  setr (- r * - θc).
  apply Rmult_lt_0_compat; lra.

  exfalso.
  clear rslt rsgt r.

  assert (~ (x₁ = 0 /\ y₁ = 0)) as nO2. {
    intros [p q]. apply nO.
    split; lra.
  }
  specialize (atan2_bound _ _ nO2) as [at2lb at2ub].


  destruct tcrng as [tclb tcub].
  destruct (Rlt_dec 0 θmax).
  + specialize (tclb r).
    clear tcub.
    destruct tclb as [[tcpl tcpu] |[tcnl tcnu]].
    lra.
    
    specialize (thms x₁ y₁) as tmdef.
    change (θmax = 2 * atan2 y₁ x₁) in tmdef.
    rewrite tmdef in *.
    clear tmdef θmax.
    rewrite tceq0 in *. clear tceq0.
    lra.

  + apply Rnot_lt_le in n.
    destruct n as [tmlt0 |tmeq0].
    specialize (tcub tmlt0).
    clear tclb.
    destruct tcub as [[tcpl tcpu] |[tcnl tcnu]].
    lra.
    
    specialize (thms x₁ y₁) as tmdef.
    change (θmax = 2 * atan2 y₁ x₁) in tmdef.
    rewrite tmdef in *.
    clear tmdef θmax.
    rewrite tceq0 in *. clear tceq0.
    lra.

    eapply thmaxne0; eauto.
Qed.

Lemma ottb_r_thetac_ub_s :
  forall (x₁ y₁ θc : R)
         (nO : ~ (0 <= x₁ /\ y₁ = 0)),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI)) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      let r := (x₁ * sin θc - y₁ * cos θc) /
                       (1 - cos θc) in
      r * θc < 2 * Rabs r * PI.
Proof.
  intros.
  specialize (ottb_r_thetac_lb_s _ _ _ nO tcrng) as rtcsign.
  unfold r in rtcsign.
  change (0 < r * θc) in rtcsign.

  assert (0 < Rabs r) as zltRabsr. {
    specialize (Rabs_pos r) as Rabsrge0.
    destruct Rabsrge0. assumption.
    exfalso.
    symmetry in H.
    apply Rabs_eq_0 in H.
    rewrite H in rtcsign.
    rewrite Rmult_0_l in rtcsign.
    clear - rtcsign. lra. }

  rewrite (sign_Rabs_eq r) at 1.
  apply (Rmult_lt_reg_r (/ Rabs r)).
  apply Rinv_0_lt_compat.
  assumption.

  setl (sign r * θc). intro; lra.
  setr (2 * PI). intro; lra.


  assert (~ (x₁ = 0 /\ y₁ = 0)) as nO2. {
    intros [p q]. apply nO.
    split; lra.
  }
  specialize (atan2_bound _ _ nO2) as [at2lb at2ub].

  specialize (thms x₁ y₁) as tmdef.
  change (θmax = 2 * atan2 y₁ x₁) in tmdef.
  
  destruct tcrng as [tmgl tmgu].
  unfold sign.
  destruct (total_order_T 0 r).
  + destruct s.
    destruct (Rlt_dec 0 θmax).
    specialize (tmgl r1).
    destruct tmgl as [[tmgll tmglu] |tmglu]; lra.

    apply Rnot_lt_le in n.
    destruct n as [tmlt0 |tmeq0].
    specialize (tmgu tmlt0).
    destruct tmgu as [[tmgll tmglu] |tmglu]; lra.

    exfalso; eapply thmaxne0; eauto.
    
    clear - rtcsign e.
    exfalso. rewrite <- e in rtcsign. lra.
    
  + apply Rgt_lt in r0.
    destruct (Rlt_dec 0 θmax).
    specialize (tmgl r1).
    destruct tmgl as [[tmgll tmglu] |tmglu]; lra.

    apply Rnot_lt_le in n.
    destruct n as [tmlt0 |tmeq0].
    specialize (tmgu tmlt0).
    destruct tmgu as [[tmgll tmglu] |tmglu]; lra.

    exfalso; eapply thmaxne0; eauto.
Qed.

Lemma calc_angle_std : forall θ₀ x₀ y₀ x₁ y₁,
    calcθ₁ θ₀ x₀ y₀ x₁ y₁ =
    calcθ₁ 0 0 0
           ((x₁-x₀)*cos θ₀ + (y₁-y₀)*sin θ₀)
           (- (x₁-x₀)* sin θ₀ + (y₁-y₀)*cos θ₀).
Proof.
  intros.
  unfold calcθ₁.
  autorewrite with null.
  reflexivity.
Qed.

Lemma rotated_straight_path_equiv :
  forall (x₀ y₀ θ₀ x₁ y₁ : R)
         (notO : ~ ((x₁-x₀) = 0 /\ (y₁-y₀) = 0))
         (tmns : calcθ₁ θ₀ x₀ y₀ x₁ y₁ <> 0),
         ~ (0 <= ((x₁-x₀)* cos θ₀ + (y₁-y₀)*sin θ₀) /\
       (- (x₁-x₀)* sin θ₀ + (y₁-y₀)*cos θ₀)=0).
Proof.
  intros.
  intros [zley xeq0].
  specialize (tmne0 _ _ _ _ _ notO tmns) as notpx.
  apply notpx. clear notpx.
  apply (atan2_rotation1 _ _ (-θ₀)); try assumption.
  rewrite sin_neg, cos_neg.
  fieldrewrite ((x₁ - x₀) * - sin θ₀ + (y₁ - y₀) * cos θ₀) (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀).
  fieldrewrite ((x₁ - x₀) * cos θ₀ - (y₁ - y₀) * - sin θ₀) ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀).
  exists 0%Z.
  fieldrewrite (θ₀ + - θ₀ + 2 * 0 * PI) 0.
  set (y := - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in *.
  set (x := (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in *.
  rewrite xeq0 in *.
  destruct zley.
  apply atan2_0; try assumption.
  exfalso.
  apply notO. clear notO.
  symmetry in H. unfold x,y in *. clear x y. 
  destruct (Req_dec (cos θ₀) 0) as [costeq0 | costne0].
  rewrite costeq0, Rmult_0_r, Rplus_0_r, Rplus_0_l in *.
  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tpigt0. lra.
  specialize (inrange_mT2T2 θ₀ _ tpigt0) as [m [lb ub]].
  assert (- (2 * PI) / 2 = -PI) as id. field. rewrite id in lb. clear id.
  assert (2 * PI / 2 = PI) as id. field. rewrite id in ub. clear id.
  assert (IZR m * (2 * PI) = 2 * IZR m * PI) as id. field.
  rewrite id in lb, ub. clear id.
  rewrite <- (cos_period1 _ m) in costeq0.
  apply coseq0_sinneq0_rng in costeq0; [|split; assumption].

  apply Rmult_integral in H.
  destruct H as [ydeq0| sinteq0].
  apply Rmult_integral in xeq0.
  destruct xeq0 as [xdeq0| cost0eq0].
  split; lra.
  exfalso.
  rewrite sin_period1 in costeq0.
  apply costeq0. assumption.
  exfalso.
  rewrite sin_period1 in costeq0.
  apply costeq0. assumption.

  destruct (Req_dec (x₁ - x₀) 0) as [xseq0|xene0].
  rewrite xseq0 in *.
  autorewrite with null in *.
  apply Rmult_integral in xeq0 as [yseq0|costeq0].
  split; auto.
  exfalso; apply costne0; assumption.
  assert (tan θ₀ = (y₁ - y₀)/(x₁ - x₀)) as tdef. {
    apply (Rmult_eq_reg_r ((x₁ - x₀) * cos θ₀)).
    unfold tan.
    setl ((x₁ - x₀)*sin θ₀); try assumption.
    setr ((y₁ - y₀)*cos θ₀); try assumption.
    apply Rplus_opp_r_uniq in xeq0. rewrite xeq0.
    field.
    apply Rmult_integral_contrapositive_currified; try assumption.
  }

  destruct (Req_dec (y₁ - y₀) 0) as [yeeq0|yene0].
  rewrite yeeq0, Rmult_0_l, Rplus_0_r in *.
  apply Rmult_integral in H. destruct H. auto.
  exfalso. apply costne0. assumption.
  assert (tan θ₀ = -(x₁ - x₀)/(y₁ - y₀)) as tdef2. {
    apply (Rmult_eq_reg_r ((y₁ - y₀) * cos θ₀)).
    unfold tan.
    setl ((y₁ - y₀)*sin θ₀); try assumption.
    setr (- (x₁ - x₀)*cos θ₀); try assumption.
    apply Rplus_opp_r_uniq in H. rewrite H.
    field.
    apply Rmult_integral_contrapositive_currified; try assumption.
  }

  rewrite tdef2 in tdef.
  assert ((y₁ - y₀)² + (x₁ - x₀)² = 0) as sqr0. {
    apply (Rplus_eq_reg_r (-(x₁ - x₀)²)).
    apply (Rmult_eq_reg_r (/ (y₁ - y₀) * / (x₁ - x₀))).
    setl ((y₁ - y₀) / (x₁ - x₀)). split; assumption.
    setr (- (x₁ - x₀) / (y₁ - y₀)). split; assumption.
    symmetry. assumption.
    apply Rmult_integral_contrapositive_currified;
      apply Rinv_neq_0_compat; assumption.
  }
  apply Rplus_sqr_eq_0_l in sqr0.
  exfalso. apply yene0. assumption.
Qed.

Lemma xxlate_arm : forall r θ₀ x₀ x₁ θc,
  (x₁ - Hxarc r θ₀ x₀ (r * θc)) = 
  ((x₁-x₀) - Hxarc r θ₀ 0 (r * θc)).
Proof.
  intros. unfold Hxarc. field.
Qed.

Lemma yxlate_arm : forall r θ₀ y₀ y₁ θc,
  (y₁ - Hyarc r θ₀ y₀ (r * θc)) = 
  ((y₁-y₀) - Hyarc r θ₀ 0 (r * θc)).
Proof.
  intros. unfold Hyarc. field.
Qed.

Lemma xlate_rot_arm :
  forall (x₀ y₀ θ₀ x₁ y₁ θc r: R)
         (rne0 : r <> 0)
         (notO : ~ (x₁ - Hxarc r θ₀ x₀ (r * θc) = 0 /\
                    y₁ - Hyarc r θ₀ y₀ (r * θc) = 0))
         (Ldir : exists k, atan2 (y₁ - Hyarc r θ₀ y₀ (r * θc))
                                 (x₁ - Hxarc r θ₀ x₀ (r * θc)) =
                           θ₀ + θc + 2* IZR k * PI),
  exists m, atan2 (- (x₁ - x₀)*sin θ₀ + (y₁ - y₀)*cos θ₀
                                      - Hyarc r 0 0 (r*θc))
                  ((x₁ - x₀)*cos θ₀ + (y₁ - y₀)* sin θ₀
                                      - Hxarc r 0 0 (r*θc)) =
            θc + 2* IZR m * PI.
Proof.
  intros.
  destruct Ldir as [k sw].
  apply (atan2_rotation _ _ (-θ₀)) in sw; try assumption.
  destruct sw as [n sw].
  assert (θ₀ + θc + 2 * IZR k * PI + - θ₀ + 2 * IZR n * PI =
          θc + 2 * IZR (k+n) * PI) as id. rewrite plus_IZR. field.
  rewrite id in sw. clear id.

  rewrite sin_neg, cos_neg in sw.
  rewrite xxlate_arm, yxlate_arm in sw.

  unfold Hyarc, Hxarc in *.
  rewrite (Rmult_minus_distr_r _ _ (- sin θ₀)) in sw.
  rewrite (Rmult_minus_distr_r _ _ (cos θ₀)) in sw.
  rewrite (Rmult_minus_distr_r (y₁ - y₀) _ (- sin θ₀)) in sw.
  rewrite (Rmult_minus_distr_r (x₁ - x₀) _ (cos θ₀)) in sw.
  repeat rewrite Rplus_0_r in *.

  rewrite (Rmult_minus_distr_r _ (r * sin θ₀) (- sin θ₀)) in sw.
  rewrite (Rmult_plus_distr_r _ (r*cos θ₀) (cos θ₀)) in sw.
  rewrite (Rmult_minus_distr_r _ (r * sin θ₀) (cos θ₀)) in sw.
  rewrite (Rmult_plus_distr_r _ (r * cos θ₀) (- sin θ₀)) in sw.

  autorewrite with null.
  exists (k+n)%Z. rewrite <- sw. clear sw.

  assert (((x₁ - x₀) * - sin θ₀ -
                (r * sin (r * θc / r + θ₀) * - sin θ₀ - r * sin θ₀ * - sin θ₀) +
                ((y₁ - y₀) * cos θ₀ -
                 (- r * cos (r * θc / r + θ₀) * cos θ₀ + r * cos θ₀ * cos θ₀)))
          = (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀
            - (- r * (cos (r * θc / r + θ₀) * cos θ₀ +
                      sin (r * θc / r + θ₀) * sin θ₀)
         + r * ((sin θ₀)² + (cos θ₀)²)))) as id.
  unfold Rsqr. field. rewrite id. clear id.
  rewrite <- cos_minus, sin2_cos2.

  assert (((x₁ - x₀) * cos θ₀ -
          (r * sin (r * θc / r + θ₀) * cos θ₀ - r * sin θ₀ * cos θ₀) -
          ((y₁ - y₀) * - sin θ₀ -
           (- r * cos (r * θc / r + θ₀) * - sin θ₀ + r * cos θ₀ * - sin θ₀)))=
         ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀
                               - r * (sin (r * θc / r + θ₀) * cos θ₀ -
                                      cos (r * θc / r + θ₀) * sin θ₀)
            )) as id.
  unfold Rsqr. field. rewrite id. clear id.
  rewrite <- sin_minus, Rmult_1_r.
  fieldrewrite (r * θc / r + θ₀ - θ₀) (θc).
  intro; lra.
  fieldrewrite (r * θc / r) (θc). intro; lra.
  reflexivity.
Qed.

Lemma Hxarc_rot : forall r θ₀ θc,
  Hxarc r θ₀ 0 (r * θc) =
  Hxarc r 0 0 (r * θc) * cos θ₀ - Hyarc r 0 0 (r * θc) * sin θ₀.
Proof.
  intros.
  unfold Hxarc, Hyarc.
  destruct (Req_dec r 0).
  + subst.
    autorewrite with null.
    reflexivity.
  + fieldrewrite (r * θc / r + θ₀) (θc + θ₀); try assumption.
    fieldrewrite (r * θc / r + 0) θc; try assumption.
    autorewrite with null.
    apply (Rmult_eq_reg_r (/r));
      [|apply Rinv_neq_0_compat; assumption].
    setl (sin (θc + θ₀) - sin θ₀); try assumption.
    setr (sin θc * cos θ₀ - (1 - cos θc) * sin θ₀); try assumption.
    rewrite sin_plus. field.
Qed.

Lemma Hyarc_rot : forall r θ₀ θc,
  Hyarc r θ₀ 0 (r * θc) =
  Hxarc r 0 0 (r * θc) * sin θ₀ + Hyarc r 0 0 (r * θc) * cos θ₀.
Proof.
  intros.
  unfold Hxarc, Hyarc.
  destruct (Req_dec r 0).
  + subst.
    autorewrite with null.
    reflexivity.
  + fieldrewrite (r * θc / r + θ₀) (θc + θ₀); try assumption.
    fieldrewrite (r * θc / r + 0) θc; try assumption.
    autorewrite with null.
    apply (Rmult_eq_reg_r (/r));
      [|apply Rinv_neq_0_compat; assumption].
    setl (- cos (θc + θ₀) + cos θ₀); try assumption.
    setr (sin θc * sin θ₀ + (1 - cos θc) * cos θ₀); try assumption.
    rewrite cos_plus. field.
Qed.

Lemma ottb_r_thetac_lb :
  forall (θ₀ x₀ y₀ x₁ y₁ θc : R)
         (nO : ~ ((x₁-x₀) = 0 /\ (y₁-y₀) = 0)),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmns : θmax <> 0)
           (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI)) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      (* choose radius where angle is tangent*)
      let r := ((x₁ - x₀) * sin (θ₀ + θc) - (y₁ - y₀) * cos (θ₀ + θc))
                 / ( 1 - cos θc) in
      0 < r * θc.
Proof.
  intros.
  unfold r. clear r.
  rewrite rxlate.
  specialize (rotated_straight_path_equiv _ _ _ _ _ nO tmns) as nots.
  unfold θmax in *. clear θmax.
  rewrite calc_angle_std in *.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  set (r := (x * sin θc - y * cos θc) / (1 - cos θc)) in *.
  set (θmax := calcθ₁ 0 0 0 x y) in *.
  apply ottb_r_thetac_lb_s; try assumption.
Qed.

Lemma ottb_r_thetac_ub :
  forall (θ₀ x₀ y₀ x₁ y₁ θc : R)
         (nO : ~ ((x₁-x₀) = 0 /\ (y₁-y₀) = 0)),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmns : θmax <> 0)
           (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI)) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      (* choose radius where angle is tangent*)
      let r := ((x₁ - x₀) * sin (θ₀ + θc) - (y₁ - y₀) * cos (θ₀ + θc))
                 / ( 1 - cos θc) in
      r * θc < 2 * Rabs r * PI.
Proof.
  intros.
  unfold r. clear r.
  rewrite rxlate.
  specialize (rotated_straight_path_equiv _ _ _ _ _ nO tmns) as nots.
  unfold θmax in *. clear θmax.
  rewrite calc_angle_std in *.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  set (r := (x * sin θc - y * cos θc) / (1 - cos θc)) in *.
  set (θmax := calcθ₁ 0 0 0 x y) in *.
  apply ottb_r_thetac_ub_s; try assumption.
Qed.

(* The inequality crng is a short way to express that c is bounded
differently by M and s, depending on the sign of M as shown. *)
Lemma order_condition : forall r M s c
    (srng: 0 < s < 1)
    (crng : r*M*s < r*c < r*M),
    (0 < M -> M*s < c < M) /\ (M < 0 -> M < c < M*s).
Proof.
  intros.
  inversion_clear srng as [slb sub].
  inversion_clear crng as [clb cub].
  generalize (total_order_T 0 M) as tot0M ; intro.
  generalize (total_order_T 0 r) as tot0r ; intro.
  inversion_clear tot0M as [[zltM  |zeqM] | zgtM].
  inversion_clear tot0r as [[zltr  |zeqr] | zgtr].
  split; intro. split.
  apply (Rmult_lt_reg_l r). assumption.
  fieldrewrite (r * (M * s)) (r * M * s).
  assumption.
  apply (Rmult_lt_reg_l r). assumption.
  assumption.
  exfalso. lra.
  rewrite <- zeqr in *. lra.

  split; intro.
  exfalso.
  assert (r * M < r * M * s).
  apply (Rmult_lt_reg_l (/ (- r * M))).
  apply Rinv_0_lt_compat.
  apply Rmult_lt_0_compat.
  apply Ropp_0_gt_lt_contravar. assumption. assumption.
  setr (-s). split; intro; lra.
  setl (-1). split; intro; lra.
  apply Ropp_lt_contravar. assumption.
  unfold IPR.
  assert (r * M * s < r * M) as opp.
  apply (Rlt_trans _ (r*c)). assumption. assumption.
  lra.
  lra.

  exfalso.
  rewrite <- zeqM in *.

  assert (0 < r * c < 0).
  split. setl (r * 0 * s).
  assumption. setr (r * 0). assumption.
  inversion H. lra.

  inversion_clear tot0r as [[zltr | zeqr]|zgtr].

  split; intro. lra.

  assert (r * M< r * M * s ).
  apply (Rmult_lt_reg_l (/ (r * - M))).
  apply Rinv_0_lt_compat.
  apply Rmult_lt_0_compat.  assumption.
  apply Ropp_0_gt_lt_contravar. assumption.
  setr (-s). split; intro; lra.
  setl (-1). split; intro; lra.
  apply Ropp_lt_contravar. assumption.
  unfold IPR.
  assert (r * M * s < r * M) as opp.
  apply (Rlt_trans _ (r*c)). assumption. assumption.
  lra.

  rewrite <- zeqr in *.
  lra.

  split; intro.
  exfalso.  lra.
  split.
  apply (Rmult_lt_reg_l (- r)).
  apply Ropp_0_gt_lt_contravar. assumption.
  setl (- (r * M)). setr (- (r * c)).
  apply Ropp_lt_contravar. assumption.
  apply (Rmult_lt_reg_l (- r)).
  apply Ropp_0_gt_lt_contravar. assumption.
  setl (- (r * c)). setr (- (r * M * s)).
  apply Ropp_lt_contravar. assumption.
Qed.

(* The inequality crng is a short way to express that c is bounded by
 M, depending on the sign of M as shown. A specialization of
 order_condition for s=.5 *)
Lemma order_condition2 : forall r M c
    (crng : r*M/2 < r*c < r*M),
    (0 < M -> M/2 < c < M) /\ (M < 0 -> M < c < M/2).
Proof.
  intros.
  assert (M / 2 = M * /2). field. rewrite H in *.
  assert (r * M / 2 = r * M * /2). field. rewrite H0 in crng.
  clear H H0.
  apply (order_condition r). split; lra. assumption.
Qed.

(* calcL and calcL' are both computations finding the hypotenuse of a
triangle, and their values are equal under these conditions. We will
see that this quantity turns out to be the distance of the linear part
of the path. *)
Lemma ottb_parameters_L_calc_s :
  forall (x₁ y₁ θc : R)
         (notpx : ~ (0<=x₁ /\ y₁=0)),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI)) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      (* choose radius where angle is tangent*)
      let r := (x₁ * sin θc - y₁ * cos θc) /
                       (1 - cos θc) in
      (* ensure correct direction of linear path *)
      forall (Ldir : exists k, atan2 (y₁ - Hyarc r 0 0 (r * θc))
                                     (x₁ - Hxarc r 0 0 (r * θc)) =
                               θc + 2* IZR k * PI),
        calcL r 0 0 0 x₁ y₁ θc = calcL' r 0 0 0 x₁ y₁ θc.
Proof.
  intros.
  set (Ldx := (x₁ - Hxarc r 0 0 (r * θc))) in *.
  set (Ldy := (y₁ - Hyarc r 0 0 (r * θc))) in *.
  unfold calcL'.
  set (L := sqrt ( Ldy² + Ldx²)) in *.
  change (calcL r 0 0 0 x₁ y₁ θc = L).
  inversion_clear Ldir as [k Ldir']. rename Ldir' into Ldir.

  specialize (ottb_r_thetac_lb_s _ _ _ notpx tcrng) as zltrthc.
  unfold r in zltrthc. change (0 < r * θc) in zltrthc.
  assert (r <> 0) as zne0. intro. rewrite H in zltrthc.
  rewrite Rmult_0_l in zltrthc. clear - zltrthc. lra.

  
  assert (0 < 1 - cos θc) as zlt1mcosz. {
    specialize (COS_bound (θc)) as [coszlb coszub].
    destruct coszub as [coszlt1 |coszeq1]. lra.
    exfalso.
    specialize PI_RGT_0 as PIgt0.
    assert (2*PI > 0) as tPIgt0; [lra|].
    specialize (inrange_0T θc (2*PI) tPIgt0) as [m bnds].
    rewrite <- Rmult_assoc in bnds.
    rewrite (Rmult_comm _ 2) in bnds.
    rewrite <- (cos_period1 _ m) in coszeq1.
    specialize (cosθeq1 _ bnds coszeq1) as thdef.
    rewrite Rplus_comm in thdef.
    apply Rplus_opp_r_uniq in thdef.

    assert (~ (x₁ = 0/\ y₁ = 0)) as notpx2. {
      clear - notpx.
      lra. }

    assert (-2*PI < θmax <= 2*PI) as [tmu tml]. {
      clear - notpx notpx2.
      unfold θmax, calcθ₁ in *. clear θmax.
      assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
      rewrite id. clear id.
      assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
      rewrite id. clear id.
      specialize (atan2_bound _ _ notpx2) as [at2lb at2ub].
      lra. }

    assert (θmax <> 0) as tmne0. {
      unfold θmax, calcθ₁ in *. clear θmax.
      assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id. rewrite sin_0, cos_0. field.
      rewrite id. clear id.
      assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id. rewrite sin_0, cos_0. field.
      rewrite id. clear id.
      intro tat2ne0.
      clear - notpx tat2ne0 notpx2.
      assert (atan2 y₁ x₁ = 0) as at2ne0. lra.
      specialize (atan2_0_impl _ _ notpx2 at2ne0).
      intro. apply notpx. lra.
    }
    
    assert (-2*PI < θc < 2*PI) as tcallrng. {
      clear - tcrng tmu tml tmne0.
      destruct tcrng as [gt0 lt0].
      destruct (Rlt_dec 0 θmax).
      specialize (gt0 r). clear lt0.
      destruct gt0 as [[tc1rngl tc1rngh] | [tc2rngl tc2rngh]]; lra.
      apply Rnot_lt_le in n.
      lra. }

    clear notpx2 tmu tml tmne0.
    destruct tcallrng as [tcalll tcallu].
    destruct m.
    rewrite thdef in zltrthc. clear - zltrthc. lra.

    assert (1 <= IZR (Z.pos p)) as gt1. {
      apply IZR_le. lia. }
    
    rewrite thdef in tcalll.
    clear - tcalll gt1 tPIgt0.
    assert (-2 *PI = -(2*PI)) as id. field. rewrite id in tcalll.
    apply Ropp_lt_cancel in tcalll.
    assert (IZR (Z.pos p) < 1) as ctrd.
    apply (Rmult_lt_reg_l 2); try lra.
    rewrite Rmult_1_r.
    apply (Rmult_lt_reg_r PI); try lra.
    lra.

    assert (IZR (Z.neg p) <= -1 ) as ltn1. {
      apply IZR_le. lia. }

    rewrite thdef in tcallu.
    clear - tcallu ltn1 tPIgt0.
    rewrite <- Ropp_involutive in tcallu.
    apply Ropp_lt_cancel in tcallu.
    assert (-1 < IZR (Z.neg p)) as ctrd. {
    apply (Rmult_lt_reg_l 2); try lra.
    apply (Rmult_lt_reg_r PI); try lra. }
    lra.
  }


  assert (Ldy * cos (θc)= Ldx * sin (θc)) as rcq. {
  unfold Ldy, Ldx, Hyarc, Hxarc.
  fieldrewrite (r * θc / r) ( θc). assumption.

  fieldrewrite (θc + 0) (θc).
  autorewrite with null.  
  setl (y₁* cos θc + r * cos θc* cos θc - r* cos θc).
  apply (Rplus_eq_reg_l (r * sin θc * sin θc)).
  setr (x₁ * sin θc).
  setl (r * ((sin θc)² + (cos θc)²) + y₁ * cos θc - r * cos θc).
  rewrite sin2_cos2.
  setl (y₁ * cos θc + r * (1 - cos θc)).

  unfold r.
  setl (y₁ * cos θc + (x₁ * sin θc - y₁ * cos θc)). intro. lra.
  lra. }

  
  unfold atan2 in Ldir.
  destruct (pre_atan2 Ldy Ldx) as [ζ [valrng [Ldydef Ldxdef]]].
  rewrite Ldir in *.

  assert (sin ζ  = sin (θc)) as sinper. {
    rewrite Ldir.
    rewrite sin_period1. reflexivity. }

  assert (cos ζ  = cos (θc)) as cosper. {
    rewrite Ldir.
    rewrite cos_period1. reflexivity. }

  rewrite <- Ldir in Ldydef, Ldxdef.
  rewrite <- Ldir in valrng.
  
  unfold calcL, L.
  fieldrewrite (0 + θc) (θc).
  destruct (Req_EM_T 0 (cos (θc))).
  + symmetry in e.
    generalize (coseq0_sinneq0 _ e) as sinne0; intro.

    change (Ldy / sin θc = L).
    apply (Rmult_eq_reg_r (sin θc));
      [| assumption].
    setl Ldy. assumption.

    rewrite e in rcq.
    assert (Ldx = 0) as dxdef. symmetry.
    apply (Rmult_eq_reg_r (sin (θc))); [|assumption].
    setl (Ldy * 0). assumption. clear rcq.
    unfold L.
    rewrite dxdef.
    unfold Rsqr at 2.
    fieldrewrite (Ldy² + 0 * 0) (Ldy²).
    rewrite sqrt_Rsqr_abs.
    
    rewrite <- sinper.
    rewrite <- cosper in e.
    inversion_clear valrng as [zetalb zetaub].
    
    destruct (Rle_dec 0 ζ).
    assert (ζ <= 2 * PI) as zeta2PIub. lra.
    specialize (cos_eq_0_2PI_0 ζ r0 zeta2PIub e) as zetaval.
    inversion_clear zetaval as [zeta | nzeta].
    ++ rewrite zeta in *. rewrite sin_PI2 in *.
       assert (0 <= Ldy).
       rewrite Ldydef.
       apply Rmult_le_pos.
       apply sqrt_pos. lra.
       rewrite Rabs_pos_eq. field. assumption.
    
    ++ exfalso.
       rewrite nzeta in zetaub.
       assert (3 <= 2) as contra.
       apply (Rmult_le_reg_r (PI/2)). lra.
       setr PI. assumption.
       lra.

    ++ clear zetaub.
       apply Rnot_le_lt in n.

       fieldrewrite ζ (- - ζ).
       rewrite sin_neg.
       assert (0 <= - ζ) as nzlb. lra.
       assert (- ζ <= 2*PI) as nzub. lra.
       rewrite <- cos_neg in e.
       generalize (cos_eq_0_2PI_0 (-ζ) nzlb nzub e) as zetaval. intro.
       inversion_clear zetaval as [zeta | nzeta].
       rewrite zeta.
       
       rewrite sin_PI2.
       assert (ζ = - - ζ) as zetanegneg. field. rewrite zetanegneg in Ldydef.
       rewrite sin_neg, zeta, sin_PI2 in Ldydef.
       assert (Ldy <= 0) as ldylt0.
       rewrite Ldydef.
       setl (- sqrt (Ldy² + Ldx²)). setr (- 0).
       apply Ropp_le_contravar.
       apply sqrt_pos.
       inversion_clear ldylt0.
       rewrite Rabs_left. field.  assumption.
       rewrite H. rewrite Rabs_R0. field.
       
       exfalso.
       assert (3 < 2) as absurd.
       apply (Rmult_lt_reg_r (PI/2)). lra.
       rewrite <- nzeta.
       setr (- - PI).
       apply Ropp_lt_contravar. assumption. lra.
       
  + change (Ldx / cos (θc) = L).
    apply (Rmult_eq_reg_r (cos (θc)));
      [| auto].
    setl (Ldx). auto.
    
    unfold L.
    rewrite <- cosper.
    assumption.
Qed.

Lemma calcL'_inv : forall r θ₀ x₀ y₀ x₁ y₁ θc,
    calcL' r θ₀ x₀ y₀ x₁ y₁ θc =
    calcL' r 0 0 0
           ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
           (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) θc.
Proof.
  intros.
  unfold calcL'.
  destruct (Req_dec r 0) as [req0 | rne0].
  + unfold Hxarc, Hyarc.
    rewrite req0.
    autorewrite with null.
    
    assert (((- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)² +
             ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)²) =
            (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²)+
            (x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²)) as id.
    unfold Rsqr. field. rewrite id, sin2_cos2, Rmult_1_r, Rmult_1_r.
    reflexivity.
    
  +  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
     set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
     unfold Hxarc, Hyarc.
     fieldrewrite (r * θc / r + 0) (θc); try assumption.
     fieldrewrite (r * θc / r + θ₀) (θc + θ₀); try assumption.
     autorewrite with null.
     apply f_equal.
     rewrite cos_plus, sin_plus.

     fieldrewrite
       ((y₁ - (- r * (cos θc * cos θ₀ - sin θc * sin θ₀) + r * cos θ₀ + y₀))² +
        (x₁ - (r * (sin θc * cos θ₀ + cos θc * sin θ₀) - r * sin θ₀ + x₀))²)
       (((y₁ - y₀) +  (- (- r * cos θc + r) * cos θ₀ - r *sin θc * sin θ₀))² +
        ((x₁ - x₀) + ((- r * cos θc + r) * sin θ₀ - r *sin θc * cos θ₀))²).

     set (yarc := (- r * cos θc + r)) in *.
     set (xarc := r * sin θc) in *.

     setl
       ((y₁ - y₀)² + (x₁ - x₀)² +
        yarc² * ((sin θ₀)² + (cos θ₀)²) +
        xarc² * ((sin θ₀)² + (cos θ₀)²)
        - 2 * (y₁ - y₀)* (yarc * cos θ₀ + xarc * sin θ₀)
        - 2 * (x₁ - x₀) * (- yarc * sin θ₀ + xarc * cos θ₀)).
     rewrite sin2_cos2, Rmult_1_r, Rmult_1_r.

     setl
       ((y₁ - y₀)² + (x₁ - x₀)²
        - 2 * yarc * (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)
        - 2 * xarc * ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
        + (yarc)² + (xarc)²).

     change  ((y₁ - y₀)² + (x₁ - x₀)²
        - 2 * yarc * y
        - 2 * xarc * x
              + (yarc)² + (xarc)² = (y - yarc)² + (x - xarc)²).

     enough ((y₁ - y₀)² + (x₁ - x₀)² = y² + x²) as dst.
     rewrite dst. unfold Rsqr; field.

     unfold y,x.
     setr ((x₁ - x₀)² * ((sin θ₀)²+(cos θ₀)²) + (y₁ - y₀)² * ((sin θ₀)²+(cos θ₀)²)).
     rewrite sin2_cos2, Rmult_1_r, Rmult_1_r.
     rewrite Rplus_comm.
     reflexivity.
Qed.
  
Lemma calcL_inv : forall r θ₀ x₀ y₀ x₁ y₁ θc,
    forall (Ldir : exists k, atan2 (y₁ - Hyarc r θ₀ y₀ (r * θc))
                                   (x₁ - Hxarc r θ₀ x₀ (r * θc)) =
                             θ₀ + θc + 2* IZR k * PI),
    calcL r θ₀ x₀ y₀ x₁ y₁ θc =
    calcL r 0 0 0
           ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
           (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) θc.
Proof.
  intros. unfold calcL.
  specialize Ldir as at21.
  
  rewrite xxlate_arm, yxlate_arm.
  rewrite xxlate_arm, yxlate_arm in Ldir.
  destruct Ldir as [k Ldir].
  unfold atan2 in Ldir.
  destruct (pre_atan2 (y₁ - y₀ - Hyarc r θ₀ 0 (r * θc))
                      (x₁ - x₀ - Hxarc r θ₀ 0 (r * θc))) as [a [ar [yd xd]]].
  set (L := sqrt ((y₁ - y₀ - Hyarc r θ₀ 0 (r * θc))² +
                  (x₁ - x₀ - Hxarc r θ₀ 0 (r * θc))²)) in *.
  rewrite Ldir in yd, xd.
  rewrite sin_period1 in yd.
  rewrite cos_period1 in xd.

  assert ((if Req_EM_T 0 (cos (θ₀ + θc))
           then (y₁ - y₀ - Hyarc r θ₀ 0 (r * θc)) / sin (θ₀ + θc)
           else (x₁ - x₀ - Hxarc r θ₀ 0 (r * θc)) / cos (θ₀ + θc)) = L) as Lm.
  
  destruct (Req_EM_T 0 (cos (θ₀ + θc))) as [zeqct0tc |znect0tc];
    [ symmetry in zeqct0tc; specialize zeqct0tc as ct0tceqz;
      apply coseq0_sinneq0 in zeqct0tc | apply not_eq_sym in znect0tc].
  rewrite yd. field. assumption.
  rewrite xd. field. assumption.
  rewrite Lm. clear Lm.

  specialize PI_RGT_0 as pigt0.
  assert (2 * PI > 0) as tpigt0; [lra|].
  specialize (inrange_mT2T2 θc _ tpigt0) as [l ir].

  destruct (Req_dec r 0) as [req0|rne0].
  + unfold L, Hxarc, Hyarc in *. clear L.
    rewrite req0 in *.
    rewrite Ropp_0 in *.
    autorewrite with null in *.

    set (L := sqrt ((y₁ - y₀)² + (x₁ - x₀)²)) in *.
    destruct (Req_EM_T 0 (cos θc)) as [zeqctc | znectc].
    ++ assert (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ =
               L * sin θc) as id. {
         rewrite <- (Rplus_0_l (sin θc)).
         rewrite <- (Rmult_1_l (sin θc)).
         rewrite <- (sin2_cos2 θ₀).
         setr (- (L * (cos θ₀ * cos θc - sin θ₀ * sin θc)) * sin θ₀ +
               (L * (sin θ₀ * cos θc + cos θ₀ * sin θc)) * cos θ₀).
         rewrite <- cos_plus, <- sin_plus, <- yd, <- xd. reflexivity.
       }
       rewrite id. clear id.
       field.
       intro.
       apply (cos_sin_0 θc).
       split; auto.
  ++ assert ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ =
               L * cos θc) as id. {
         rewrite <- (Rplus_0_l (cos θc)).
         rewrite <- (Rmult_1_l (cos θc)).
         rewrite <- (sin2_cos2 θ₀).
         setr ((L * (cos θ₀ * cos θc - sin θ₀ * sin θc)) * cos θ₀ +
               (L * (sin θ₀ * cos θc + cos θ₀ * sin θc)) * sin θ₀).
         rewrite <- cos_plus, <- sin_plus, <- yd, <- xd. reflexivity.
       }
       rewrite id. clear id.
       field. auto.

  + destruct (Req_dec L 0) as [Leq0 | Lne0].
    ++ rewrite Leq0.
       unfold L in Leq0.
       rewrite <- sqrt_0 in Leq0 at 3.
       apply sqrt_inj in Leq0;
         [|apply Rplus_le_le_0_compat; apply Rle_0_sqr|right; reflexivity].
       specialize (Rle_0_sqr (y₁ - y₀ - Hyarc r θ₀ 0 (r * θc)))
         as zleyd.
       specialize (Rle_0_sqr (x₁ - x₀ - Hxarc r θ₀ 0 (r * θc)))
         as zlexd.
       destruct zleyd as [zltyd | zeqyd].
       specialize (Rplus_lt_le_0_compat _ _ zltyd zlexd) as ctrd.
       rewrite Leq0 in ctrd.
       clear - ctrd. lra.
       symmetry in zeqyd. rewrite zeqyd in Leq0.
       rewrite Rplus_0_l in Leq0. clear zlexd.
       apply Rsqr_eq_0 in Leq0.
       apply Rsqr_eq_0 in zeqyd.

       destruct (Req_EM_T 0 (cos (0 + θc))).
       +++ symmetry in e.
           apply coseq0_sinneq0 in e.
           apply (Rmult_eq_reg_r (sin (0 + θc)));
             [|assumption].
           setl 0.
           setr (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ - Hyarc r 0 0 (r * θc));
             try assumption.
           rewrite Hyarc_rot in zeqyd.
           rewrite Hxarc_rot in Leq0.
           set (dx := x₁ - x₀) in *.
           set (dy := y₁ - y₀) in *.
           set (Y := Hyarc r 0 0 (r * θc)) in *.
           set (X := Hxarc r 0 0 (r * θc)) in *.
           apply Rminus_diag_uniq in Leq0.
           apply Rminus_diag_uniq in zeqyd.
           rewrite Leq0, zeqyd.
           setr ( Y * ((sin θ₀)² + (cos θ₀)²) - Y).
           rewrite sin2_cos2. field.
           
       +++ apply (Rmult_eq_reg_r (cos (0 + θc)));
             [|auto].
           setl 0.
           setr ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ - Hxarc r 0 0 (r * θc));
             try auto.
           rewrite Hyarc_rot in zeqyd.
           rewrite Hxarc_rot in Leq0.
           set (dx := x₁ - x₀) in *.
           set (dy := y₁ - y₀) in *.
           set (Y := Hyarc r 0 0 (r * θc)) in *.
           set (X := Hxarc r 0 0 (r * θc)) in *.
           apply Rminus_diag_uniq in Leq0.
           apply Rminus_diag_uniq in zeqyd.
           rewrite Leq0, zeqyd.
           setr ( X * ((sin θ₀)² + (cos θ₀)²) - X).
           rewrite sin2_cos2. field.
       
  ++ assert (~ (x₁ - Hxarc r θ₀ x₀ (r * θc) = 0 /\
                y₁ - Hyarc r θ₀ y₀ (r * θc) = 0)) as nO. {
       intros [x0 y0].
       apply Lne0.
      rewrite xxlate_arm in x0.
      rewrite yxlate_arm in y0.
      apply Rminus_diag_uniq in x0.
      apply Rminus_diag_uniq in y0.
      unfold L.
      rewrite x0, y0.
      fieldrewrite ((Hyarc r θ₀ 0 (r * θc) - Hyarc r θ₀ 0 (r * θc))² +
                    (Hxarc r θ₀ 0 (r * θc) - Hxarc r θ₀ 0 (r * θc))²)
                   (0² + 0²).
      rewrite Rsqr_0, Rplus_0_l, sqrt_0. reflexivity. }
     specialize (xlate_rot_arm _ _ _ _ _ _ _ rne0 nO at21) as [m at2d].
     unfold atan2 in at2d.
     destruct (pre_atan2
              (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ -
                                      Hyarc r 0 0 (r * θc))
              ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ -
                                    Hxarc r 0 0 (r * θc)))
       as [b [br [yd' xd']]].

     rewrite at2d in *.
     rewrite sin_period1 in yd'.
     rewrite cos_period1 in xd'.
     set (L':= sqrt
                 ((- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀
                                          - Hyarc r 0 0 (r * θc))² +
                  ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀
                                        - Hxarc r 0 0 (r * θc))²)) in *.
     rewrite yd'.
     rewrite xd'.
     rewrite Rplus_0_l.

     destruct (Req_EM_T 0 (cos θc)).
     +++ setr L'.
         symmetry in e.
         apply coseq0_sinneq0; assumption.
         apply f_equal.
         set (dy := y₁ - y₀) in *.
         set (dx := x₁ - x₀) in *.
         rewrite Hyarc_rot, (Hxarc_rot r θ₀ θc).
         set (X := Hxarc r 0 0 (r * θc)) in *.
         set (Y := Hyarc r 0 0 (r * θc)) in *.
         apply rot1_rot2.
        
     +++ setr L'.
         auto.
         apply f_equal.
         set (dy := y₁ - y₀) in *.
         set (dx := x₁ - x₀) in *.
         rewrite Hyarc_rot, (Hxarc_rot r θ₀ θc).
         set (X := Hxarc r 0 0 (r * θc)) in *.
         set (Y := Hyarc r 0 0 (r * θc)) in *.
         apply rot1_rot2.
Qed.

Lemma ottb_parameters_L_calc :
  forall (θ₀ x₀ y₀ x₁ y₁ θc : R)
         (notO : ~ ((x₁-x₀) = 0 /\ (y₁-y₀) = 0)),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmns : θmax <> 0)
           (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI)) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      (* choose radius where angle is tangent*)
      let r := ((x₁ - x₀) * sin (θ₀ + θc) - (y₁ - y₀) * cos (θ₀ + θc))
                 / ( 1 - cos θc) in
      (* ensure correct direction of linear path *)
      forall (Ldir : exists k, atan2 (y₁ - Hyarc r θ₀ y₀ (r * θc))
                                     (x₁ - Hxarc r θ₀ x₀ (r * θc)) =
                               θ₀ + θc + 2* IZR k * PI),
        calcL r θ₀ x₀ y₀ x₁ y₁ θc = calcL' r θ₀ x₀ y₀ x₁ y₁ θc.
Proof.
  intros.
  specialize Ldir as Ldiro.
  specialize (tmne0 _ _ _ _ _ notO tmns) as notpx.
  specialize (rotated_straight_path_equiv _ _ _ _ _ notO tmns) as notpxs.
    
  destruct (Req_dec r 0).
  + unfold calcL, calcL', Hxarc, Hyarc.
    rewrite H, Ropp_0.
    autorewrite with null in *.
    destruct Ldiro as [k at2].
    assert (y₁ - Hyarc r θ₀ y₀ (r * θc) = y₁ - y₀) as ydg. {
      unfold Hyarc.
      rewrite H, Ropp_0, Rmult_0_l, Rplus_0_l, Rmult_0_l, Rplus_0_l.
      reflexivity. }
    assert (x₁ - Hxarc r θ₀ x₀ (r * θc) = x₁ - x₀) as xdg. {
      unfold Hxarc.
      rewrite H, Rmult_0_l, Rminus_0_l, Rmult_0_l, Ropp_0, Rplus_0_l.
      reflexivity. }
    rewrite xdg, ydg in at2.
    unfold atan2 in at2.
    destruct (pre_atan2 (y₁ - y₀) (x₁ - x₀)) as [a [arng [xd yd]]].
    rewrite at2 in xd, yd.
    rewrite sin_period1 in xd.
    rewrite cos_period1 in yd.
    destruct (Req_EM_T 0 (cos (θ₀ + θc))).
    ++ symmetry in e.
       apply coseq0_sinneq0 in e.
       apply (Rmult_eq_reg_r (sin (θ₀ + θc))); try assumption.
       setl (y₁ - y₀); try assumption.
    ++ apply (Rmult_eq_reg_r (cos (θ₀ + θc))); try auto.
       setl (x₁ - x₀); try auto.

  + assert (~ (x₁ - Hxarc r θ₀ x₀ (r * θc) = 0 /\ y₁ - Hyarc r θ₀ y₀ (r * θc) = 0) \/
            (x₁ - Hxarc r θ₀ x₀ (r * θc) = 0 /\ y₁ - Hyarc r θ₀ y₀ (r * θc) = 0))
    as [noc | oc]. {
    destruct (Req_dec (x₁ - Hxarc r θ₀ x₀ (r * θc)) 0) as [xe|xn].
    destruct (Req_dec (y₁ - Hyarc r θ₀ y₀ (r * θc)) 0) as [ye|yn];
      [right; split; assumption|].
    left; intros [z1 z2]. clear - yn z2. lra.
    left; intros [z1 z2]. clear - xn z1. lra. }
    ++ apply xlate_rot_arm in Ldir; try assumption.
       unfold θmax in *. clear θmax.
       rewrite calc_angle_std in *.
       unfold r in *. clear r.
       rewrite rxlate in *.
       set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
       set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
       set (θmax := calcθ₁ 0 0 0 x y) in *.
       set (r := ((x * sin θc - y * cos θc) / (1 - cos θc))) in *.
       rewrite calcL'_inv.
       rewrite calcL_inv; [|apply Ldiro].
       apply (ottb_parameters_L_calc_s x y θc notpxs tcrng Ldir).
    ++ inversion oc as [xoc yoc]. unfold calcL, calcL'.
       rewrite xoc, yoc.
       destruct (Req_EM_T 0 (cos (θ₀ + θc))).
       +++ symmetry in e.
           apply coseq0_sinneq0 in e.
           apply (Rmult_eq_reg_r (sin (θ₀ + θc))); try assumption.
           setl 0; try assumption.
           autorewrite with null in *.
           reflexivity.
       +++ apply (Rmult_eq_reg_r (cos (θ₀ + θc))); try auto.
           setl 0; try auto.
           autorewrite with null in *.
           reflexivity.
Qed.

(* calcL is non-negative. *)
Lemma ottb_parameters_compat_0leL :
  forall (x₀ y₀ θ₀ x₁ y₁ θc : R)
         (notO : ~ ((x₁-x₀) = 0 /\ (y₁-y₀) = 0)),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmns : θmax <> 0)
           (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI)) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      (* choose radius where angle is tangent*)
      let r := ((x₁ - x₀) * sin (θ₀ + θc) - (y₁ - y₀) * cos (θ₀ + θc))
                 / ( 1 - cos θc) in
      (* ensure correct direction of linear path *)
      forall (Ldir : exists k, atan2 (y₁ - Hyarc r θ₀ y₀ (r * θc))
                                     (x₁ - Hxarc r θ₀ x₀ (r * θc)) =
                               (θ₀ + θc) + 2* IZR k * PI),
        0 <= calcL r θ₀ x₀ y₀ x₁ y₁ θc.
Proof.
  intros.
  specialize (ottb_parameters_L_calc _ _ _ _ _ _ notO tmns tcrng Ldir) as
      calcLdef.
  set (Ldy := y₁ - Hyarc r θ₀ y₀ (r * θc)).
  set (Ldx := x₁ - Hxarc r θ₀ x₀ (r * θc)).
  set (L := sqrt (Ldy² + Ldx²)).
  change (calcL r θ₀ x₀ y₀ x₁ y₁ θc = L) in calcLdef.
  rewrite calcLdef.
  apply sqrt_pos.
Qed.

(* calcL is non-negative. *)
Lemma ottb_parameters_compat_0leL_s :
  forall (x₁ y₁ θc : R)
         (notpx : ~ (0<=x₁ /\ y₁=0)),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI)) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      (* choose radius where angle is tangent*)
      let r := (x₁ * sin θc - y₁ * cos θc) /
                       (1 - cos θc) in
      (* ensure correct direction of linear path *)
      forall (Ldir : exists k, atan2 (y₁ - Hyarc r 0 0 (r * θc))
                                     (x₁ - Hxarc r 0 0 (r * θc)) =
                               θc + 2* IZR k * PI),
        0 <= calcL r 0 0 0 x₁ y₁ θc.
Proof.
  intros.
  specialize (ottb_parameters_L_calc_s _ _ _ notpx tcrng Ldir) as
      calcLdef.
  set (Ldy := y₁ - Hyarc r 0 0 (r * θc)).
  set (Ldx := x₁ - Hxarc r 0 0 (r * θc)).
  set (L := sqrt (Ldy² + Ldx²)).
  change (calcL r 0 0 0 x₁ y₁ θc = L) in calcLdef.
  rewrite calcLdef.
  apply sqrt_pos.
Qed.

(* calcL is positive if we are on the straight part of the path *)
Lemma ottb_parameters_compat_L :
  forall (x₀ y₀ x₁ y₁ θ₀ θc : R),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmns : θmax <> 0)
           (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI)) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      let r := ((x₁ - x₀) * sin (θ₀ + θc) - (y₁ - y₀) * cos (θ₀ + θc))
                 / ( 1 - cos θc) in
      let Ldx := x₁ - Hxarc r θ₀ x₀ (r * θc) in
      let Ldy := y₁ - Hyarc r θ₀ y₀ (r * θc) in
      forall (Ldir : exists k : Z, atan2 Ldy Ldx = θ₀ + θc + 2 * IZR k * PI)
             (phase : straight r θ₀ x₀ y₀ x₁ y₁),
      0 < calcL r θ₀ x₀ y₀ x₁ y₁ θc.
Proof.
  intros.
  specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as notid.
  specialize (ottb_parameters_L_calc _ _ _ _ _ _ notid tmns tcrng Ldir) as
      calcLdef.
  set (L := sqrt (Ldy² + Ldx²)).
  change (calcL r θ₀ x₀ y₀ x₁ y₁ θc = L) in calcLdef.
  rewrite calcLdef. clear calcLdef.
  assert (0 <= L) as zleL.
  apply sqrt_pos.
  inversion_clear zleL as [zltL | zeqL]. assumption.

  exfalso.
  assert (0 <= (Ldy² + Ldx²)) as zlesum.
  apply Rplus_le_le_0_compat.
  apply Rle_0_sqr.
  apply Rle_0_sqr.
  symmetry in zeqL.
  generalize (sqrt_eq_0 _ zlesum zeqL) as sumeq0. intro.
  generalize (Rplus_sqr_eq_0_l _ _ sumeq0) as Ldyeq0. intro.
  rewrite Rplus_comm in sumeq0.
  generalize (Rplus_sqr_eq_0_l _ _ sumeq0) as Ldxeq0. intro.

  clear zeqL zlesum sumeq0.

  
  unfold straight, Tcx, Tcy in phase.

  unfold Ldy, Hyarc in Ldyeq0.
  assert ((y₁ - (y₀ + r * cos θ₀)) = - r * cos (r * θc / r + θ₀)) as yleg.
  apply (Rplus_eq_reg_l (r * cos (r * θc / r + θ₀))). setr 0.
  rewrite <- Ldyeq0. field.

  unfold Ldx, Hxarc in Ldxeq0.
  assert ((x₁ - (x₀ - r * sin θ₀)) = r * sin (r * θc / r + θ₀)) as xleg.
  apply (Rplus_eq_reg_l (- r * sin (r * θc / r + θ₀))). setr 0.
  rewrite <- Ldxeq0. field.
  rewrite cos_sin in yleg.
  rewrite sin_cos in xleg.
  rewrite yleg in phase.
  assert ((x₀ - r * - cos (PI / 2 + θ₀)) =
          (x₀ + r * cos (PI / 2 + θ₀))) as negneg. field.
  rewrite negneg in xleg. clear negneg.
  rewrite xleg in phase.
  assert ((r * sin (r * θc / r + θ₀))² + (- r * cos (r * θc / r + θ₀))² =
          r² * ((sin (r * θc / r + θ₀))² + (cos (r * θc / r + θ₀))²))
    as ident. unfold Rsqr. field. rewrite ident in phase.
  rewrite sin2_cos2 in phase.
  lra.
Qed.

Lemma Harc_arg_dir : forall (r θ₀ θc : R)
                           (rcompat : 0 < r * θc),
    exists k, atan2 (Hyarc' r θ₀ (r * θc)) (Hxarc' r θ₀ (r * θc)) =
              θ₀ + θc + 2 * IZR k * PI.
Proof.
  intros.
  specialize PI_RGT_0 as PIgt0.
  assert (2*PI > 0) as tPIgt0. lra.
  specialize (inrange_mT2T2 (θ₀ + θc) _ tPIgt0) as [k [rnglb rngub]].

  assert (2 * PI / 2 = PI) as id1. field. rewrite id1 in rngub. clear id1.
  assert (- (2 * PI) / 2 = - PI) as id2. field. rewrite id2 in rnglb. clear id2.
  assert (IZR k * (2 * PI) = 2* IZR k * PI) as id3. field. rewrite id3 in rnglb, rngub. clear id3.
  set (ζ := θ₀ + θc + 2 * IZR k * PI) in *.

  set (py := (Hyarc' r θ₀ (r * θc))).
  set (px := (Hxarc' r θ₀ (r * θc))).
  unfold atan2.
  destruct (pre_atan2 py px) as [x [[xrnglb xrngub] [pydef pxdef]]].
  unfold py, px in pydef, pxdef.
  unfold Hyarc', Hxarc' in pydef, pxdef.

  assert (r * θc / r + θ₀ = θ₀ + θc) as id. field.
  intro. subst. lra.
  rewrite id in pydef, pxdef.
  rewrite sin2_cos2, sqrt_1, Rmult_1_l in pydef, pxdef. clear id.

  rewrite <- (sin_period1 _ k) in pydef. change (sin ζ = sin x) in pydef.
  rewrite <- (cos_period1 _ k) in pxdef. change (cos ζ = cos x) in pxdef.
  assert (sin (x - ζ) = 0) as sinxz0.
  setr (sin x * cos x - cos x * sin x).
  rewrite <- pxdef at 1.
  rewrite <- pydef at 2.
  rewrite sin_minus. field.

  assert (cos (x - ζ) = 1) as cosxz1.
  rewrite <- (sin2_cos2 x), Rplus_comm. unfold Rsqr.
  rewrite <- pxdef at 2.
  rewrite <- pydef at 2.
  rewrite cos_minus. field.
  
  assert (-2*PI < x - ζ) as lb. lra.
  assert (x - ζ <= 2*PI) as ub. lra.

  destruct (Rle_dec 0 (x - ζ)).
  specialize (sin_eq_O_2PI_0 _ r0 ub sinxz0) as vals.
  inversion_clear vals.
  exists k. change (x = ζ).
  apply (Rplus_eq_reg_r (-ζ)). setr 0. setl (x - ζ). assumption.

  inversion_clear H. exfalso.
  rewrite H0, cos_PI in cosxz1.
  lra.

  exists (k+1)%Z.
  rewrite plus_IZR.
  fieldrewrite (θ₀ + θc + 2 * (IZR k + 1) * PI)
               (θ₀ + θc + 2 * IZR k * PI + 2 * PI).
  change (x = ζ + 2 * PI).
  apply (Rplus_eq_reg_r (-ζ)). setr (2*PI). setl (x - ζ). assumption.

  apply Rnot_le_lt in n. clear ub.
  rewrite <- (sin_period1 _ 1%Z) in sinxz0.
  rewrite <- (cos_period1 _ 1%Z) in cosxz1.
  assert (0 < (x - ζ + 2 * 1 * PI)) as shflb. lra.
  assert ((x - ζ + 2 * 1 * PI) < 2*PI) as shfub. lra.
  assert (0 <= (x - ζ + 2 * 1 * PI)) as shflb1. left. assumption.
  assert ((x - ζ + 2 * 1 * PI) <= 2*PI) as shfub1. left. assumption.

  specialize (sin_eq_O_2PI_0 _ shflb1 shfub1 sinxz0) as vals.
  inversion_clear vals.
  rewrite H in shflb. lra.
  inversion_clear H.
  rewrite H0, cos_PI in cosxz1. lra.
  rewrite H0 in shfub. lra.
Qed.

Lemma sint2ne0 : 
  forall (x₀ y₀ x₁ y₁ θ₀ : R),
    let θ := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (st2ne0 : sin (θ/2) <> 0), (* x-axis disallowed for pure turns *)
           θ <> 0. (* + x-axis disallowed for ottb *)
Proof.
  intros.
  unfold θ in *. clear θ.
  unfold calcθ₁ in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  unfold atan2 in *.
  destruct (pre_atan2 y x) as [θ [trng [yd xd]]].
  intro tne0.
  apply st2ne0.
  fieldrewrite (2 * θ / 2) (θ).
  apply Rmult_integral in tne0.
  destruct tne0 as [ctd |teq0].
  exfalso. clear - ctd. lra.
  subst.
  apply sin_0.
Qed.

Lemma turn_params_consist:
  forall (x₀ y₀ x₁ y₁ θ₀ : R),
    let θ₁ := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    let r := sqrt ((y₁ - y₀)² + (x₁ - x₀)²) / (2*sin (θ₁/2)) in
    forall
      (sinnneg : sin (θ₁/2) <> 0)
      (zner : 0 <> r),
      (0 <= r * θ₁).
Proof.
  intros.

  unfold calcθ₁, atan2 in θ₁.
  destruct (pre_atan2 (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)
                      ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) as [x cond].
  inversion_clear cond as [xrange [sinx cosx]].

  (* proof for 0 <= rtheta1 *)
  clear sinx cosx.
  generalize (total_order_T 0 r) as xpossible.
  intros. inversion_clear xpossible as [[zltx | zeqx] | zgtx]; [|contradiction|].

  (* 0<r*)
  unfold r in zltx.
  assert ( sqrt ((y₁ - y₀)² + (x₁ - x₀)²) / (2 * sin (θ₁ / 2)) =
           sqrt ((y₁ - y₀)² + (x₁ - x₀)²) * / (2 * sin (θ₁ / 2))) as mltid. field. assumption.
  rewrite mltid in zltx. clear mltid.

  generalize (zlt_mult _ _ zltx (sqrt_pos _)) as zltinvden; intro.
  apply Rinv_0_lt_compat in zltinvden.
  rewrite Rinv_involutive in zltinvden.
  assert ( 0 = 2 * 0) as zeqz. field. rewrite zeqz in zltinvden. clear zeqz.
  apply Rmult_lt_reg_l in zltinvden.
  unfold θ₁ in zltinvden.
  assert (2 * x / 2 = x) as xdef. field. rewrite xdef in zltinvden. clear xdef.

  assert (sqrt ((y₁ - y₀)² + (x₁ - x₀)²) * / (2 * sin (θ₁ / 2)) =
          sqrt ((y₁ - y₀)² + (x₁ - x₀)²) / (2 * sin (θ₁ / 2))) as und.
  field. assumption. rewrite und in zltx. clear und.
  change (0 < r) in zltx.
  destruct (Rle_dec 0 x).
  unfold θ₁. 
  apply Rmult_le_pos. left. assumption.
  lra.

  exfalso.
  assert (sin x < 0) as sinxlt0.
  rewrite <- (sin_period x 1).
  unfold INR.
  set (q := (x + 2 * 1 * PI)).
  assert (PI < q < 2 * PI) as qrng.
  split. unfold q.
  inversion xrange as [nPIltx xlePI].
  lra.
  unfold q.
  apply Rnot_le_lt in n.
  lra.
  inversion_clear qrng.
  eapply sin_lt_0; eauto.
  lra. lra.
  intro.
  apply sinnneg.
  apply (Rmult_eq_reg_l 2). setr 0. assumption.
  discrR.

  (* 0>r*)
  unfold r in zgtx.
  assert ( sqrt ((y₁ - y₀)² + (x₁ - x₀)²) / (2 * sin (θ₁ / 2)) =
           sqrt ((y₁ - y₀)² + (x₁ - x₀)²) * / (2 * sin (θ₁ / 2))) as mltid. field. assumption.
  rewrite mltid in zgtx. clear mltid.

  generalize (zgt_mult _ _ zgtx (sqrt_pos _)) as zltinvden; intro.
  apply Rinv_lt_0_compat in zltinvden.
  rewrite Rinv_involutive in zltinvden.
  assert ( 0 = 2 * 0) as zeqz. field. rewrite zeqz in zltinvden. clear zeqz.
  apply Rmult_lt_reg_l in zltinvden.
  unfold θ₁ in zltinvden.
  assert (2 * x / 2 = x) as xdef. field. rewrite xdef in zltinvden. clear xdef.

  assert (sqrt ((y₁ - y₀)² + (x₁ - x₀)²) * / (2 * sin (θ₁ / 2)) =
          sqrt ((y₁ - y₀)² + (x₁ - x₀)²) / (2 * sin (θ₁ / 2))) as und.
  field. assumption.
  rewrite und in zgtx. clear und.
  change (0 > r) in zgtx.
  destruct (Rle_dec 0 x).

  exfalso.
  assert (0 <= sin x ) as sinxge0.
  apply sin_ge_0. assumption.
  inversion xrange. assumption.
  lra. 

  unfold θ₁.
  apply Rnot_le_lt in n.
  generalize (Ropp_0_gt_lt_contravar _ n) as zltmx; intro.
  generalize (Ropp_0_gt_lt_contravar _ zgtx) as zltmr; intro.
  setr ((-r)*2*(-x)).
  apply Rmult_le_pos; [| left; assumption].
  apply Rmult_le_pos; [left; assumption |].
  lra. lra.
  intro.

  apply sinnneg.
  apply (Rmult_eq_reg_l 2). setr 0. assumption.
  discrR.
Qed.

Lemma turnpath_parameters_range :
  forall (x₀ y₀ x₁ y₁ θ₀: R),
    let θ₁ := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    let r := sqrt((y₁ - y₀)² + (x₁ - x₀)²) / (2 * sin (θ₁ / 2)) in
    forall
      (sinnneg : sin (θ₁ / 2) <> 0)
      (zner : 0 <> r),
      (r * θ₁ < 2 * Rabs r * PI).
Proof.
  intros.
  unfold calcθ₁, atan2 in θ₁.
  destruct (pre_atan2 (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)
                      ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) as [x cond].
  inversion_clear cond as [xrange [sinx cosx]].

  clear sinx cosx.
  unfold θ₁.
  destruct (Rle_dec 0 r).
  inversion_clear r0; [| contradiction].
  rewrite Rabs_pos_eq.
  inversion_clear xrange.
  inversion_clear H1.
  setl (2*r*x).
  apply (Rmult_lt_compat_l (2*r)).
  lra. assumption.
  exfalso.
  subst.
  apply sinnneg.
  unfold θ₁.
  fieldrewrite (2*PI/2) PI.
  apply sin_PI.
  left. assumption.

  apply Rnot_le_lt in n.
  rewrite Rabs_left.
  setl (2 * (-r) * (-x)).
  inversion_clear xrange.
  inversion_clear H0.
  apply (Rmult_lt_compat_l (2*(-r))).
  apply Rmult_lt_0_compat. lra. lra.
  lra.

  exfalso.
  subst.
  apply sinnneg.
  unfold θ₁.
  fieldrewrite (2 * PI/ 2) PI.
  apply sin_PI. assumption.
Qed.

Lemma turnpath_parameters_on_arc :
  forall (x₀ y₀ x₁ y₁ θ₀ : R),
    let θ₁ := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
     let r := sqrt((y₁ - y₀)²+(x₁ - x₀)²)/(2*sin (θ₁/2)) in
     forall
       (sinnneg : sin (θ₁/2) <> 0)
       (zner : 0 <> r),
       (x₁ = Hxarc r θ₀ x₀ (r*θ₁)) /\ (y₁ = Hyarc r θ₀ y₀ (r*θ₁)).
Proof.
  intros.
  unfold calcθ₁, atan2 in θ₁.
  destruct (pre_atan2 (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)
                      ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) as [x cond].
  inversion_clear cond as [xrange [sinx cosx]].

  assert ((- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)² + ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)² =
           (x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²)
           + (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²)) as id1.
  unfold Rsqr. field.
  rewrite id1 in cosx. clear id1.
  repeat rewrite sin2_cos2 in cosx.

  assert ((- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)² + ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)² =
          ( (x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²)
            + (y₁ - y₀)² * ((sin θ₀)²+ (cos θ₀)²))) as id2.
  unfold Rsqr. field. rewrite id2 in sinx. clear id2.
  repeat rewrite sin2_cos2 in sinx.
  
  assert ((x₁ - x₀)² * 1 + (y₁ - y₀)² * 1 =
          (x₁ - x₀)²+ (y₁ - y₀)²) as id3. field. rewrite id3 in sinx,cosx. clear id3.

  (************)
  assert (r * 2 * sin (x) = sqrt ( (x₁ - x₀)² + (y₁ - y₀)²)) as sqrt2r.
  unfold r,θ₁.
  fieldrewrite (2 * x / 2) x.
  setl (sqrt ((y₁ - y₀)² + (x₁ - x₀)²)).
  unfold θ₁ in sinnneg.
  assert ((2 * x / 2) = x) as x2x. field. rewrite x2x in sinnneg.
  assumption.
  rewrite Rplus_comm.
  reflexivity.
  rewrite <- sqrt2r in sinx, cosx. clear sqrt2r.

  rewrite Rmult_assoc in cosx.
  rewrite Rmult_assoc in cosx.
  rewrite <- (Rmult_assoc 2 (sin x)) in cosx.
  rewrite <- sin_2a in cosx.
  change ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ = r * sin θ₁) in cosx.

  rewrite Rmult_assoc in sinx.
  rewrite Rmult_assoc in sinx.
  rewrite <- (Rmult_assoc 2 (sin x)) in sinx.
  
  assert (2*sin x *sin x = 1 - cos (2*x)) as sinx2.
  rewrite cos_2a_sin. field.
  rewrite sinx2 in sinx. clear sinx2.
  change (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ = r * (1 - cos θ₁)) in sinx.

  split.
  unfold Hxarc.
  fieldrewrite (r * θ₁ / r + θ₀) (θ₁ + θ₀). auto.
  apply (Rplus_eq_reg_r (-x₀)). setl ((x₁ - x₀)*1 + (y₁ - y₀)*0).
  setr (r * (sin (θ₁ + θ₀) -  sin θ₀)).
  rewrite <- (sin2_cos2 θ₀). unfold Rsqr.
  rewrite <- sin_0.
  fieldrewrite 0 (θ₀ - θ₀).
  rewrite (sin_minus θ₀ θ₀).

  rewrite sin_plus.
  fieldrewrite (r * (sin θ₁ * cos θ₀ + cos θ₁ * sin θ₀ - sin θ₀))
               ((r * sin θ₁) * cos θ₀ - (r * (1 - cos θ₁)) * sin θ₀).

  rewrite <- sinx, <- cosx. field.

  unfold Hyarc.
  fieldrewrite (r * θ₁ / r + θ₀) (θ₁ + θ₀). auto.
  apply (Rplus_eq_reg_r (-y₀)). setl ((y₁ - y₀)*1 + (x₁ - x₀)*0).
  setr (r * (- cos (θ₁ + θ₀) +  cos θ₀)).
  rewrite <- (sin2_cos2 θ₀). unfold Rsqr.
  rewrite <- sin_0.
  fieldrewrite 0 (θ₀ - θ₀).
  rewrite (sin_minus θ₀ θ₀).

  rewrite cos_plus.
  fieldrewrite (r * (- (cos θ₁ * cos θ₀ - sin θ₁ * sin θ₀) + cos θ₀))
               ((r * (1 - cos θ₁) * cos θ₀ + r * sin θ₁ * sin θ₀)).

  rewrite <- sinx, <- cosx. field.

Qed.

Lemma turnpath_parameters_turning :
  forall (x₀ y₀ x₁ y₁ θ₀ : R),
    let θ₁ := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
     let r := sqrt((y₁ - y₀)²+(x₁ - x₀)²)/(2*sin (θ₁/2)) in
     forall
       (sinnneg : sin (θ₁/2) <> 0)
       (zner : 0 <> r),
       turning r θ₀ x₀ y₀ x₁ y₁.
Proof.
  intros.
  generalize (turnpath_parameters_on_arc x₀ y₀ x₁ y₁ θ₀ sinnneg zner) as xydef; intro.
  inversion_clear xydef as [xdef ydef].
  change (x₁ = Hxarc r θ₀ x₀ (r*θ₁)) in xdef.
  change (y₁ = Hyarc r θ₀ y₀ (r*θ₁)) in ydef.
  rewrite xdef, ydef.
  unfold turning, Tcy, Tcx, Hyarc, Hxarc.
  fieldrewrite (r * θ₁ / r + θ₀) (θ₁ + θ₀). auto.
  rewrite <- (cos_sin θ₀).
  fieldrewrite (r * sin (θ₁ + θ₀) - r * sin θ₀ + x₀ - (x₀ + r * cos (PI / 2 + θ₀)))
               (r * sin (θ₁ + θ₀) - r * sin θ₀ + x₀ - x₀ + r * - cos (PI / 2 + θ₀)).
  rewrite <- (sin_cos θ₀).
  assert ((r * sin (θ₁ + θ₀) - r * sin θ₀ + x₀ - x₀ + r * sin θ₀)² +
          (- r * cos (θ₁ + θ₀) + r * cos θ₀ + y₀ - (y₀ + r * cos θ₀))² =
          r² * ((sin (θ₁ + θ₀))² + (cos (θ₁ + θ₀))²)).
  unfold Rsqr. field. rewrite H.
  rewrite sin2_cos2. field.
Qed.

Lemma thetac_rsgn_bnds : forall (x₁ y₁ θc : R),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (ntX : ~ (y₁=0))
           (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                 - 2*PI < θc < θmax/2 - 2*PI )) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      let r := (x₁ * sin θc - y₁ * cos θc) /
                       (1 - cos θc) in
      (0 < r /\ 0 < θc < 2 * PI) \/ (r < 0 /\ - 2 * PI < θc < 0).
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.

  assert (~ (0<=x₁ /\ y₁=0)) as nX. {
    intros [zleqx1 y1ne0].
    apply ntX. assumption. }
  
  specialize (ottb_r_thetac_lb_s _ _ _ nX tcrng) as rcompat.
  change (0 < r * θc)in rcompat.

  destruct tcrng as [tmgt0tc tmlt0tc].

  assert (r <> 0) as rne0. {
    intro req0. rewrite req0 in rcompat. lra. }


  specialize (calcth1_atan2_s x₁ y₁) as tmd.
  change (θmax = 2 * atan2 y₁ x₁) in tmd.

  destruct (total_order_T 0 r) as [zler | zgtr].
  + destruct zler as [zltr | zeqr]; [|exfalso; apply rne0; auto].
    destruct (total_order_T 0 y₁) as [zley1 |zgty1].
    ++ destruct zley1 as [zlty1 |zeqy1].
       +++ left.
           split; [assumption|].

           assert (0 < θmax) as zlttm. {
             rewrite tmd.
             apply Rmult_lt_0_compat; [lra|].
             destruct (total_order_T 0 x₁) as [zlex1 | zgtx1].
             ++++ destruct zlex1 as [zltx1 |zeqx1].
                 +++++ specialize (atan2Q1 _ _ zltx1 zlty1) as [at2lb at2ub].
                      assumption.
                 +++++ rewrite <- zeqx1.
                      rewrite atan2_PI2; try assumption.
                      lra.
             ++++ apply Rgt_lt in zgtx1.
             specialize (atan2Q2 _ _ zgtx1 zlty1) as [at2lb at2ub].
             lra. }

           assert (θmax <= 2 * PI) as tmlt2PI. {
             assert (~ (x₁ = 0 /\ y₁ = 0)) as nO. {
               intros [xo yo].
               apply nX.
               split; [right; symmetry; assumption|assumption]. }
             specialize (atan2_bound _ _ nO) as [atlb atub].
             rewrite tmd.
             destruct atub as [atltPI |ateqPI]; lra. }
       
           specialize (tmgt0tc zlttm) as [[tcgl tcgu] | [tcll tclu]]; clear tmlt0tc.
           ++++ split; lra.
           ++++ exfalso.
                assert (0 < θc) as zlttc. {
                  apply zlt_mult in rcompat; [ assumption| left; assumption]. }
                lra.

       +++ left.
           split; [assumption|].

           assert (0 < θmax) as zlttm. {
             rewrite tmd.
             apply Rmult_lt_0_compat; [lra|].
             destruct (total_order_T 0 x₁) as [zlex1 | zgtx1].
             ++++ destruct zlex1 as [zltx1 |zeqx1].
                  +++++ exfalso. apply nX.
                  split; [left; assumption|symmetry; assumption].
                  +++++ exfalso. apply nX.
                  split; [right|symmetry]; assumption.
             ++++ apply Rgt_lt in zgtx1.
                  rewrite <- zeqy1.
                  rewrite (atan2_PI _ zgtx1).
                  lra. }

           assert (θmax <= 2 * PI) as tmlt2PI. {
             assert (~ (x₁ = 0 /\ y₁ = 0)) as nO. {
               intros [xo yo].
               apply nX.
               split; [right; symmetry; assumption|assumption]. }
             specialize (atan2_bound _ _ nO) as [atlb atub].
             rewrite tmd.
             destruct atub as [atltPI |ateqPI]; lra. }
       
           specialize (tmgt0tc zlttm) as [[tcgl tcgu] | [tcll tclu]]; clear tmlt0tc.
           ++++ split; lra.
           ++++ exfalso.
                assert (0 < θc) as zlttc. {
                  apply zlt_mult in rcompat; [ assumption| left; assumption]. }
                lra.
    ++ left.
       split; [assumption|].
       apply Rgt_lt in zgty1.
       
       assert (θmax < 0) as tmlt0. {
         rewrite tmd.
         apply (Rmult_lt_reg_r (/2));
           [apply pos_half_prf|].
         setr 0. setl (atan2 y₁ x₁).

         destruct (total_order_T 0 x₁) as [zlex1 | zgtx1].
         ++++ destruct zlex1 as [zltx1 |zeqx1].
              +++++ specialize (atan2Q4 _ _ zltx1 zgty1) as [at2lb at2ub].
              assumption.
              +++++ rewrite <- zeqx1.
              rewrite atan2_mPI2; try assumption.
              lra.
         ++++ apply Rgt_lt in zgtx1.
              specialize (atan2Q3 _ _ zgtx1 zgty1) as [at2lb at2ub].
              lra. }
       
       assert (- 2 * PI <= θmax) as tmlt2PI. {
         assert (~ (x₁ = 0 /\ y₁ = 0)) as nO. {
           intros [xo yo].
           apply nX.
           split; [right; symmetry; assumption|assumption]. }
         specialize (atan2_bound _ _ nO) as [atlb atub].
         rewrite tmd.
         destruct atub as [atltPI |ateqPI]; lra. }
       
       specialize (tmlt0tc tmlt0) as [[tcgl tcgu] | [tcll tclu]]; clear tmgt0tc.
       ++++ exfalso.
            assert (0 < θc) as zlttc. {
              apply zlt_mult in rcompat; [ assumption| left; assumption]. }
            lra.
       ++++ split; lra.

  + apply Rgt_lt in zgtr.
    destruct (total_order_T 0 y₁) as [zley1 |zgty1].
    ++ destruct zley1 as [zlty1 |zeqy1].
       +++ right.
           split; [assumption|].

           assert (0 < θmax) as zlttm. {
             rewrite tmd.
             apply Rmult_lt_0_compat; [lra|].
             destruct (total_order_T 0 x₁) as [zlex1 | zgtx1].
             ++++ destruct zlex1 as [zltx1 |zeqx1].
                 +++++ specialize (atan2Q1 _ _ zltx1 zlty1) as [at2lb at2ub].
                      assumption.
                 +++++ rewrite <- zeqx1.
                      rewrite atan2_PI2; try assumption.
                      lra.
             ++++ apply Rgt_lt in zgtx1.
             specialize (atan2Q2 _ _ zgtx1 zlty1) as [at2lb at2ub].
             lra. }

           assert (θmax <= 2 * PI) as tmlt2PI. {
             assert (~ (x₁ = 0 /\ y₁ = 0)) as nO. {
               intros [xo yo].
               apply nX.
               split; [right; symmetry; assumption|assumption]. }
             specialize (atan2_bound _ _ nO) as [atlb atub].
             rewrite tmd.
             destruct atub as [atltPI |ateqPI]; lra. }
       
           specialize (tmgt0tc zlttm) as [[tcgl tcgu] | [tcll tclu]];
                                                 clear tmlt0tc.
           ++++ exfalso.
                assert (θc < 0) as zlttc. {
                  rewrite <- Rmult_opp_opp in rcompat.
                  apply zlt_mult in rcompat; lra.  }
                lra.
           ++++ split; lra.

       +++ exfalso. apply ntX. symmetry. assumption.

    ++ right.
       apply Rgt_lt in zgty1.
       split; [assumption|].
       
       assert (θmax < 0) as tmlt0. {
         rewrite tmd.
         apply (Rmult_lt_reg_r (/2));
           [apply pos_half_prf|].
         setr 0. setl (atan2 y₁ x₁).

         destruct (total_order_T 0 x₁) as [zlex1 | zgtx1].
         ++++ destruct zlex1 as [zltx1 |zeqx1].
              +++++ specialize (atan2Q4 _ _ zltx1 zgty1) as [at2lb at2ub].
              assumption.
              +++++ rewrite <- zeqx1.
              rewrite atan2_mPI2; try assumption.
              lra.
         ++++ apply Rgt_lt in zgtx1.
              specialize (atan2Q3 _ _ zgtx1 zgty1) as [at2lb at2ub].
              lra. }
       
       assert (- 2 * PI <= θmax) as tmlt2PI. {
         assert (~ (x₁ = 0 /\ y₁ = 0)) as nO. {
           intros [xo yo].
           apply nX.
           split; [right; symmetry; assumption|assumption]. }
         specialize (atan2_bound _ _ nO) as [atlb atub].
         rewrite tmd.
         destruct atub as [atltPI |ateqPI]; lra. }
       
       specialize (tmlt0tc tmlt0) as [[tcgl tcgu] | [tcll tclu]];
                                               clear tmgt0tc.
       ++++ split; lra.
       ++++ exfalso.
            assert (θc < 0) as zlttc. {
              assert (r * θc = - r * - θc) as id. {
                field. }
              rewrite id in rcompat. clear id.
              apply zlt_mult in rcompat; lra. }
            lra.
Qed.

Lemma straight_path_exists_s : forall (x₁ y₁ θc : R),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (nX : ~ (0<=x₁ /\ y₁=0))
           (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                  - 2*PI < θc < θmax/2 - 2*PI )) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      let r := (x₁ * sin θc - y₁ * cos θc) /
                       (1 - cos θc) in
      let Ldx := x₁ - Hxarc r 0 0 (r * θc) in
      let Ldy := y₁ - Hyarc r 0 0 (r * θc) in
      forall (phase : straight r 0 0 0 x₁ y₁)
             (sac : ~ (r<0 /\ x₁<0 /\ y₁=0)),
      exists k : Z, atan2 Ldy Ldx = θc + 2 * IZR k * PI.
Proof.
  intros.


  specialize (calcth1_atan2_s x₁ y₁) as tmd.
  change (θmax = 2 * atan2 y₁ x₁) in tmd.

  assert ((- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0) = y₁) as y1.
  rewrite sin_0, cos_0. field. 
  assert (((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0) = x₁) as x1.
  rewrite sin_0, cos_0. field. 

  assert (θmax <> 0) as tmaxne0. {
    intro tmeq0.
    unfold θmax,calcθ₁ in tmeq0.
    rewrite x1,y1 in tmeq0.
    rewrite <- (Rmult_0_r 2) in tmeq0.
    apply Rmult_eq_reg_l in tmeq0; [|discrR].
    apply atan2_0_impl in tmeq0 as [zltx1 y1eq0];
      [|intros [x0 y0]; apply nX; subst; split; [right |]; reflexivity].
    apply nX.
    split; [left|]; assumption. }

  (* same proof strategy as before, just copy and paste here *)
  assert (0 < 1 - cos θc) as zltomcostc. {
    unfold calcθ₁, atan2 in θmax.
    destruct (pre_atan2 (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0)
                        ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0))
    as [θmax2 [xrng atanprop]].
    rewrite x1,y1 in atanprop. clear x1 y1.
    inversion_clear xrng as [θmax2lb θmax2ub].
    generalize (COS_bound θc) as COS_bound; intro.
    inversion_clear COS_bound as [coslb cosub].
    inversion_clear cosub. lra.

    exfalso.
    destruct (Rle_dec 0 θmax) as [[tmgt0 |tmeq0]| tmlt0];
      unfold θmax in *.
    - destruct tcrng as [θcrng θcnrng].
      clear θcnrng.
      specialize (θcrng tmgt0).
      destruct θcrng as [tcp| tcn].
      -- destruct tcp as [θcrnglb θcrngub].
         assert (0 < θc) as tclb.
         assert (2 * θmax2 / 2 = θmax2) as id;
           [field | rewrite id in θcrnglb; clear id].
         lra.
         assert (θc < 2*PI) as tcub. lra.
         assert (0 <= θc < 2*PI) as thcrng;
           [split; [left; assumption| assumption]|].
         specialize (cosθeq1 _ thcrng H) as tceq0.
         rewrite tceq0 in tclb. lra.
      -- destruct tcn as [θcrnglb θcrngub].
         assert (0 < - θc) as tclb.
         rewrite <- Ropp_0.
         apply Ropp_lt_contravar.
         assert (2 * θmax2 / 2 = θmax2) as id;
           [field | rewrite id in θcrngub; clear id].
         lra.
         assert (- θc < 2*PI) as tcub. lra.
         assert (0 <= - θc < 2*PI) as thcrng;
           [split; [left; assumption| assumption]|].
         rewrite <- cos_neg in H.
         specialize (cosθeq1 _ thcrng H) as tceq0.
         rewrite tceq0 in tclb. lra.
    - apply tmaxne0. auto.
    - apply Rnot_le_lt in tmlt0.
      destruct tcrng as [θcrng θcnrng].
      clear θcrng.
      specialize (θcnrng tmlt0).
      destruct θcnrng as [tcp| tcn].
      -- destruct tcp as [θcrnglb θcrngub].
         assert (0 < - θc) as tclb.
         assert (2 * θmax2 / 2 = θmax2) as id;
           [field | rewrite id in θcrngub; clear id].
         lra.
         assert (- θc < 2*PI) as tcub. lra.
         assert (0 <= - θc < 2*PI) as thcrng;
           [split; [left; assumption| assumption]|].
         rewrite <- cos_neg in H.
         specialize (cosθeq1 _ thcrng H) as tceq0.
         rewrite tceq0 in tclb. lra.
      -- destruct tcn as [θcrnglb θcrngub].
         assert (0 < θc) as tclb.
         assert (2 * θmax2 / 2 = θmax2) as id;
           [field | rewrite id in θcrnglb; clear id].
         lra.
         assert (θc < 2*PI) as tcub. lra.
         assert (0 <= θc < 2*PI) as thcrng;
           [split; [left; assumption| assumption]|].
         specialize (cosθeq1 _ thcrng H) as tceq0.
         rewrite tceq0 in tclb. lra. }

  specialize (ottb_r_thetac_lb_s _ _ _ nX tcrng) as rcompat.
  change (0 < r * θc)in rcompat.

  assert (r <> 0) as rne0. intro req0. rewrite req0 in rcompat. lra.

  assert (Hxarc r 0 0 (r*θc) = r * sin θc) as Hxarcdef. {
    unfold Hxarc. rewrite sin_0.
    fieldrewrite (r * θc / r + 0) (θc). assumption. field. }

  assert (Hyarc r 0 0 (r*θc) = r * (1-cos θc)) as Hyarcdef. {
    unfold Hyarc. rewrite cos_0.
    fieldrewrite (r * θc / r + 0) (θc). assumption. field. }
  
  assert (Ldy * cos θc = Ldx * sin θc) as rcq. {
    unfold Ldy, Ldx. rewrite Hxarcdef, Hyarcdef.
    setl (y₁ * cos θc + r * (cos θc * cos θc) - r *cos θc).
    setr (x₁ * sin θc - r * (sin θc * sin θc)).
    
    change (y₁ * cos (θc) + r * (cos (θc))² -
                            r * cos (θc) =
            x₁ * sin θc - r * (sin θc)²).
    apply (Rplus_eq_reg_l (r * (sin θc)² +
                           r * cos θc -
                           y₁ * cos θc)).
    setl (r * ((sin θc)²+ (cos θc)²)).
    setr (r * (cos θc) + x₁ * sin θc - y₁ * cos θc).
    rewrite sin2_cos2.
    apply (Rplus_eq_reg_r (- r * cos θc)).
    setr (x₁ * sin θc - y₁ * cos θc).
    unfold r.
    setl (x₁ * sin θc - y₁ * cos θc).
    intro omcostceq0. rewrite omcostceq0 in zltomcostc. lra.
    reflexivity. }
  
  specialize PI_RGT_0 as PI_RGT_0.
  assert (2*PI > 0) as twoPIgt0; [lra|].

  assert (~ (x₁ = 0 /\ y₁ = 0)) as notid. {
    intros [x10 y10].
    apply nX.
    split; [right|]; auto. }

  (* straight path after turn arc *)
  generalize phase; intro phasec.
  unfold straight, Tcx, Tcy in phase.
  apply (Rplus_lt_compat_r (-r²)) in phase.
  assert ((PI / 2 + 0) = PI / 2) as id. field. rewrite id in phase.
  rewrite cos_PI2, sin_PI2 in phase. clear id.
  autorewrite with null in phase.
  rewrite Rsqr_minus in phase.
  assert (x₁² + (y₁² + r² - 2 * y₁ * r) + - r²
          = x₁² + y₁² - 2 * y₁ * r) as id. field.
  rewrite id in phase. clear id.
  apply Rminus_gt_0_lt in phase.
  
  assert (~ (Ldy = 0 /\ Ldx = 0)) as LdxLdyne01. {
    unfold Ldx, Ldy.
    rewrite Hxarcdef, Hyarcdef.
    intros [yn0 xn0].
    apply Rminus_diag_uniq in yn0.
    apply Rminus_diag_uniq in xn0.
    rewrite xn0,yn0 in phase.
    clear - phase rne0 zltomcostc.
    assert (1 < 1) as ctd; [|lra]. {
      apply (Rmult_lt_reg_r (2* (r² * (1 - cos θc))));
        [apply Rmult_lt_0_compat;
         [lra|
          apply Rmult_lt_0_compat;
          [specialize (Rle_0_sqr r) as zler2;
           destruct zler2 as [zltr2|zeqr2];
           [assumption|
            exfalso; symmetry in zeqr2;
            apply Rsqr_eq_0 in zeqr2;
            apply rne0; assumption]|assumption]
         ]|].

      setr (r² * (1 + 1 - 2 * cos θc)).
      rewrite <- (sin2_cos2 θc) at 3.
      setr ((r * sin θc)² + (r * (1 - cos θc))²).
      setl (2 * (r * (1 - cos θc)) * r).
      assumption.
    }
  }

  assert (Ldy <> 0 \/ Ldx <> 0) as LdxLdyne0. {
    clear - LdxLdyne01.
    destruct (Req_dec Ldx 0).
    destruct (Req_dec Ldy 0).
    exfalso. apply LdxLdyne01. split; assumption.
    left; assumption.
    right; assumption. }

  unfold atan2.
  destruct (pre_atan2 Ldy Ldx) as [φ [xrng [Ldydef Ldxdef]]].
  inversion xrng as [xrnglb xrngub].

  specialize (atan2_val Ldy Ldx φ xrng LdxLdyne0 Ldydef Ldxdef) as xfun.
  unfold Ldx, Ldy in xfun.
  rewrite Hyarcdef, Hxarcdef in xfun.
  change (κ₂ x₁ y₁ r θc = φ) in xfun.

  assert (0 < sqrt (Ldy² + Ldx²)) as zltsqrttrm. {
    specialize (sqrt_pos (Ldy² + Ldx²)) as zleL.
    destruct zleL as [ |zeqsqrttrm];
      [ assumption|
        exfalso;
        rewrite <- sqrt_0 in zeqsqrttrm;
        specialize (Rle_0_sqr Ldy) as Ldyge0;
        specialize (Rle_0_sqr Ldx) as Ldxge0;
        apply sqrt_inj in zeqsqrttrm;
        [ |right; reflexivity
          | apply Rplus_le_le_0_compat; assumption];
        destruct Ldyge0 as [Ldygt0 |Ldyeq0]; 
        [specialize (Rplus_lt_le_0_compat _ _ Ldygt0 Ldxge0) as ctrd;
         rewrite <- zeqsqrttrm in ctrd;
         clear - ctrd; lra|];
        rewrite <- Ldyeq0, Rplus_0_l in zeqsqrttrm;
        symmetry in zeqsqrttrm, Ldyeq0;
        apply Rsqr_eq_0 in zeqsqrttrm;
        apply Rsqr_eq_0 in Ldyeq0;
        apply LdxLdyne01;
        split; assumption]. }
  
  assert (sin (φ - θc) = 0) as sinetc0. {
    rewrite sin_minus.
    apply (Rplus_eq_reg_l (cos φ * sin θc)).
    apply (Rmult_eq_reg_l (sqrt (Ldy² + Ldx²))).
    setl ((sqrt (Ldy² + Ldx²) * sin φ) * cos θc).
    setr ((sqrt (Ldy² + Ldx²) * cos φ) * sin θc).
    rewrite <- Ldxdef, <- Ldydef.
    assumption. intro. clear - H zltsqrttrm. lra. }

  specialize (inrange_0T (φ - θc) _ twoPIgt0) as [k [xzrnglb xzrngub]].
  rewrite Rmult_comm, Rmult_assoc, (Rmult_comm PI (IZR k)),
          <- Rmult_assoc in xzrnglb, xzrngub.
  rewrite <- (sin_period1 (φ - θc) k) in sinetc0.

  assert (φ - θc + 2 * IZR k * PI <= 2 * PI) as argle2PI. {
    left. assumption. }

  specialize (sin_eq_O_2PI_0 _  xzrnglb argle2PI sinetc0)
    as [eq0| [eqPI| eq2PI]]; clear xzrnglb argle2PI;
  [exists (-k)%Z; (* sin arg = 0; arg= 0 *)
    apply (Rplus_eq_reg_r (- θc - 2 * IZR (-k)%Z * PI)); setr 0;
      rewrite opp_IZR;
      setl (φ - θc + 2 * IZR k * PI); assumption
        | clear xzrngub (* sin arg = 0; arg= PI *)
        | rewrite eq2PI in xzrngub; lra]. (* sin arg = 0; arg= 2*PI *)

  assert (φ = θc + IZR (2*(-k)+1) * PI) as phidef. {
    rewrite plus_IZR, mult_IZR, opp_IZR.
    apply (Rplus_eq_reg_r (- θc + 2 * IZR k * PI)).
    setl (φ - θc + 2 * IZR k * PI).
    setr PI.
    assumption. }
  rewrite phidef in xfun.
  assert (exists m, κ₂ x₁ y₁ r θc = θc + IZR (2 * m + 1) * PI) as exfun. {
    exists (-k)%Z. assumption. }

  + exfalso. (* sin argument is PI *)
    specialize (theta2_odd _ _ _ _ rne0 phasec exfun) as [n t2rt].
    specialize (theta2_rsgn_bnd _ _ _ rne0 phasec) as [prbnd nrbnd].
    destruct (Rlt_dec 0 r) as [rpos | rneg];
      [ specialize (prbnd rpos) as [t2lb t2ub]; clear nrbnd |
        apply Rnot_lt_le in rneg;
        destruct rneg as [rlt0 |req0];
        [|clear - req0 rne0; lra];
        specialize (nrbnd rlt0) as [t2lb t2ub]; clear prbnd].

    ++ destruct (Rlt_dec 0 y₁) as [y1gt0 | y1le0];
         [|apply Rnot_lt_ge in y1le0;
           apply Rge_le in y1le0;
           destruct y1le0 as [y1lt0 | y1eq0]].
       +++ specialize (root_ordering_rpos_left _ _ _ rpos y1gt0 phasec)
           as [rol rou].

           unfold calcθ₁, atan2 in *.
           destruct (pre_atan2 (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0)
                               ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0))
             as [θmax2 [[θmax2lb θmax2ub] [y1def x1def]]].
           rewrite x1, y1 in *.

           change (θ1 x₁ y₁ r < θmax) in rol.
           change (θmax < θ2 x₁ y₁ r) in rou.
           assert (- 2 * PI < θmax) as θmaxlb. {
             unfold θmax. clear - θmax2lb. lra. }
           assert (θmax <= 2 * PI) as θmaxub. {
             unfold θmax. clear - θmax2ub. lra. }

           destruct tcrng as [zlttmb tmlt0b].
           destruct (total_order_T 0 θmax) as [[zlttm | zeqtm]| zgttm].
           ++++ clear tmlt0b.
                specialize (zlttmb zlttm) as [[ptcl ptcu] | [ntcl ntcu]].
                +++++ destruct n.
                ++++++ rewrite mult_IZR, Rmult_0_r, Rmult_0_l, Rplus_0_r
                  in t2rt.
                rewrite <- t2rt in *.
                lra.
                ++++++ assert (2 * PI <= IZR (2 * Z.pos p) * PI) as gt2PI. {
                  assert ((1 <= IZR (Z.pos p)%Z)) as posge1. {
                    apply IZR_le. lia. }
                  apply (Rmult_le_compat_l (2*PI)) in posge1; [|lra].
                  rewrite mult_IZR.
                  lra. }
                lra.
                ++++++ assert (IZR (2 * Z.neg p) * PI <= - 2 * PI) as gt2PI. {
                  assert ((IZR (Z.neg p)%Z <= -1)) as posge1. {
                    apply IZR_le. lia. }
                  apply (Rmult_le_compat_l (2*PI)) in posge1; [|lra].
                  rewrite mult_IZR.
                  lra. }
                lra.
                +++++ assert (0 < θc) as tcpos. {
                  clear - rpos rcompat.
                  apply zlt_mult in rcompat;
                    [ assumption | left; assumption]. }
                lra.
           ++++ apply tmaxne0. symmetry in zeqtm. assumption.
           ++++ apply Rgt_lt in zgttm. clear θmaxub.
                clear - zgttm y1gt0 PI_RGT_0 tmd nX.
                change (θmax = 2 * atan2 y₁ x₁) in tmd.
                rewrite tmd in zgttm.
                apply Ropp_gt_lt_0_contravar in zgttm.
                apply Rgt_lt in zgttm.
                rewrite Rmult_comm, Ropp_mult_distr_l, Rmult_comm in zgttm.
                apply zlt_mult in zgttm; [|lra].
                apply Ropp_0_lt_gt_contravar in zgttm.
                rewrite Ropp_involutive in zgttm.
                apply Rgt_lt in zgttm.
                destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] | zgtx1].
                +++++ specialize (atan2Q1 _ _ zltx1 y1gt0) as [lb ub].
                lra.
                +++++ rewrite <- zeqx1 in *.
                specialize (atan2_PI2 _ y1gt0) as at2d.
                rewrite at2d in zgttm.
                lra.
                +++++ apply Rgt_lt in zgtx1.
                specialize (atan2Q2 _ _ zgtx1 y1gt0) as [lb ub].
                lra.
       +++ specialize (root_ordering_rpos_right _ _ _ rpos y1lt0 phasec)
           as [rol rou].

           unfold calcθ₁, atan2 in *.
           destruct (pre_atan2 (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0)
                               ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0))
             as [θmax2 [[θmax2lb θmax2ub] [y1def x1def]]].
           rewrite x1, y1 in *.

           change (θ2 x₁ y₁ r < θmax / 2 + 2 * PI) in rol.
           change (θmax / 2 + 2 * PI < θ1 x₁ y₁ r) in rou.
           assert (- 2 * PI < θmax) as θmaxlb. {
             unfold θmax. clear - θmax2lb. lra. }
           assert (θmax <= 2 * PI) as θmaxub. {
             unfold θmax. clear - θmax2ub. lra. }

           destruct tcrng as [zlttmb tmlt0b].
           destruct (total_order_T 0 θmax) as [[zlttm | zeqtm]| zgttm].
           ++++ clear tmlt0b.
                clear - zlttm y1lt0 PI_RGT_0 tmd nX.
                change (θmax = 2 * atan2 y₁ x₁) in tmd.
                rewrite tmd in zlttm.
                apply zlt_mult in zlttm; [|lra].
                destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] | zgtx1].
                +++++ specialize (atan2Q4 _ _ zltx1 y1lt0) as [lb ub].
                lra.
                +++++ rewrite <- zeqx1 in *.
                specialize (atan2_mPI2 _ y1lt0) as at2d.
                rewrite at2d in zlttm.
                lra.
                +++++ apply Rgt_lt in zgtx1.
                specialize (atan2Q3 _ _ zgtx1 y1lt0) as [lb ub].
                lra.
           ++++ apply tmaxne0. symmetry in zeqtm. assumption.
           ++++ apply Rgt_lt in zgttm.
                specialize (tmlt0b zgttm) as [[ptcl ptcu] | [ntcl ntcu]].
                +++++ assert (0 < θc) as tcpos. {
                  clear - rpos rcompat.
                  apply zlt_mult in rcompat;
                    [ assumption | left; assumption]. }
                lra.
                +++++ destruct n.
                ++++++ rewrite mult_IZR, Rmult_0_r, Rmult_0_l, Rplus_0_r
                  in t2rt.
                rewrite <- t2rt in *.
                lra.
                ++++++ assert (2 * PI <= IZR (2 * Z.pos p) * PI) as gt2PI. {
                  assert ((1 <= IZR (Z.pos p)%Z)) as posge1. {
                    apply IZR_le. lia. }
                  apply (Rmult_le_compat_l (2*PI)) in posge1; [|lra].
                  rewrite mult_IZR.
                  lra. }
                lra.
                ++++++ assert (IZR (2 * Z.neg p) * PI <= - 2 * PI) as gt2PI. {
                  assert ((IZR (Z.neg p)%Z <= -1)) as posge1. {
                    apply IZR_le. lia. }
                  apply (Rmult_le_compat_l (2*PI)) in posge1; [|lra].
                  rewrite mult_IZR.
                  lra. }
                lra.
       +++ destruct (total_order_T 0 x₁) as [[zltx1 | zeqx1 ] | zgtx1];
             [clear - nX y1eq0 zltx1; apply nX; split; [left|]; assumption|
              clear - nX y1eq0 zeqx1; apply nX; split; [right|]; auto |
              apply Rgt_lt in zgtx1].
           assert (x₁ <= 0) as x1le0; [lra|].
           specialize (root_ordering_rpos_back
                         _ _ _ rpos y1eq0 x1le0 phasec) as [t1ub tmeq2PI].
           change (θmax = 2 * PI) in tmeq2PI.
           change (θ1 x₁ y₁ r < θmax) in t1ub.
           clear x1le0.
           rewrite y1eq0 in *.

           assert (θ2 x₁ 0 r = 2*PI) as t2def. {
             unfold θ2.
             destruct (total_order_T 0 r) as [[zltr |zeqr]|zgtr];
               [ | lra| lra].
             destruct (total_order_T 0 0) as [[zlty1 |zeqy1]|zgty1'];
               [lra | | lra].
             destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1]|zgtx1'];
               lra. }

           rewrite t2def in *. clear t2def.
           assert (0 < θmax) as zlttm. {
             lra. }
           assert (0 < θc) as tcpos. {
                  clear - rpos rcompat.
                  apply zlt_mult in rcompat;
                    [ assumption | left; assumption]. }
           destruct tcrng as [zlttmc tmlt0c]. clear tmlt0c.
           specialize (zlttmc zlttm) as [[lb ub]| [lb ub]].
           rewrite tmeq2PI in ub.
           clear - tcpos ub t2rt.
           destruct n.
           +++++ rewrite mult_IZR, Rmult_0_r, Rmult_0_l, Rplus_0_r in t2rt.
           lra.
           +++++ assert (2 * PI <= IZR (2 * Z.pos p) * PI) as gt2PI. {
                  assert ((1 <= IZR (Z.pos p)%Z)) as posge1. {
                    apply IZR_le. lia. }
                  apply (Rmult_le_compat_l (2*PI)) in posge1; [|lra].
                  rewrite mult_IZR.
                  lra. }
           lra.
           +++++ assert (IZR (2 * Z.neg p) * PI <= - 2 * PI) as gt2PI. {
                  assert ((IZR (Z.neg p)%Z <= -1)) as posge1. {
                    apply IZR_le. lia. }
                  apply (Rmult_le_compat_l (2*PI)) in posge1; [|lra].
                  rewrite mult_IZR.
                  lra. }
           lra.
           +++++ assert (θc < 0) as tclt0. lra.
           lra.
           
    ++ destruct (Rlt_dec 0 y₁) as [y1gt0 | y1le0];
         [|apply Rnot_lt_ge in y1le0;
           apply Rge_le in y1le0;
           destruct y1le0 as [y1lt0 | y1eq0]].
       +++ specialize (root_ordering_rneg_left _ _ _ rlt0 y1gt0 phasec)
           as [rol rou].

           unfold calcθ₁, atan2 in *.
           destruct (pre_atan2 (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0)
                               ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0))
             as [θmax2 [[θmax2lb θmax2ub] [y1def x1def]]].
           rewrite x1, y1 in *.

           change (θ1 x₁ y₁ r < θmax / 2 - 2 * PI) in rol.
           change (θmax / 2 - 2 * PI < θ2 x₁ y₁ r) in rou.
           assert (- 2 * PI < θmax) as θmaxlb. {
             unfold θmax. clear - θmax2lb. lra. }
           assert (θmax <= 2 * PI) as θmaxub. {
             unfold θmax. clear - θmax2ub. lra. }

           destruct tcrng as [zlttmb tmlt0b].
           destruct (total_order_T 0 θmax) as [[zlttm | zeqtm]| zgttm].
           ++++ clear tmlt0b.
                specialize (zlttmb zlttm) as [[ptcl ptcu] | [ntcl ntcu]].
                +++++ assert (θc < 0) as tcneg. {
                  clear - rlt0 rcompat.
                  rewrite <- Rmult_opp_opp in rcompat.
                  apply zlt_mult in rcompat; lra. }
                lra.
                +++++ destruct n.
                ++++++ rewrite mult_IZR, Rmult_0_r, Rmult_0_l, Rplus_0_r
                  in t2rt.
                rewrite <- t2rt in *.
                lra.
                ++++++ assert (2 * PI <= IZR (2 * Z.pos p) * PI) as gt2PI. {
                  assert ((1 <= IZR (Z.pos p)%Z)) as posge1. {
                    apply IZR_le. lia. }
                  apply (Rmult_le_compat_l (2*PI)) in posge1; [|lra].
                  rewrite mult_IZR.
                  lra. }
                lra.
                ++++++ assert (IZR (2 * Z.neg p) * PI <= - 2 * PI) as gt2PI. {
                  assert ((IZR (Z.neg p)%Z <= -1)) as posge1. {
                    apply IZR_le. lia. }
                  apply (Rmult_le_compat_l (2*PI)) in posge1; [|lra].
                  rewrite mult_IZR.
                  lra. }
                lra.

           ++++ apply tmaxne0. symmetry in zeqtm. assumption.
           ++++ apply Rgt_lt in zgttm. clear θmaxub.
                clear - zgttm y1gt0 PI_RGT_0 tmd nX.
                change (θmax = 2 * atan2 y₁ x₁) in tmd.
                rewrite tmd in zgttm.
                apply Ropp_gt_lt_0_contravar in zgttm.
                apply Rgt_lt in zgttm.
                rewrite Rmult_comm, Ropp_mult_distr_l, Rmult_comm in zgttm.
                apply zlt_mult in zgttm; [|lra].
                apply Ropp_0_lt_gt_contravar in zgttm.
                rewrite Ropp_involutive in zgttm.
                apply Rgt_lt in zgttm.
                destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] | zgtx1].
                +++++ specialize (atan2Q1 _ _ zltx1 y1gt0) as [lb ub].
                lra.
                +++++ rewrite <- zeqx1 in *.
                specialize (atan2_PI2 _ y1gt0) as at2d.
                rewrite at2d in zgttm.
                lra.
                +++++ apply Rgt_lt in zgtx1.
                specialize (atan2Q2 _ _ zgtx1 y1gt0) as [lb ub].
                lra.
       +++ specialize (root_ordering_rneg_right _ _ _ rlt0 y1lt0 phasec)
           as [rol rou].

           unfold calcθ₁, atan2 in *.
           destruct (pre_atan2 (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0)
                               ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0))
             as [θmax2 [[θmax2lb θmax2ub] [y1def x1def]]].
           rewrite x1, y1 in *.

           change (θ2 x₁ y₁ r < θmax) in rol.
           change (θmax < θ1 x₁ y₁ r) in rou.
           assert (- 2 * PI < θmax) as θmaxlb. {
             unfold θmax. clear - θmax2lb. lra. }
           assert (θmax <= 2 * PI) as θmaxub. {
             unfold θmax. clear - θmax2ub. lra. }

           destruct tcrng as [zlttmb tmlt0b].
           destruct (total_order_T 0 θmax) as [[zlttm | zeqtm]| zgttm].
           ++++ clear tmlt0b.
                clear - zlttm y1lt0 PI_RGT_0 tmd nX.
                change (θmax = 2 * atan2 y₁ x₁) in tmd.
                rewrite tmd in zlttm.
                apply zlt_mult in zlttm; [|lra].
                destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] | zgtx1].
                +++++ specialize (atan2Q4 _ _ zltx1 y1lt0) as [lb ub].
                lra.
                +++++ rewrite <- zeqx1 in *.
                specialize (atan2_mPI2 _ y1lt0) as at2d.
                rewrite at2d in zlttm.
                lra.
                +++++ apply Rgt_lt in zgtx1.
                specialize (atan2Q3 _ _ zgtx1 y1lt0) as [lb ub].
                lra.
           ++++ apply tmaxne0. symmetry in zeqtm. assumption.
           ++++ apply Rgt_lt in zgttm.
                specialize (tmlt0b zgttm) as [[ptcl ptcu] | [ntcl ntcu]].
                +++++ destruct n.
                ++++++ rewrite mult_IZR, Rmult_0_r, Rmult_0_l, Rplus_0_r
                  in t2rt.
                rewrite <- t2rt in *.
                lra.
                ++++++ assert (2 * PI <= IZR (2 * Z.pos p) * PI) as gt2PI. {
                  assert ((1 <= IZR (Z.pos p)%Z)) as posge1. {
                    apply IZR_le. lia. }
                  apply (Rmult_le_compat_l (2*PI)) in posge1; [|lra].
                  rewrite mult_IZR.
                  lra. }
                lra.
                ++++++ assert (IZR (2 * Z.neg p) * PI <= - 2 * PI) as gt2PI. {
                  assert ((IZR (Z.neg p)%Z <= -1)) as posge1. {
                    apply IZR_le. lia. }
                  apply (Rmult_le_compat_l (2*PI)) in posge1; [|lra].
                  rewrite mult_IZR.
                  lra. }
                lra.
                +++++ assert (θc < 0) as tcneg. {
                  clear - rlt0 rcompat.
                  rewrite <- Rmult_opp_opp in rcompat.
                  apply zlt_mult in rcompat; lra. }
                lra.

       +++ destruct (total_order_T 0 x₁) as [[zltx1 | zeqx1 ] | zgtx1];
             [clear - nX y1eq0 zltx1; apply nX; split; [left|]; assumption|
              clear - nX y1eq0 zeqx1; apply nX; split; [right|]; auto |
              apply Rgt_lt in zgtx1].
           lra.
Qed.

Lemma straight_rot : forall r θ₀ x₀ y₀ x₁ y₁,
    straight r θ₀ x₀ y₀ x₁ y₁ ->
    straight r 0 0 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
             (- (x₁-x₀)* sin θ₀ + (y₁-y₀)*cos θ₀).
Proof.
  intros *. intro strt.

  unfold straight, Tcx, Tcy in *.
  autorewrite with null.

  assert (x₁ - (x₀ + r * cos (PI / 2 + θ₀)) =
          ((x₁ - x₀) + r * - cos (PI / 2 + θ₀))) as id. field.
  rewrite id in strt. clear id.
  assert (y₁ - (y₀ + r * sin (PI / 2 + θ₀)) =
          ((y₁ - y₀) - r * sin (PI / 2 + θ₀))) as id. field.
  rewrite id in strt. clear id.
  rewrite <- cos_sin, <- sin_cos in strt.
  rewrite Rsqr_plus, (Rsqr_minus (y₁ - y₀)) in strt.
  fieldrewrite ((- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ - r))
               ((- (x₁ - x₀) * sin θ₀) + ((y₁ - y₀) * cos θ₀ - r)).
  rewrite Rsqr_plus.
  rewrite Rsqr_plus.
  fieldrewrite (((x₁ - x₀) * cos θ₀)² + ((y₁ - y₀) * sin θ₀)² +
                2 * ((x₁ - x₀) * cos θ₀) * ((y₁ - y₀) * sin θ₀) +
                ((- (x₁ - x₀) * sin θ₀)² + ((y₁ - y₀) * cos θ₀ - r)² +
                 2 * (- (x₁ - x₀) * sin θ₀) * ((y₁ - y₀) * cos θ₀ - r)))
               ((x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²) +
                (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²) +
                r² +
                2 * r * ((x₁ - x₀) * sin θ₀ - (y₁ - y₀) * cos θ₀)
               ).
  rewrite sin2_cos2, Rmult_1_r, Rmult_1_r.
  rewrite <- (Rmult_1_r (r²)) at 2.
  rewrite <- (sin2_cos2 θ₀).
  setr ((x₁ - x₀)² + (r * sin θ₀)² + 2 * (x₁ - x₀) * (r * sin θ₀) +
        ((y₁ - y₀)² + (r * cos θ₀)² - 2 * (y₁ - y₀) * (r * cos θ₀))).
  assumption.
Qed.

Lemma rot_straight : forall r θ₀ x₀ y₀ x₁ y₁,
    straight r 0 0 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
             (- (x₁-x₀)* sin θ₀ + (y₁-y₀)*cos θ₀) ->
    straight r θ₀ x₀ y₀ x₁ y₁.
Proof.
    intros *. intro strt.

  unfold straight, Tcx, Tcy in *.
  autorewrite with null in *.

  assert (x₁ - (x₀ + r * cos (PI / 2 + θ₀)) =
          ((x₁ - x₀) + r * - cos (PI / 2 + θ₀))) as id. field.
  rewrite id. clear id.
  assert (y₁ - (y₀ + r * sin (PI / 2 + θ₀)) =
          ((y₁ - y₀) - r * sin (PI / 2 + θ₀))) as id. field.
  rewrite id. clear id.
  rewrite <- cos_sin, <- sin_cos.
  rewrite Rsqr_plus, (Rsqr_minus (y₁ - y₀)).
  assert ((- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ - r)=
          (- (x₁ - x₀) * sin θ₀) + ((y₁ - y₀) * cos θ₀ - r)) as id; try lra.
  rewrite id in strt; clear id.
  rewrite Rsqr_plus in strt.
  rewrite Rsqr_plus in strt.
  assert (((x₁ - x₀) * cos θ₀)² + ((y₁ - y₀) * sin θ₀)² +
                2 * ((x₁ - x₀) * cos θ₀) * ((y₁ - y₀) * sin θ₀) +
                ((- (x₁ - x₀) * sin θ₀)² + ((y₁ - y₀) * cos θ₀ - r)² +
                 2 * (- (x₁ - x₀) * sin θ₀) * ((y₁ - y₀) * cos θ₀ - r)) = 
               ((x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²) +
                (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²) +
                r² +
                2 * r * ((x₁ - x₀) * sin θ₀ - (y₁ - y₀) * cos θ₀)
               )) as id. unfold Rsqr. field. rewrite id in strt; clear id.
  rewrite sin2_cos2, Rmult_1_r, Rmult_1_r in strt.
  rewrite <- (Rmult_1_r (r²)) in strt at 2 .
  rewrite <- (sin2_cos2 θ₀) in strt.
  lrag strt.
Qed.



Lemma turning_rot : forall r θ₀ x₀ y₀ x₁ y₁,
    turning r θ₀ x₀ y₀ x₁ y₁ ->
    turning r 0 0 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀).
Proof.
  intros * phase.
  unfold turning, Tcx, Tcy in *.
  autorewrite with null in *.
  rewrite <- cos_sin in phase.
  assert (x₁ - (x₀ + r * cos (PI / 2 + θ₀)) = x₁ - x₀ + r * - cos (PI / 2 + θ₀)) as id.
  field.
  rewrite id in phase.
  clear id.
  rewrite <- sin_cos in phase.
  rewrite phase. clear phase.
  repeat rewrite Rsqr_plus in *.
  repeat rewrite Rsqr_minus in *.
  repeat rewrite Rsqr_plus in *.
  
  setl ((x₁ - x₀)²
        + (y₁ - y₀)²
        + r² * ((sin θ₀)² + (cos θ₀)²)
        + 2 * (x₁ - x₀) * (r * sin θ₀)
        + (- 2 * (y₁ - y₀) * (r * cos θ₀))).
  setr ((x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²)
        + (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²)
        + r²
          - 2 * (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) * r).
  repeat rewrite sin2_cos2.
  field.
Qed.

Lemma rot_turning : forall r θ₀ x₀ y₀ x₁ y₁,
    turning r 0 0 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
            (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) ->
    turning r θ₀ x₀ y₀ x₁ y₁.
Proof.
  intros * phase.
  unfold turning, Tcx, Tcy in *.
  autorewrite with null in *.
  rewrite <- cos_sin.
  assert (x₁ - (x₀ + r * cos (PI / 2 + θ₀)) = x₁ - x₀ + r * - cos (PI / 2 + θ₀)) as id.
  field.
  rewrite id.
  clear id.
  rewrite <- sin_cos.
  rewrite phase. clear phase.
  repeat rewrite Rsqr_plus in *.
  repeat rewrite Rsqr_minus in *.
  repeat rewrite Rsqr_plus in *.
  
  setr ((x₁ - x₀)²
        + (y₁ - y₀)²
        + r² * ((sin θ₀)² + (cos θ₀)²)
        + 2 * (x₁ - x₀) * (r * sin θ₀)
        + (- 2 * (y₁ - y₀) * (r * cos θ₀))).
  setl ((x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²)
        + (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²)
        + r²
          - 2 * (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) * r).
  repeat rewrite sin2_cos2.
  field.
Qed.

Lemma straight_path_exists : forall (x₀ y₀ θ₀ x₁ y₁ θc : R),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nO : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (tmaxne0 : θmax <> 0)
           (tcrng : (0 < θmax -> (θmax/2 < θc < θmax \/
                                 - 2*PI < θc < θmax/2 - 2*PI )) /\
                    (θmax < 0 -> (θmax < θc < θmax/2 \/
                                  θmax/2 + 2*PI < θc < 2*PI))),
      let r := ((x₁ - x₀) * sin (θ₀ + θc) - (y₁ - y₀) * cos (θ₀ + θc)) /
                                (1 - cos θc) in
      let Ldx := x₁ - Hxarc r θ₀ x₀ (r * θc) in
      let Ldy := y₁ - Hyarc r θ₀ y₀ (r * θc) in
      forall (phase : straight r θ₀ x₀ y₀ x₁ y₁)
             (rne0 : r <> 0)
             (sac : ~ (r<0 /\
                       ((x₁-x₀)* cos θ₀ + (y₁-y₀)*sin θ₀)<0 /\
                       (- (x₁-x₀)* sin θ₀ + (y₁-y₀)*cos θ₀)=0)),
      exists k : Z, atan2 Ldy Ldx = θ₀ + θc + 2 * IZR k * PI.
Proof.
  intros.
  unfold Ldx, Ldy. clear Ldx Ldy.
  rewrite xxlate_arm, yxlate_arm.
  rewrite Hyarc_rot,  (Hxarc_rot r θ₀ θc). 
  apply straight_rot in phase.

  unfold r in *.  clear r.
  rewrite rxlate in *.
  specialize (rotated_straight_path_equiv _ _ _ _ _ nO tmaxne0) as nots.
  unfold θmax in *. clear θmax.
  rewrite calc_angle_std in *.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  set (r := (x * sin θc - y * cos θc) / (1 - cos θc)) in *.
  set (θmax := calcθ₁ 0 0 0 x y) in *.
  specialize (straight_path_exists_s x y θc nots tcrng phase sac) as [q foo].
  apply atan2_rot1_rot2.
  change (~ (x - Hxarc r 0 0 (r * θc) = 0 /\ y - Hyarc r 0 0 (r * θc)= 0)).
  change (atan2 (y - Hyarc r 0 0 (r * θc))
                (x - Hxarc r 0 0 (r * θc)) = θc + 2 * IZR q * PI) in foo.
  assert ((2 * r - y) * y < x²) as ssa. {
    unfold straight, Tcx, Tcy in phase.
    autorewrite with null in phase.
    rewrite Rsqr_minus in phase.
    apply (Rplus_lt_reg_r (r² - (2 * r - y) * y)).
    setl r².
    setr (x² + (y² + r² - 2 * y * r)).
    assumption. }
  unfold Hxarc, Hyarc.
  autorewrite with null.
  fieldrewrite (r * θc / r) (θc); 
    [assumption|].
  fieldrewrite (- r * cos θc + r) (r*(1 - cos θc)).
  intros [xd yd].
  apply Rminus_diag_uniq in xd.
  apply Rminus_diag_uniq in yd.
  rewrite xd, yd in ssa.
  rewrite Rmult_minus_distr_r in ssa.
  assert (2 * r * (r * (1 - cos θc)) - r * (1 - cos θc) * (r * (1 - cos θc)) =
          2 * r² - r² * 1 - r² * (cos θc)²) as id. unfold Rsqr. field.
  rewrite id in ssa. clear id.
  generalize ssa.
  change (~(2 * r² - r² * 1 - r² * (cos θc)² < (r * sin θc)²)).
  apply Rle_not_lt.
  apply (Rplus_le_reg_r (r² * (cos θc)²)).
  setl (r² * ((sin θc)² + (cos θc)²)).
  rewrite sin2_cos2, Rmult_1_r.
  setr r². right. reflexivity.
  exists q. assumption.
Qed.

Lemma nxaxiscond : forall (x₀ y₀ x₁ y₁ θ₀ : R),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ < 0 /\
     - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ = 0) ->
    θmax = 2*PI.
Proof.
  intros *. intros [nx zy].
  unfold θmax.
  unfold calcθ₁.
  rewrite zy.
  apply (Rmult_eq_reg_r (/2)); [|apply Rinv_neq_0_compat; lra].
  setr PI. setl (atan2 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)).
  apply atan2_PI.
  assumption.
Qed.

Lemma nposx_t1ne0:
  forall (x₁ y₁ r : R)
    (nO : ~ (0 <= x₁ /\ y₁ = 0))
    (rne0 : r <> 0)
    (rrng : 2 * r * y₁ < x₁² + y₁²),
    θ1 x₁ y₁ r <> 0.
Proof.
  intros.
  intro tceq0.
  unfold θ1 in tceq0.
  apply nO.

  assert (0 < x₁² - (2 * r - y₁) * y₁) as a1gt0. {
    apply (Rplus_lt_reg_r (2 * r * y₁)).
    lrag rrng. }

  destruct total_order_T; [destruct s|]; try lra.
  + destruct total_order_T; [destruct s|]; try lra.
    ++ destruct total_order_T; [destruct s|]; try lra.
       +++ destruct total_order_T; [destruct s|]; try lra.
           ++++ exfalso.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                assert (0 < x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) as a2gt0. {
                  rewrite <- (sqrt_Rsqr x₁) at 1; try lra.
                  apply Rlt_Rminus.
                  apply sqrt_lt_1.
                  - left; assumption.
                  - apply Rle_0_sqr.
                  - apply (Rplus_lt_reg_r (-x₁²)).
                    setr (-0); try lra.
                    setl (- ((2 * r - y₁) * y₁)).
                    apply Ropp_lt_contravar.
                    apply Rmult_lt_0_compat; try lra. }
                assert (0 < ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                               / (2 * r - y₁)))
                  as a3gt0. {
                  rewrite <- RmultRinv.
                  zltab. }
                comp.
                
           ++++ exfalso.
                symmetry in e.
                apply Rminus_diag_uniq_sym in e.
                rewrite e in tceq0.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                assert (0 < (2 * r / (2 * x₁)))
                  as a3gt0. {
                  rewrite <- RmultRinv.
                  zltab. }
                comp.

           ++++ exfalso.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                assert (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁) < 0) as a2gt0. {
                  rewrite <- (sqrt_Rsqr x₁) at 1; try lra.
                  apply Rlt_minus.
                  apply sqrt_lt_1.
                  - apply Rle_0_sqr.
                  - left; assumption.
                  - apply (Rplus_lt_reg_r (-x₁²)).
                    setl (0); try lra.
                    setr (- (2 * r - y₁) * y₁).
                    zltab. }
                assert (0 < ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                               / (2 * r - y₁)))
                  as a3gt0. {
                  setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) *
                          / - (2 * r - y₁)).
                  lra.
                  zltab.
                  lra. }
                comp.
                
       +++ exfalso.
           comp.
    ++ destruct total_order_T; [destruct s|]; try lra.
       +++ destruct total_order_T; [destruct s|]; try lra.
           ++++ exfalso.
                rewrite <- e in *.
                autorewrite with null in *.
                rewrite Ropp_mult_distr_r in a1gt0.
                apply zlt_mult in a1gt0; try lra.
           ++++ exfalso.
                rewrite <- e0, <- e in *.
                autorewrite with null in *.
                lra.
           ++++ exfalso.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                assert (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁) < 0) as a2gt0. {
                  rewrite <- (sqrt_Rsqr x₁) at 1; try lra.
                  apply Rlt_minus.
                  apply sqrt_lt_1.
                  - apply Rle_0_sqr.
                  - left; assumption.
                  - apply (Rplus_lt_reg_r (-x₁²)).
                    setl (0); try lra.
                    setr (- (2 * r - y₁) * y₁).
                    zltab. }
                assert (0 < ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                               / (2 * r - y₁)))
                  as a3gt0. {
                  setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) *
                          / - (2 * r - y₁)).
                  lra.
                  zltab.
                  lra. }
                comp.
       +++ exfalso.
           comp.
    ++ destruct total_order_T; [destruct s|]; try lra.
       +++ destruct total_order_T; [destruct s|]; try lra.
           ++++ exfalso.
                comp.
           ++++ specialize PI_RGT_0 as pigt0; lra.
           ++++ exfalso.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                assert (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁) < 0) as a2gt0. {
                  assert (0 < sqrt (x₁² - (2 * r - y₁) * y₁)) as zltsq. {
                    rewrite <- sqrt_0.
                    apply sqrt_lt_1; try lra. }
                  lra. }
                assert (0 < ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                               / (2 * r - y₁))) as a3gt0. {
                  setr (- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) *
                        / - (2 * r - y₁)); try lra.
                  zltab.
                  lra. }
                comp.
       +++ exfalso.
           comp.
       +++ exfalso.
           comp.
  + destruct total_order_T; [destruct s|]; try lra.
    ++ destruct total_order_T; [destruct s|]; try lra.
       +++ exfalso.
           comp.
       +++ destruct total_order_T; [destruct s|]; try lra.
           ++++ exfalso.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                assert (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁) < 0) as a2gt0. {
                  assert (0 < sqrt (x₁² - (2 * r - y₁) * y₁)) as zltsq. {
                    rewrite <- sqrt_0.
                    apply sqrt_lt_1; try lra. }
                  rewrite <- (sqrt_Rsqr x₁) at 1; try lra.
                  apply Rlt_minus.
                  apply sqrt_lt_1.
                  - apply Rle_0_sqr.
                  - left; assumption.
                  - apply (Rplus_lt_reg_r (-x₁²)).
                    setl (0); try lra.
                    setr ((2 * r - y₁) * - y₁).
                    zltab. }
                assert (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                           / (2 * r - y₁)) < 0) as a3gt0. {
                  rewrite <- RmultRinv.
                  setl (- ((- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))) *
                          / (2 * r - y₁))); try lra.
                  setr (- 0).
                  apply Ropp_lt_contravar.
                  zltab. }
                comp.
           ++++ exfalso.
                symmetry in e.
                apply Rminus_diag_uniq_sym in e.
                rewrite e in tceq0.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                assert ((2 * r / (2 * x₁)) < 0)
                  as a3gt0. {
                  setl (-((2 * -r) * / (2 * x₁))); try lra.
                  setr (-0).
                  apply Ropp_lt_contravar.
                  zltab. }
                comp.
           ++++ exfalso.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                assert (0 < x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) as a2gt0. {
                  rewrite <- (sqrt_Rsqr x₁) at 1; try lra.
                  apply Rlt_Rminus.
                  apply sqrt_lt_1.
                  - left; assumption.
                  - apply Rle_0_sqr.
                  - apply (Rplus_lt_reg_r (-x₁²)).
                    setr (- 0); try lra.
                    setl (- (- (2 * r - y₁) * - y₁)).
                    apply Ropp_lt_contravar.
                    zltab. }
                assert (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                               / (2 * r - y₁)) < 0)
                  as a3gt0. {
                  setl (-((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) *
                          / - (2 * r - y₁))).
                  lra.
                  setr (- 0); try lra.
                  apply Ropp_lt_contravar.
                  zltab.
                  lra. }
                comp.
    ++ destruct total_order_T; [destruct s|]; try lra.
       +++ exfalso.
           comp.
       +++ destruct total_order_T; [destruct s|]; try lra.
           ++++ exfalso.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                assert (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁) < 0) as a2gt0. {
                  rewrite <- e.
                  arn.
                  setr (-0).
                  apply Ropp_lt_contravar.
                  rewrite <- sqrt_0.
                  apply sqrt_lt_1.
                  - right; reflexivity.
                  - rewrite Ropp_mult_distr_r.
                    zltab.
                  - rewrite Ropp_mult_distr_r.
                    zltab. }
                assert (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                           / (2 * r - y₁)) < 0) as a3gt0. {
                  rewrite <- RmultRinv.
                  setl (- ((- (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))) *
                          / (2 * r - y₁))); try lra.
                  setr (- 0).
                  apply Ropp_lt_contravar.
                  zltab. }
                comp.
           ++++ exfalso.
                rewrite <- e0, <- e in a1gt0.
                autorewrite with null in a1gt0.
                lra.
           ++++ exfalso.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                rewrite <- e in *.
                autorewrite with null in *.
                assert (- ((2 * r - y₁) * y₁) < 0) as contr. {
                  rewrite <- Ropp_0.
                  apply Ropp_lt_contravar.
                  setr (- (2 * r - y₁) * - y₁).
                  zltab. }
                lra.
    ++ destruct total_order_T; [destruct s|]; try lra.
       +++ exfalso.
           comp.
       +++ exfalso.
           comp.
       +++ destruct total_order_T; [destruct s|]; try lra.
           ++++ exfalso.
                apply Rmult_integral in tceq0.
                destruct tceq0 as [ctr| ateq0]; try lra.
                assert (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁) < 0) as a2gt0. {
                  assert (0 < sqrt (x₁² - (2 * r - y₁) * y₁)) as zltsq. {
                    rewrite <- sqrt_0.
                    apply sqrt_lt_1; try lra. }
                  lra. }
                assert (((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))
                               / (2 * r - y₁)) < 0) as a3gt0. {
                  setl (- ( - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) *
                          / (2 * r - y₁))); try lra.
                  setr (-0).
                  apply Ropp_lt_contravar.
                  zltab. }
                comp.
           ++++ specialize PI_RGT_0 as pigt0; lra.
           ++++ exfalso.
                comp.
Qed.

Lemma ottb_r_thetac_lb2_s :
  forall (x₁ y₁ r : R)
    (nO : ~ (0 <= x₁ /\ y₁ = 0))
    (rne0 : r <> 0)
    (rrng : 2 * r * y₁ < x₁² + y₁²),
    let θc := θ1 x₁ y₁ r in
        0 < r * θc.
Proof.
  intros.
  assert (straight r 0 0 0 x₁ y₁) as phase.
  unfold straight, Tcy, Tcx.
  autorewrite with null.
  rewrite Rsqr_minus.
  apply (Rplus_lt_reg_r (-r²)).
  setl 0. setr (x₁² + y₁² - 2 * y₁ * r).
  lra.

  specialize (theta1_rsgn_bnd _ _ _ rne0 phase) as [t1rgt0 t1rlt0].
  change (0 < r -> 0 <= θc < 2 * PI) in t1rgt0.
  change (r < 0 -> -2 * PI < θc <= 0) in t1rlt0.

  specialize (nposx_t1ne0 _ _ _ nO rne0 rrng) as tcne0.
  change (θc <> 0) in tcne0.
  destruct (total_order_T 0 r) as [[zltr |zeqr]|zgtr].
  + specialize (t1rgt0 zltr) as [lb ub]. clear - lb ub zltr tcne0.
    apply Rmult_lt_0_compat; try lra.
  + exfalso. apply rne0. auto.
  + specialize (t1rlt0 zgtr) as [lb ub]. clear - lb ub zgtr tcne0.
    setr (- r * - θc).
    apply Rmult_lt_0_compat; lra.
Qed.

Lemma ottb_r_thetac_lb2 :
  forall (θ₀ x₀ y₀ x₁ y₁ r : R)
         (nO : ~ ((x₁-x₀) = 0 /\ (y₁-y₀) = 0)),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmns : θmax <> 0)
           (rne0 : r <> 0)
           (phase : straight r θ₀ x₀ y₀ x₁ y₁),
      let θc := θ1 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
                   (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) r in
      0 < r * θc.
Proof.
  intros.
  specialize (rotated_straight_path_equiv _ _ _ _ _ nO tmns) as nots.
  unfold θmax in *. clear θmax.
  apply straight_rot in phase.
  rewrite calc_angle_std in *.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.

  unfold straight, Tcy, Tcx in phase.
  autorewrite with null in phase.
  rewrite Rsqr_minus in phase.
  apply (Rplus_lt_compat_r (-r²)) in phase.
  assert (2 * r * y < x² + y²) as phases.
  apply Rminus_gt_0_lt.
  setl (r² + - r²). setr (x² + (y² + r² - 2 * y * r) + - r²).
  assumption. clear phase.

  set (θmax := calcθ₁ 0 0 0 x y) in *.
  unfold θc. clear θc nO tmns θmax.
  apply (ottb_r_thetac_lb2_s _ _ _ nots rne0 phases).
Qed.

Lemma ottb_parameters2_L_calc_s :
  forall (x₁ y₁ r : R)
         (notpx : ~ (0<=x₁ /\ y₁=0))
         (rne0 : r <> 0)
         (strt : 2 * r * y₁ < x₁² + y₁²),
    let θc := θ1 x₁ y₁ r in
      (* ensure correct direction of linear path *)
    forall (Ldir : exists k, atan2 (y₁ - Hyarc r 0 0 (r * θc))
                                   (x₁ - Hxarc r 0 0 (r * θc)) =
                             θc + 2* IZR k * PI),
        calcL r 0 0 0 x₁ y₁ θc = calcL' r 0 0 0 x₁ y₁ θc.
Proof.
  intros.
  set (Ldx := (x₁ - Hxarc r 0 0 (r * θc))) in *.
  set (Ldy := (y₁ - Hyarc r 0 0 (r * θc))) in *.
  unfold calcL'.
  set (L := sqrt ( Ldy² + Ldx²)) in *.
  change (calcL r 0 0 0 x₁ y₁ θc = L).
  inversion_clear Ldir as [k Ldir']. rename Ldir' into Ldir.

  specialize (ottb_r_thetac_lb2_s _ _ _ notpx rne0 strt) as zltrthc.
  change (0 < r * θc) in zltrthc.
  
  unfold atan2 in Ldir.
  destruct (pre_atan2 Ldy Ldx) as [ζ [valrng [Ldydef Ldxdef]]].
  rewrite Ldir in *.

  assert (sin ζ  = sin (θc)) as sinper. {
    rewrite Ldir.
    rewrite sin_period1. reflexivity. }

  assert (cos ζ  = cos (θc)) as cosper. {
    rewrite Ldir.
    rewrite cos_period1. reflexivity. }

  rewrite <- Ldir in Ldydef, Ldxdef.
  rewrite <- Ldir in valrng.
  
  unfold calcL, L.
  fieldrewrite (0 + θc) (θc).
  destruct (Req_EM_T 0 (cos (θc))).
  + symmetry in e.
    generalize (coseq0_sinneq0 _ e) as sinne0; intro.

    change (Ldy / sin θc = L).
    apply (Rmult_eq_reg_r (sin θc));
      [| assumption].
    setl Ldy. assumption.

    assert (Ldx = 0) as dxdef.
    rewrite Ldxdef, cosper, e.
    field.
    
    rewrite <- sinper.
    rewrite <- cosper in e.
    inversion_clear valrng as [zetalb zetaub].

    destruct (Rle_dec 0 ζ).
    ++ assert (ζ <= 2 * PI) as zeta2PIub. lra.
       specialize (cos_eq_0_2PI_0 ζ r0 zeta2PIub e) as zetaval.
       inversion_clear zetaval as [zeta | nzeta].
       +++ rewrite zeta in *. rewrite sin_PI2 in *.
           assert (0 <= Ldy) as zleLdy. {
             rewrite Ldydef.
             apply Rmult_le_pos.
             apply sqrt_pos. lra. }
           unfold L, Rsqr at 2.
           rewrite dxdef, Rmult_1_r, Rmult_0_r, Rplus_0_r.
           rewrite sqrt_Rsqr. reflexivity. assumption.

       +++ exfalso.
           rewrite nzeta in zetaub.
           assert (3 <= 2) as contra.
           apply (Rmult_le_reg_r (PI/2)). lra.
           setr PI. assumption.
           lra.
    ++ clear zetaub.
       apply Rnot_le_lt in n.

       fieldrewrite ζ (- - ζ).
       rewrite sin_neg.
       assert (0 <= - ζ) as nzlb. lra.
       assert (- ζ <= 2*PI) as nzub. lra.
       rewrite <- cos_neg in e.
       generalize (cos_eq_0_2PI_0 (-ζ) nzlb nzub e) as zetaval. intro.
       inversion_clear zetaval as [zeta | nzeta].
       rewrite zeta.

       rewrite sin_PI2.
       assert (ζ = - - ζ) as zetanegneg. field. rewrite zetanegneg in Ldydef.
       rewrite sin_neg, zeta, sin_PI2 in Ldydef.
       assert (Ldy <= 0) as ldylt0. {
       rewrite Ldydef.
       setl (- sqrt (Ldy² + Ldx²)). setr (- 0).
       apply Ropp_le_contravar.
       apply sqrt_pos. }
       unfold L. lra.
       
       +++ exfalso.
           assert (3 < 2) as absurd.
           apply (Rmult_lt_reg_r (PI/2)). lra.
           rewrite <- nzeta.
           setr (- - PI).
           apply Ropp_lt_contravar. assumption. lra.
           
  + change (Ldx / cos (θc) = L).
    apply (Rmult_eq_reg_r (cos (θc)));
      [| auto].
    setl (Ldx). auto.
    
    unfold L.
    rewrite <- cosper.
    assumption.
Qed.

Lemma ottb_parameters2_L_calc :
  forall (θ₀ x₀ y₀ x₁ y₁ r : R),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmns : θmax <> 0)
           (rne0 : r <> 0)
           (phase : straight r θ₀ x₀ y₀ x₁ y₁),
      let θc := θ1 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
                   (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) r in
      (* ensure correct direction of linear path *)
      forall (Ldir : exists k, atan2 (y₁ - Hyarc r θ₀ y₀ (r * θc))
                                     (x₁ - Hxarc r θ₀ x₀ (r * θc)) =
                               θ₀ + θc + 2* IZR k * PI),
        calcL r θ₀ x₀ y₀ x₁ y₁ θc = calcL' r θ₀ x₀ y₀ x₁ y₁ θc.
Proof.
  intros.
  specialize Ldir as Ldiro.
  specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as notO. 
  specialize (tmne0 _ _ _ _ _ notO tmns) as notpx.
  specialize (rotated_straight_path_equiv _ _ _ _ _ notO tmns) as notpxs.
  apply straight_rot in phase.
  destruct (Req_dec r 0).
  + exfalso. auto.
  + clear H.
    assert (~ (x₁ - Hxarc r θ₀ x₀ (r * θc) = 0 /\ y₁ - Hyarc r θ₀ y₀ (r * θc) = 0) \/
            (x₁ - Hxarc r θ₀ x₀ (r * θc) = 0 /\ y₁ - Hyarc r θ₀ y₀ (r * θc) = 0))
    as [noc | oc]. {
    destruct (Req_dec (x₁ - Hxarc r θ₀ x₀ (r * θc)) 0) as [xe|xn].
    destruct (Req_dec (y₁ - Hyarc r θ₀ y₀ (r * θc)) 0) as [ye|yn];
      [right; split; assumption|].
    left; intros [z1 z2]. clear - yn z2. lra.
    left; intros [z1 z2]. clear - xn z1. lra. }
    ++ apply xlate_rot_arm in Ldir; try assumption.
       unfold θmax in *. clear θmax.
       rewrite calc_angle_std in *.
       set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
       set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
       set (θmax := calcθ₁ 0 0 0 x y) in *.
       rewrite calcL'_inv.
       rewrite calcL_inv; [|apply Ldiro].
       change (calcL r 0 0 0 x y θc = calcL' r 0 0 0 x y θc).
       apply straightcond in phase.
       apply (ottb_parameters2_L_calc_s x y r notpxs rne0 phase Ldir).
    ++ inversion oc as [xoc yoc]. unfold calcL, calcL'.
       rewrite xoc, yoc.
       destruct (Req_EM_T 0 (cos (θ₀ + θc))).
       +++ symmetry in e.
           apply coseq0_sinneq0 in e.
           apply (Rmult_eq_reg_r (sin (θ₀ + θc))); try assumption.
           setl 0; try assumption.
           rewrite Rsqr_0, Rplus_0_r, sqrt_0, Rmult_0_l.
           reflexivity.
       +++ apply (Rmult_eq_reg_r (cos (θ₀ + θc))); try auto.
           setl 0; try auto.
           rewrite Rsqr_0, Rplus_0_r, sqrt_0, Rmult_0_l.
           reflexivity.
Qed.

(* calcL is non-negative. *)
Lemma ottb_parameters2_compat_0leL :
  forall (θ₀ x₀ y₀ x₁ y₁ r : R),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmns : θmax <> 0)
           (rne0 : r <> 0)
           (phase : straight r θ₀ x₀ y₀ x₁ y₁),
      let θc := θ1 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
                   (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) r in
      (* ensure correct direction of linear path *)
      forall (Ldir : exists k, atan2 (y₁ - Hyarc r θ₀ y₀ (r * θc))
                                     (x₁ - Hxarc r θ₀ x₀ (r * θc)) =
                               θ₀ + θc + 2* IZR k * PI),
        0 <= calcL r θ₀ x₀ y₀ x₁ y₁ θc.
Proof.
  intros.
  specialize (ottb_parameters2_L_calc _ _ _ _ _ _ tmns rne0 phase Ldir) as
      calcLdef.
  set (Ldy := y₁ - Hyarc r θ₀ y₀ (r * θc)).
  set (Ldx := x₁ - Hxarc r θ₀ x₀ (r * θc)).
  set (L := sqrt (Ldy² + Ldx²)).
  change (calcL r θ₀ x₀ y₀ x₁ y₁ θc = L) in calcLdef.
  rewrite calcLdef.
  apply sqrt_pos.
Qed.

Lemma ottb_parameters2_compat_L :
  forall (θ₀ x₀ y₀ x₁ y₁ r : R),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmns : θmax <> 0)
           (rne0 : r <> 0)
           (phase : straight r θ₀ x₀ y₀ x₁ y₁),
      let θc := θ1 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
                   (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) r in
      (* ensure correct direction of linear path *)
      forall (Ldir : exists k, atan2 (y₁ - Hyarc r θ₀ y₀ (r * θc))
                                     (x₁ - Hxarc r θ₀ x₀ (r * θc)) =
                               θ₀ + θc + 2* IZR k * PI),
        0 < calcL r θ₀ x₀ y₀ x₁ y₁ θc.
Proof.
  intros.
  specialize (ottb_parameters2_L_calc _ _ _ _ _ _ tmns rne0 phase Ldir) as
      calcLdef.
  change (calcL r θ₀ x₀ y₀ x₁ y₁ θc = calcL' r θ₀ x₀ y₀ x₁ y₁ θc) in calcLdef.
  set (Ldy := (y₁ - Hyarc r θ₀ y₀ (r * θc))) in *.
  set (Ldx := (x₁ - Hxarc r θ₀ x₀ (r * θc))) in *.
  set (L := sqrt (Ldy² + Ldx²)).
  change (calcL r θ₀ x₀ y₀ x₁ y₁ θc = L) in calcLdef.
  rewrite calcLdef.
  assert (0 <= L) as zleL.
  apply sqrt_pos.
  inversion_clear zleL as [zltL | zeqL]. assumption.

  exfalso.
  assert (0 <= (Ldy² + Ldx²)) as zlesum.
  apply Rplus_le_le_0_compat.
  apply Rle_0_sqr.
  apply Rle_0_sqr.
  symmetry in zeqL.
  generalize (sqrt_eq_0 _ zlesum zeqL) as sumeq0. intro.
  generalize (Rplus_sqr_eq_0_l _ _ sumeq0) as Ldyeq0. intro.
  rewrite Rplus_comm in sumeq0.
  generalize (Rplus_sqr_eq_0_l _ _ sumeq0) as Ldxeq0. intro.

  clear zeqL zlesum sumeq0.

  
  unfold straight, Tcx, Tcy in phase.

  unfold Ldy, Hyarc in Ldyeq0.
  assert ((y₁ - (y₀ + r * cos θ₀)) = - r * cos (r * θc / r + θ₀)) as yleg.
  apply (Rplus_eq_reg_l (r * cos (r * θc / r + θ₀))). setr 0.
  rewrite <- Ldyeq0. field.

  unfold Ldx, Hxarc in Ldxeq0.
  assert ((x₁ - (x₀ - r * sin θ₀)) = r * sin (r * θc / r + θ₀)) as xleg.
  apply (Rplus_eq_reg_l (- r * sin (r * θc / r + θ₀))). setr 0.
  rewrite <- Ldxeq0. field.
  rewrite cos_sin in yleg.
  rewrite sin_cos in xleg.
  rewrite yleg in phase.
  assert ((x₀ - r * - cos (PI / 2 + θ₀)) =
          (x₀ + r * cos (PI / 2 + θ₀))) as negneg. field.
  rewrite negneg in xleg. clear negneg.
  rewrite xleg in phase.
  assert ((r * sin (r * θc / r + θ₀))² + (- r * cos (r * θc / r + θ₀))² =
          r² * ((sin (r * θc / r + θ₀))² + (cos (r * θc / r + θ₀))²))
    as ident. unfold Rsqr. field. rewrite ident in phase.
  rewrite sin2_cos2 in phase.
  lra.
Qed.



Lemma straight_path_exists2_s :
  forall (x₁ y₁ r : R)
         (strt : straight r 0 0 0 x₁ y₁)
         (rne0 : r <> 0),
    let θc := θ1 x₁ y₁ r in
      (* ensure correct direction of linear path *)
    let Ldx := x₁ - Hxarc r 0 0 (r * θc) in
    let Ldy := y₁ - Hyarc r 0 0 (r * θc) in
    exists k : Z, atan2 Ldy Ldx = θc + 2 * IZR k * PI.
Proof.
  intros.

  assert (Hxarc r 0 0 (r*θc) = r * sin θc) as Hxarcdef. {
    unfold Hxarc. rewrite sin_0.
    fieldrewrite (r * θc / r + 0) (θc). assumption. field. }

  assert (Hyarc r 0 0 (r*θc) = r * (1-cos θc)) as Hyarcdef. {
    unfold Hyarc. rewrite cos_0.
    fieldrewrite (r * θc / r + 0) (θc). assumption. field. }
  
  unfold Ldx, Ldy.
  rewrite Hyarcdef, Hxarcdef.
  change (exists k, κ₂ x₁ y₁ r θc = θc + 2 * IZR k * PI).

  specialize (k2_theta1_even x₁ y₁ r rne0 strt) as [q k2def].
  change (κ₂ x₁ y₁ r θc = θc + 2 * IZR q * PI) in k2def.
  rewrite k2def.
  exists q. reflexivity.
Qed.


Lemma straight_path_exists2 :
  forall (x₀ y₀ θ₀ x₁ y₁ r: R)
         (phase : straight r θ₀ x₀ y₀ x₁ y₁)
         (rne0 : r <> 0),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    let θc := θ1 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
                 (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) r in
    (* ensure correct direction of linear path *)
    let Ldx := x₁ - Hxarc r θ₀ x₀ (r * θc) in
    let Ldy := y₁ - Hyarc r θ₀ y₀ (r * θc) in
    forall (tmaxne0 : θmax <> 0),
    exists k : Z, atan2 Ldy Ldx = θ₀ + θc + 2 * IZR k * PI.
Proof.
  intros.
  specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as notO.

  unfold Ldx, Ldy. clear Ldx Ldy.
  rewrite xxlate_arm, yxlate_arm.
  rewrite Hyarc_rot,  (Hxarc_rot r θ₀ θc). 

  apply straight_rot in phase.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  apply atan2_rot1_rot2.
  change (~ (x - Hxarc r 0 0 (r * θc) = 0 /\ y - Hyarc r 0 0 (r * θc)= 0)).

  unfold Hxarc, Hyarc.
  autorewrite with null.
  fieldrewrite (r * θc / r) (θc); 
    [assumption|].
  fieldrewrite (- r * cos θc + r) (r*(1 - cos θc)).
  intros [xd yd].
  apply Rminus_diag_uniq in xd.
  apply Rminus_diag_uniq in yd.
  apply straightcond in phase.
  rewrite xd, yd in phase.

  assert (2 < 2) as absurd. {
    assert (2 = 1 + 1) as id. field. rewrite id at 2. clear id.
    rewrite <- (sin2_cos2 θc) at 1.
    apply (Rmult_lt_reg_r r²). {
      specialize (Rle_0_sqr r) as des.
      destruct des. assumption.
      
      exfalso. apply rne0.
      apply (Rmult_eq_reg_r r); auto.
      setr 0. symmetry. assumption.
    }
    apply (Rplus_lt_reg_r (- 2 * r * r * cos θc)).
    setl (2 * r * (r * (1 - cos θc))).
    setr ((r * sin θc)² + (r * (1 - cos θc))²).
    assumption. }
  lra.

  change (exists q : Z,
             atan2 (y - Hyarc r 0 0 (r * θc))
                   (x - Hxarc r 0 0 (r * θc)) = θc + 2 * IZR q * PI).
  unfold θmax in tmaxne0.

  apply (straight_path_exists2_s _ _ _ phase rne0).
Qed.

Lemma ottb_r_thetac_ub2 :
  forall (θ₀ x₀ y₀ x₁ y₁ r:R)
         (phase : straight r θ₀ x₀ y₀ x₁ y₁)
         (rne0 : r <> 0),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    let θc := θ1 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
                 (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) r in
    forall (tmaxne : θmax <> 0),
    r * θc < Rabs r * 2 * PI.
Proof.
  intros.

  specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as nO.
  specialize (ottb_r_thetac_lb2 _ _ _ _ _ _ nO tmaxne rne0 phase) as rclb;
    unfold θc in rclb; change (0 < r * θc) in rclb.

  assert (- 2 * PI <= θmax <= 2 * PI) as [tmlb tmub]. {
    apply (notid_rot θ₀) in nO.
    unfold θmax,calcθ₁.
    specialize (atan2_bound _ _ nO) as [atl atu].
    lra. }
  assert (- 2 * PI < θc < 2 * PI) as [tclb tcub]. {
    unfold θc.
    apply straight_rot in phase.
    specialize (rotated_straight_path_equiv
                  x₀ y₀ θ₀ x₁ y₁ nO tmaxne) as nsno.
    specialize (theta1_rng _ _ _ rne0 phase) as [tcl tcu].
    split; lra. }

  unfold Rabs.
  destruct (Rcase_abs r).
  + assert (θc < 0). {
      apply (Rmult_lt_reg_r (-r));
        [lra| arn; lra]. }
    setl (- r * - θc).
    apply (Rmult_lt_reg_r (/ -r));
      [zltab; lra|
       setl (- θc); [ lra|];
       setr (2 * PI); [ lra|lra]].
  + destruct r0; try lra.
    apply (Rmult_lt_reg_r (/r));
      [zltab; lra |
       setl (θc); [ lra|];
       setr (2 * PI); [ lra|lra]].
Qed.

Lemma not_colinear_s :
  forall x y r θr stp Dr
         (P : path_segment Dr (Hx r 0 0 θr stp) (Hy r 0 0 θr stp)
                           (mkpt 0 0) (mkpt x y)),
    ~ (0 < x /\ y = 0).
Proof.
  intros.
  addzner.

  intros [zlex yeq0].
  inversion P.
  clear contx conty abnd pzbydist.
  injection bbnd.
  clear bbnd.
  intros Hyd Hxd.
  unfold Hy in Hyd.
  unfold Hx in Hxd.
  unfold extension_cont in *.
  destruct Rle_dec.
  + unfold Hxarc, Hyarc in Hyd, Hxd.
    autorewrite with null in *.
    assert (2 * r * y = x² + y²) as contr. {
      apply Rminus_diag_uniq.
      rewrite <- Hyd, <- Hxd.
      setl (r² * (1 - ((sin (Dr / r))² + (cos (Dr / r))²))).
      rewrite sin2_cos2.
      field. }
    rewrite yeq0 in *.
    autorewrite with null in contr.
    rewrite <- Rsqr_0 in contr.
    apply Rsqr_inj in contr; try lra.
  + unfold Hxlin, Hylin, Hxarc, Hyarc in *.
    autorewrite with null in *.
    assert (r * θr / r = θr) as id. {
      field. lra. } 
    rewrite id in *. clear id.
    destruct (Req_dec θr 0) as [treq0 | trne0].
    rewrite treq0 in *.
    autorewrite with null in rtpl.
    lra.
    rewrite <- Hyd in yeq0.
    rewrite <- Hxd in zlex.
    clear Hxd Hyd.
    destruct (total_order_T 0 r) as [[zltr| zeqr]| zgtr];
      [ | lra | ].
    -- destruct (total_order_T 0 (sin θr)) as [[zlts| zeqs]| zgts].
       ++ assert (0 < (Dr - r * θr) * sin θr) as pt. {
            zltab. }
          assert (0 <= (- r * cos θr + r)) as nnt. {
            specialize (COS_bound θr) as [clb cub].
            apply (Rmult_le_reg_r (/ r)).
            zltab.
            setl 0. lra.
            setr (- cos θr + 1). lra.
            lra. }
          assert (0 <= (Dr - r * θr) * sin θr + (- r * cos θr + r)) as ctr. {
            zltab. left. assumption. }
          lra.
       ++ rewrite <- zeqs in *.
          autorewrite with null in *.
          symmetry in zeqs.
          specialize PI_RGT_0 as pigt0.
          assert (2 * PI > 0) as tpigt0; [ lra|].
          
          specialize (inrange_mT2T2 θr _ tpigt0) as [k [tl tu]].
          rewrite <- Rmult_assoc, (Rmult_comm _ 2) in tl, tu.
          rewrite <- (sin_period1 _ k) in zeqs.
          apply sinθeq0 in zeqs; [|split; lra].
          destruct zeqs as [tr0 | trpi].
          +++ rewrite Rplus_comm in tr0.
              apply Rplus_opp_r_uniq in tr0.
              rewrite tr0, cos_neg in yeq0.
              rewrite <- (Rplus_0_l (2 * IZR k * PI)) in yeq0.
              rewrite cos_period1 in yeq0.
              destruct k.
              ++++ autorewrite with null in tr0.
                   lra.
              ++++ specialize (IZRposge1 p) as pord.
                   assert (θr < 0) as trlt0. {
                     rewrite tr0.
                     setr (-0).
                     apply Ropp_lt_contravar.
                     zltab. }
                   clear - zltr trlt0 rtpl.
                   generalize trlt0.
                   apply Rge_not_lt.
                   apply Rle_ge.
                   left.
                   apply (Rmult_lt_reg_l r).
                   assumption.
                   setl 0.
                   assumption.
                   
              ++++ specialize (IZRneglen1 p) as pord.
                   generalize rtpu.
                   apply Rle_not_lt.
                   rewrite Rabs_right; try lra.
                   apply (Rmult_le_reg_r (/ (2 * PI * r))).
                   zltab.
                   setl (1). lra.
                   rewrite tr0.
                   setr (- IZR (Z.neg p)). lra.
                   lra.
          +++ assert (θr = PI + 2 * IZR (- k) * PI) as td. {
                rewrite opp_IZR.
                apply (Rplus_eq_reg_r (2 * IZR k * PI)).
                setr PI.
                assumption. }
              clear trpi.
              rewrite td in yeq0.
              rewrite cos_period1 in yeq0.
              rewrite cos_PI in yeq0.
              lra. 
       ++ assert (Dr - r * θr = r * (1 - cos θr) / (- sin θr)) as drrt. {
            apply (Rmult_eq_reg_r (sin θr)).
            apply (Rplus_eq_reg_r (r * (1 - cos θr))).
            lrag yeq0.
            lra. }
          rewrite drrt in zlex.
          assert (0 <= 1 - cos θr) as nnd. {
            specialize (COS_bound θr) as [cl cu].
            lra. }
          apply Ropp_le_contravar in nnd.
          apply (Rmult_le_compat_l r) in nnd; [|lra].
          autorewrite with null in nnd.
          assert (0 < r * - (1 - cos θr)) as ctr. {
            rewrite <- (sin2_cos2 θr).
            apply (Rmult_lt_reg_r (/ - sin θr)).
            zltab. lra.
            setl 0. lra.
            setr ((r * (1 - cos θr) / - sin θr) * cos θr + r * sin θr).
            lra.
            assumption. }
          lra.
    -- destruct (total_order_T 0 (sin θr)) as [[zlts| zeqs]| zgts].
       ++ assert (Dr - r * θr = - r * (1 - cos θr) / (sin θr)) as drrt. {
            apply (Rmult_eq_reg_r (sin θr)).
            apply (Rplus_eq_reg_r (r * (1 - cos θr))).
            lrag yeq0.
            lra. }
          rewrite drrt in zlex.
          assert (0 <= 1 - cos θr) as nnd. {
            specialize (COS_bound θr) as [cl cu].
            lra. }
          apply Ropp_le_contravar in nnd.
          apply (Rmult_le_compat_l (- r)) in nnd; [|lra].
          autorewrite with null in nnd.
          rewrite Rmult_opp_opp in nnd.
          
          assert (0 < r * (1 - cos θr)) as ctr. {
            rewrite <- (sin2_cos2 θr).
            apply (Rmult_lt_reg_r (/ sin θr)).
            zltab.
            setl 0. lra.
            setr ((r * (1 - cos θr) / - sin θr) * cos θr + r * sin θr).
            lra.
            lrag zlex. }
          lra.
       ++ rewrite <- zeqs in *.
          autorewrite with null in *.
          assert (cos θr = 1) as ctr1. {
            apply (Rplus_eq_reg_r (-1)).
            apply (Rmult_eq_reg_r r).
            setr 0.
            lrag yeq0. lra. }
               
          specialize PI_RGT_0 as pigt0.
          assert (2 * PI > 0) as tpigt0; [ lra|].
          
          specialize (inrange_0T θr _ tpigt0) as [k [tl tu]].
          rewrite <- (cos_period1 _ k) in ctr1.
          apply cosθeq1 in ctr1; [|split; lra].
          rewrite Rplus_comm in ctr1.
          apply Rplus_opp_r_uniq in ctr1.
          rewrite ctr1, cos_neg in yeq0.
          rewrite <- (Rplus_0_l (2 * IZR k * PI)) in yeq0.
          rewrite cos_period1 in yeq0.
          destruct k.
          ++++ autorewrite with null in ctr1.
               lra.
          ++++ specialize (IZRposge1 p) as pord.
               generalize rtpu.
               apply Rle_not_lt.
               rewrite Rabs_left; try lra.
               apply (Rmult_le_reg_r (/ (2 * PI * - r))).
               zltab.
               setl (1). lra.
               rewrite ctr1.
               setr (IZR (Z.pos p)). lra.
               assumption.
          ++++ specialize (IZRneglen1 p) as pord.
               assert (0 < θr) as trlt0. {
                 rewrite ctr1.
                 setr (2 * - IZR (Z.neg p) * PI).
                 zltab. }
               clear - zgtr trlt0 rtpl.
               generalize trlt0.
               apply Rge_not_lt.
               apply Rle_ge.
               left.
               apply (Rmult_lt_reg_l (-r)).
               lra.
               setr (- 0).
               setl (- (r * θr)).
               apply Ropp_lt_contravar.
               assumption.
       ++ assert (Dr - r * θr = r * (1 - cos θr) / (- sin θr)) as drrt. {
            apply (Rmult_eq_reg_r (sin θr)).
            apply (Rplus_eq_reg_r (r * (1 - cos θr))).
            lrag yeq0.
            lra. }
          rewrite drrt in zlex.
          assert (0 <= 1 - cos θr) as nnd. {
            specialize (COS_bound θr) as [cl cu].
            lra. }
               apply Ropp_le_contravar in nnd.
          apply (Rmult_le_compat_l (-r)) in nnd; [|lra].
          autorewrite with null in nnd.
          rewrite Rmult_opp_opp in nnd.
          
          assert ((Dr - r * θr) * sin θr < 0) as pos.
          setl ( - ((Dr - r * θr) * - sin θr)).
          setr (-0).
          apply Ropp_lt_contravar.
          zltab.
          assert ((Dr - r * θr) * sin θr +
                  (- r * cos θr + r) < 0) as ctr. {
            setl (- (- ((Dr - r * θr) * sin θr) +
                     (- (r * (1 - cos θr))))).
            setr (-0).
            apply Ropp_lt_contravar.
            apply Rplus_le_lt_0_compat.
            lra.
            lra. }
          lra.
Qed.

Lemma npx_straight_s :
  forall x y r θr stp Dr
         (phaser : straight r 0 0 0 x y)
         (P : path_segment Dr (Hx r 0 0 θr stp) (Hy r 0 0 θr stp)
                           (mkpt 0 0) (mkpt x y)),
    ~ (0 <= x /\ y = 0).
Proof.
  intros.
  specialize (not_colinear_s _ _ _ _ _ _ P) as nc.
  intro ncno.
  apply nc.
  destruct ncno as [[zltx| zeqx] yeq0].
  + split; assumption.
  + apply straightcond in phaser.
    rewrite <- zeqx, yeq0 in phaser.
    autorewrite with null in phaser.
    lra.
Qed.

Lemma k_deriv_θ1_0 :
  forall x y r
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x y),
  sign (κ' x y r (θ1 x y r)) = 0.
Proof.
  intros.  
  apply (theta1_theta2_k_deriv _ _ _ _ 0%Z); try assumption.
  left. autorewrite with null.
  reflexivity.
Qed.

Lemma fct1 :
  forall x y r (phase : straight r 0 0 0 x y) (rne0 : r <> 0),
    (x - r * sin (θ1 x y r)) * sin (θ1 x y r) =
    (y - r * (1 - cos (θ1 x y r))) * cos (θ1 x y r).
Proof.
  intros.
  specialize (k_deriv_θ1_0 x y r rne0 phase) as k'eq0.
  set (t := (θ1 x y r)) in *.
  unfold κ' in k'eq0.
  rewrite sign_eq_pos_den in k'eq0.
  + apply straightcond in phase.
    rewrite signeq0_eqv in k'eq0.
    apply (Rmult_eq_reg_r (-r)).
    apply Rminus_diag_uniq.
    rewrite <- k'eq0.
    field.
    lra.

  + assert (~((x - r * sin t) = 0 /\ (y - r * (1 - cos t)) = 0)) as dne0. {
      intro noc. inversion_clear noc as [nox noy].
      assert (x = r * sin t) as x1cd. {
        apply (Rplus_eq_reg_r (- r * sin t)).
        setr 0. setl (x - r * sin t).
        assumption. }
      assert (y = r * (1-cos t)) as y1cd. {
        apply (Rplus_eq_reg_r (- r * (1 - cos t))).
        setr 0. setl (y - r * (1 - cos t)).
        assumption. }
      rewrite x1cd, y1cd in phase.
      assert (1 < 1) as c. {
        apply (Rmult_lt_reg_l (r²)).
        apply Rsqr_pos_lt ; assumption.
        rewrite <- (sin2_cos2 t) at 2.
        setr ((r * sin t)² + (r * (1 - cos t) - r)²). setl r².
        apply straight_std_impl_ineq in phase.
        assumption. }
      lra. }
    
    assert ((y - r * (1 - cos t))² + (x - r * sin t)² <> 0) as noc. {
      intro oc. apply dne0.
      split.
      eapply Rplus_sqr_eq_0. apply oc.
      rewrite Rplus_comm in oc.
      eapply Rplus_sqr_eq_0. apply oc. }
    specialize (Rle_0_sqr (y - r * (1 - cos t))) as yge0.
    specialize (Rle_0_sqr (x - r * sin t)) as xge0.
    specialize (Rplus_le_le_0_compat _ _ yge0 xge0) as xyge0.
    lra.
Qed.

Corollary fct2 :
  forall x y r (phase : straight r 0 0 0 x y) (rne0 : r <> 0),
    (r + (y - r) * cos (θ1 x y r) - x * sin (θ1 x y r)) = 0.
Proof.
  intros.
  rewrite <- (Rmult_1_r r) at 1.
  rewrite <- (sin2_cos2 (θ1 x y r)).
  setl ( (y - r * (1 - cos (θ1 x y r))) * cos (θ1 x y r) - (x - r * sin (θ1 x y r)) * sin (θ1 x y r)).
  rewrite fct1; auto.
  field.
Qed.

Lemma Darm_Q :
  forall x y r (phase : straight r 0 0 0 x y) (rne0 : r <> 0),
    (x - r * sin (θ1 x y r))² + (y - r * (1 - cos (θ1 x y r)))² =
    (x² - (2 * r - y) * y).
Proof.
  intros.
  specialize (k_deriv_θ1_0 x y r rne0 phase) as k'eq0.
  set (t := (θ1 x y r)) in *.
  setl (x² - (2 * r - y) * y +
        (2 * r * y * cos t + r² - 2 * r² * cos t + r² * (cos t)²
            - 2 * r * x * sin t + r² * (sin t)²)).
  rewrite <- (Rmult_1_r (r²)) at 1.
  rewrite <- (sin2_cos2 t).
  setl (x² - (2 * r - y) * y
        + 2 * r * ((y - r * (1 - cos t)) * cos t - (x - r * sin t) * sin t)).
  specialize (fct1 _ _ _ phase rne0) as id.
  symmetry in id.
  apply Rminus_diag_eq in id.
  change
    ((y - r * (1 - cos t)) * cos t - (x - r * sin t) * sin t = 0) in id.
  rewrite id.
  field.
Qed.

Lemma Darm_cos :
  forall x y r (phase : straight r 0 0 0 x y) (rne0 : r <> 0),
    sqrt ((x - r * sin (θ1 x y r))² +
          (y - r * (1 - cos (θ1 x y r)))²) * cos (θ1 x y r) =
    (x - r * sin (θ1 x y r)).
Proof.
  intros.
  set (t := (θ1 x y r)) in *.
  rewrite Rplus_comm.
  
  assert (Hxarc r 0 0 (r*t) = r * sin t) as Hxarcdef. {
    unfold Hxarc. rewrite sin_0.
    fieldrewrite (r * t / r + 0) (t). assumption. field. }
    
  assert (Hyarc r 0 0 (r*t) = r * (1-cos t)) as Hyarcdef. {
    unfold Hyarc. rewrite cos_0.
    fieldrewrite (r * t / r + 0) (t). assumption. field. }

  specialize (straight_path_exists2_s _ _ _ phase rne0) as at2.
  simpl in at2.
  destruct at2 as [m at2].
  change (atan2 (y - Hyarc r 0 0 (r * t)) (x - Hxarc r 0 0 (r * t)) = t + 2 * IZR m * PI) in at2.
  rewrite Hxarcdef, Hyarcdef in at2.
  unfold atan2 in at2.
  destruct (pre_atan2 (y - r * (1 - cos t)) (x - r * sin t)) as [α [arng [ydf xdf]]].
  set (M := sqrt ((y - r * (1 - cos t))² + (x - r * sin t)²)) in *.
  rewrite at2, cos_period1 in xdf.
  symmetry.
  assumption.
Qed.

Lemma Darm_sin :
  forall x y r (phase : straight r 0 0 0 x y) (rne0 : r <> 0),
    sqrt ((x - r * sin (θ1 x y r))² +
          (y - r * (1 - cos (θ1 x y r)))²) * sin (θ1 x y r) =
    (y - r * (1 - cos (θ1 x y r))).
Proof.
  intros.
  set (t := (θ1 x y r)) in *.
  rewrite Rplus_comm.
  
  assert (Hxarc r 0 0 (r*t) = r * sin t) as Hxarcdef. {
    unfold Hxarc. rewrite sin_0.
    fieldrewrite (r * t / r + 0) (t). assumption. field. }
    
  assert (Hyarc r 0 0 (r*t) = r * (1-cos t)) as Hyarcdef. {
    unfold Hyarc. rewrite cos_0.
    fieldrewrite (r * t / r + 0) (t). assumption. field. }

  specialize (straight_path_exists2_s _ _ _ phase rne0) as at2.
  simpl in at2.
  destruct at2 as [m at2].
  change (atan2 (y - Hyarc r 0 0 (r * t)) (x - Hxarc r 0 0 (r * t)) = t + 2 * IZR m * PI) in at2.
  rewrite Hxarcdef, Hyarcdef in at2.
  unfold atan2 in at2.
  destruct (pre_atan2 (y - r * (1 - cos t)) (x - r * sin t)) as [α [arng [ydf xdf]]].
  set (M := sqrt ((y - r * (1 - cos t))² + (x - r * sin t)²)) in *.
  rewrite at2, sin_period1 in ydf.
  symmetry.
  assumption.
Qed.


Lemma Darm_simpl :
  forall x y r (phase : straight r 0 0 0 x y) (rne0 : r <> 0),
    sqrt ((x - r * sin (θ1 x y r))² +
          (y - r * (1 - cos (θ1 x y r)))²) =
    x * cos (θ1 x y r) + (y - r) * sin (θ1 x y r).
Proof.
  intros.
  rewrite <- Rmult_1_r at 1.
  rewrite <- (sin2_cos2 (θ1 x y r)) at 2.
  rewrite Rmult_plus_distr_l.
  unfold Rsqr at 3; unfold Rsqr at 5.
  repeat rewrite <- Rmult_assoc.
  rewrite Darm_cos, Darm_sin; auto.
  field.
Qed.

(* end hide *)

Lemma Darm_Q_gen :
  forall θ₀ x₀ y₀ x₁ y₁ r (phase : straight r θ₀ x₀ y₀ x₁ y₁) (rne0 : r <> 0),
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    (x - r * sin (θ1 x y r))² + (y - r * (1 - cos (θ1 x y r)))² =
    (x² - (2 * r - y) * y).
Proof.
  intros.
  apply straight_rot in phase.
  change (straight r 0 0 0 x y) in phase.
  apply Darm_Q; assumption.
Qed.

Lemma Darm_cos_gen :
  forall θ₀ x₀ y₀ x₁ y₁ r (phase : straight r θ₀ x₀ y₀ x₁ y₁) (rne0 : r <> 0),
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    sqrt ((x - r * sin (θ1 x y r))² +
          (y - r * (1 - cos (θ1 x y r)))²) * cos (θ1 x y r) =
    (x - r * sin (θ1 x y r)).
Proof.
  intros.
  intros.
  apply straight_rot in phase.
  change (straight r 0 0 0 x y) in phase.
  apply Darm_cos; assumption.
Qed.

Lemma Darm_sin_gen :
  forall θ₀ x₀ y₀ x₁ y₁ r (phase : straight r θ₀ x₀ y₀ x₁ y₁) (rne0 : r <> 0),
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    sqrt ((x - r * sin (θ1 x y r))² +
          (y - r * (1 - cos (θ1 x y r)))²) * sin (θ1 x y r) =
    (y - r * (1 - cos (θ1 x y r))).
Proof.
  intros.
  apply straight_rot in phase.
  change (straight r 0 0 0 x y) in phase.
  apply Darm_sin; assumption.
Qed.


Lemma Darm_simpl_gen :
  forall θ₀ x₀ y₀ x₁ y₁ r (phase : straight r θ₀ x₀ y₀ x₁ y₁) (rne0 : r <> 0),
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    sqrt ((x - r * sin (θ1 x y r))² +
          (y - r * (1 - cos (θ1 x y r)))²) =
    x * cos (θ1 x y r) + (y - r) * sin (θ1 x y r).
Proof.
  intros.
  apply straight_rot in phase.
  change (straight r 0 0 0 x y) in phase.
  apply Darm_simpl; assumption.
Qed.


(* begin hide *)

Lemma turningcond : forall x y r,
    turning r 0 0 0 x y -> 2 * r * y = x² + y².
Proof.
  intros * trn.
  unfold turning, Tcx, Tcy in trn.
  autorewrite with null in trn.
  rewrite Rsqr_minus in trn.
  lra.
Qed.
  
Lemma tscond : forall x y r,
    turning r 0 0 0 x y \/ straight r 0 0 0 x y ->
    2 * r * y <= x² + y².
Proof.
  intros * [trn | str].
  apply turningcond in trn; right; assumption.
  apply straightcond in str; left; assumption.
Qed.

Lemma theta1_Q1_ex_derive :
  forall r x y 
         (phase : straight r 0 0 0 x y)
         (rgt0 : 0 < r)
         (xgt0 : 0 < x)
         (ygt0 : 0 <= y),
    let θ1_alt := (fun r => 2 * atan (y * /(x + sqrt (x² - (2 * r - y) * y)))) in
    let θ1_Q1 := (θ1 x y) in
    ex_derive θ1_Q1 r.
Proof.
  intros.
  apply straightcond in phase.

  assert (locally r (fun t => θ1_alt t = θ1_Q1 t)) as P0.
  { unfold locally, ball; simpl; unfold AbsRing_ball, minus, plus, opp; simpl.
    assert (0 < (Rmin r (if (Rlt_le_dec 0 y) then ((x² + y²)*/(2*y) - r) else r))) as Q1.
    { apply Rmin_glb_lt; auto.
      destruct Rlt_le_dec; auto.
      apply Rlt_Rminus, (Rmult_lt_reg_r (2 * y));[lra|].
      rewrite Rmult_assoc, Rinv_l; lra.
    }
    exists (mkposreal _ Q1); simpl; intros val Hball.
    apply Rabs_def2 in Hball as [P1 P2].
    assert (0 < val) as Q2.
    { unfold minus, plus, opp in P2; simpl in P2.
      rewrite <- Rmax_opp_Rmin in P2.
      apply Rmax_Rlt in P2 as [P2 P3]; lra.
    }
    assert (straight val 0 0 0 x y) as Q3.
    { apply condstraight.
      unfold minus, plus, opp in P1; simpl in P1.
      apply Rmin_def in P1 as [P1 P3].
      destruct Rlt_le_dec.
      - setl (val * ( 2 * y)).
        apply (Rmult_lt_reg_r (/(2 * y)));
          [apply Rinv_0_lt_compat; lra|].
        rewrite Rmult_assoc, Rinv_r; lra.
      - destruct (Rle_lt_or_eq_dec _ _ r0) as [ylt | yeq].
        + apply Rlt_trans with (r2 := 0).
          * setl (-((2 * val) * (-y))).
            setr (-0).
            apply Ropp_lt_contravar.
            repeat apply Rmult_lt_0_compat; lra.
          * apply Rplus_le_lt_0_compat; [apply Rle_0_sqr| apply Rsqr_pos_lt; lra].
        + rewrite yeq, Rmult_0_r in *; assumption.
    }
    unfold θ1_alt, θ1_Q1, θ1.
    destruct total_order_T;[destruct s|]; try lra.
    destruct total_order_T;[destruct s|]; try lra.
    destruct total_order_T;[destruct s|]; try lra.
    destruct total_order_T;[destruct s|].
    - assert (0 < (x + sqrt (x² - (2 * val - y) * y))) as P3.
      { apply Rplus_lt_le_0_compat;[auto |apply sqrt_pos]. }
      apply Rmult_eq_compat_l, f_equal, (Rmult_eq_reg_l (x + sqrt (x² - (2 * val - y) * y)));[|lra].
      rewrite <- Rmult_assoc, Rinv_r_simpl_m; [|lra].
      setr ((x² - (sqrt (x² - (2 * val - y) * y))²) * /(2 * val - y)); try lra.
      rewrite Rsqr_sqrt; try field; try lra.
      apply straightcond in Q3.
      setr (x² + y² - 2 * val * y); lra.
    - rewrite <- e, Rmult_0_l, Rminus_0_r, sqrt_Rsqr, (double x) ;[reflexivity|lra].    
    - assert (0 < (x + sqrt (x² - (2 * val - y) * y))) as P3.
      { apply Rplus_lt_le_0_compat;[auto |apply sqrt_pos]. }
      apply Rmult_eq_compat_l, f_equal, (Rmult_eq_reg_l (x + sqrt (x² - (2 * val - y) * y)));[|lra].
      rewrite <- Rmult_assoc, Rinv_r_simpl_m; [|lra].
      setr ((x² - (sqrt (x² - (2 * val - y) * y))²) * /(2 * val - y)); try lra.
      rewrite Rsqr_sqrt; try field; try lra.
      apply straightcond in Q3.
      setr (x² + y² - 2 * val * y); lra.
    - rewrite <- e, Rmult_0_l, atan_0.
      field.
  }
  eapply ex_derive_ext_loc; eauto.
  unfold θ1_alt.
  auto_derive; repeat split; auto.
  + setr (x² + y² - 2 * r * y); lra.
  + intro.
    specialize (Rplus_lt_le_0_compat _ (sqrt (x² + - ((2 * r + - y) * y))) xgt0 (sqrt_pos _)) as CTRD.
    lra.
Qed.

Lemma theta1_Q34_ex_derive :
  forall r x y 
         (phase : straight r 0 0 0 x y)
         (rgt0 : 0 < r)
         (ygt0 : y < 0),
    let θ1_alt := (fun r => 2 * atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y)) +
                            2 * (IZR 1) * PI) in
    let θ1_Q34 := (θ1 x y) in
    ex_derive θ1_Q34 r.
Proof.
  intros.
  assert (locally r (fun t => θ1_alt t = θ1_Q34 t)) as P0.
  { unfold locally, ball; simpl; unfold AbsRing_ball, minus, plus, opp; simpl.
    assert (0 < (Rmin r (if (Rlt_le_dec 0 y) then ((x² + y²)*/(2*y) - r) else r))) as Q1.
    { apply Rmin_glb_lt; auto.
      destruct Rlt_le_dec; auto.
      apply straightcond in phase.
      apply Rlt_Rminus, (Rmult_lt_reg_r (2 * y));[lra|].
      rewrite Rmult_assoc, Rinv_l; lra.
    }
    exists (mkposreal _ Q1); simpl; intros val Hball.
    apply Rabs_def2 in Hball as [P1 P2].
    assert (0 < val) as Q2.
    { unfold minus, plus, opp in P2; simpl in P2.
      rewrite <- Rmax_opp_Rmin in P2.
      apply Rmax_Rlt in P2 as [P2 P3]; lra.
    }
    assert (straight val 0 0 0 x y) as Q3.
    { apply condstraight.
      unfold minus, plus, opp in P1; simpl in P1.
      apply Rmin_def in P1 as [P1 P3].
      destruct Rlt_le_dec.
      - setl (val * ( 2 * y)).
        apply (Rmult_lt_reg_r (/(2 * y)));
          [apply Rinv_0_lt_compat; lra|].
        rewrite Rmult_assoc, Rinv_r; lra.
      - apply straightcond in phase.
        destruct (Rle_lt_or_eq_dec _ _ r0) as [ylt | yeq].
        + apply Rlt_trans with (r2 := 0).
          * setl (-((2 * val) * (-y))).
            setr (-0).
            apply Ropp_lt_contravar.
            repeat apply Rmult_lt_0_compat; lra.
          * apply Rplus_le_lt_0_compat; [apply Rle_0_sqr| apply Rsqr_pos_lt; lra].
        + rewrite yeq, Rmult_0_r in *; assumption.
    }
    unfold θ1_alt, θ1_Q34, θ1.
    destruct total_order_T;[destruct s|]; try lra.
    destruct total_order_T;[destruct s|].
    - destruct total_order_T;[destruct s|]; try lra.
    - destruct total_order_T;[destruct s|]; try lra.
    - destruct total_order_T;[destruct s|]; try lra.
  }
  eapply ex_derive_ext_loc; eauto.
  unfold θ1_alt.
  auto_derive; repeat split; auto.
  + apply straightcond in phase.
    setr (x² + y² - 2 * r * y); lra.
  + intro.
    lra.
Qed.

Lemma theta1_py_ex_derive :
  forall r x y 
         (phase : straight r 0 0 0 x y)
         (rgt0 : 0 < r)
         (xeq0 : x = 0)
         (ygt0 : 0 < y),
    let θ1_alt := (fun r => 2 * atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))) in
    let θ1_py := (θ1 x y) in
    ex_derive θ1_py r.
Proof.
  intros.
  assert (locally r (fun t => θ1_alt t = θ1_py t)) as P0.
  { unfold locally, ball; simpl; unfold AbsRing_ball, minus, plus, opp; simpl.
    assert (0 < (Rmin r (if (Rlt_le_dec 0 y) then ((x² + y²)*/(2*y) - r) else r))) as Q1.
    { apply Rmin_glb_lt; auto.
      destruct Rlt_le_dec; auto.
      apply straightcond in phase.
      apply Rlt_Rminus, (Rmult_lt_reg_r (2 * y));[lra|].
      rewrite Rmult_assoc, Rinv_l; lra.
    }
    exists (mkposreal _ Q1); simpl; intros val Hball.
    apply Rabs_def2 in Hball as [P1 P2].
    assert (0 < val) as Q2.
    { unfold minus, plus, opp in P2; simpl in P2.
      rewrite <- Rmax_opp_Rmin in P2.
      apply Rmax_Rlt in P2 as [P2 P3]; lra.
    }
    assert (straight val 0 0 0 x y) as Q3.
    { apply condstraight.
      unfold minus, plus, opp in P1; simpl in P1.
      apply Rmin_def in P1 as [P1 P3].
      destruct Rlt_le_dec.
      - setl (val * ( 2 * y)).
        apply (Rmult_lt_reg_r (/(2 * y)));
          [apply Rinv_0_lt_compat; lra|].
        rewrite Rmult_assoc, Rinv_r; lra.
      - apply straightcond in phase.
        destruct (Rle_lt_or_eq_dec _ _ r0) as [ylt | yeq].
        + apply Rlt_trans with (r2 := 0).
          * setl (-((2 * val) * (-y))).
            setr (-0).
            apply Ropp_lt_contravar.
            repeat apply Rmult_lt_0_compat; lra.
          * apply Rplus_le_lt_0_compat; [apply Rle_0_sqr| apply Rsqr_pos_lt; lra].
        + rewrite yeq, Rmult_0_r in *; assumption.
    }
    unfold θ1_alt, θ1_py, θ1.
    destruct total_order_T;[destruct s|]; try lra.
    destruct total_order_T;[destruct s|]; try lra.
    destruct total_order_T;[destruct s|]; try lra.
    destruct total_order_T;[destruct s|]; try lra.
    exfalso.
    apply straightcond in Q3.
    rewrite <- e, Rsqr_0, Rplus_0_l in Q3.
    symmetry in e0.
    apply Rminus_diag_uniq in e0.
    rewrite e0 in Q3.
    unfold Rsqr in Q3. clear - Q3. lra.
  }
  eapply ex_derive_ext_loc; eauto.
  unfold θ1_alt.
  auto_derive; repeat split; auto.
  + apply straightcond in phase.
    setr (x² + y² - 2 * r * y); lra.
  + intro.
    apply straightcond in phase.
    rewrite xeq0, Rsqr_0, Rplus_0_l in phase.
    apply Rminus_diag_uniq in H.
    rewrite H in phase.
    unfold Rsqr in phase. clear - phase. lra.
Qed.

Lemma theta1_Q2_ex_derive :
  forall r x y 
         (phase : straight r 0 0 0 x y)
         (rgt0 : 0 < r)
         (xgt0 : x < 0)
         (ygt0 : 0 <= y),
    let θ1_alt := (fun r => 2 * (PI / 2
                            - atan ((2 * r - y)
                                      / (x - sqrt (x² - (2 * r - y) * y))))) in
    let θ1_Q2 := (θ1 x y) in
    ex_derive θ1_Q2 r.
Proof.  
  intros.
  assert (locally r (fun t => θ1_alt t = θ1_Q2 t)) as P0.
  { unfold locally, ball; simpl; unfold AbsRing_ball, minus, plus, opp; simpl.
    assert (0 < (Rmin r (if (Rlt_le_dec 0 y) then ((x² + y²)*/(2*y) - r) else r))) as Q1.
    { apply Rmin_glb_lt; auto.
      destruct Rlt_le_dec; auto.
      apply straightcond in phase.
      apply Rlt_Rminus, (Rmult_lt_reg_r (2 * y));[lra|].
      rewrite Rmult_assoc, Rinv_l; lra.
    }
    exists (mkposreal _ Q1); simpl; intros val Hball.
    apply Rabs_def2 in Hball as [P1 P2].
    assert (0 < val) as Q2.
    { unfold minus, plus, opp in P2; simpl in P2.
      rewrite <- Rmax_opp_Rmin in P2.
      apply Rmax_Rlt in P2 as [P2 P3]; lra.
    }
    assert (straight val 0 0 0 x y) as Q3.
    { apply condstraight.
      unfold minus, plus, opp in P1; simpl in P1.
      apply Rmin_def in P1 as [P1 P3].
      destruct Rlt_le_dec.
      - setl (val * ( 2 * y)).
        apply (Rmult_lt_reg_r (/(2 * y)));
          [apply Rinv_0_lt_compat; lra|].
        rewrite Rmult_assoc, Rinv_r; lra.
      - apply straightcond in phase.
        destruct (Rle_lt_or_eq_dec _ _ r0) as [ylt | yeq].
        + apply Rlt_trans with (r2 := 0).
          * setl (-((2 * val) * (-y))).
            setr (-0).
            apply Ropp_lt_contravar.
            repeat apply Rmult_lt_0_compat; lra.
          * apply Rplus_le_lt_0_compat; [apply Rle_0_sqr| apply Rsqr_pos_lt; lra].
        + rewrite yeq, Rmult_0_r in *; assumption.
    }
    assert ((x - sqrt (x² - (2 * val - y) * y)) < 0) as nn. {
      specialize (sqrt_pos (x² - (2 * val - y) * y)) as sqp.
      lra. }
    unfold θ1_alt, θ1_Q2, θ1.
    
    destruct total_order_T;[destruct s|]; try lra.
    destruct total_order_T;[destruct s|]; try lra.
    destruct total_order_T;[destruct s|]; try lra.
    destruct total_order_T;[destruct s|].
    - fieldrewrite ((2 * val - y) / (x - sqrt (x² - (2 * val - y) * y)))
                   ((- (2 * val - y)) / (- (x - sqrt (x² - (2 * val - y) * y)))).
      fold (Rsqr x).
      lra.
      rewrite <- atan2_atan_Q1Q2 ;[|lra].
      rewrite atan2_atan_Q2; [|lra|lra].
      fieldrewrite ((- (x - sqrt (x² - (2 * val - y) * y)))/(- (2 * val - y)))
                 ((x - sqrt (x² - (2 * val - y) * y))/ (2 * val - y)).
      lra.
      lra.
    - fieldrewrite ((2 * val - y) / (x - sqrt (x² - (2 * val - y) * y)))
                   ((- (2 * val - y)) / (- (x - sqrt (x² - (2 * val - y) * y)))).
      fold (Rsqr x). lra.
      rewrite <- atan2_atan_Q1Q2; [|lra].
      symmetry in e.
      rewrite e in *.
      rewrite Ropp_0, Rmult_0_l, Rminus_0_r.
      rewrite sqrt_Rsqr_abs.
      rewrite Rabs_left; [|lra].
      fieldrewrite (- (x - - x)) (- (2 * x)).
      rewrite atan2_PI2;[ field |lra].
      - fieldrewrite ((2 * val - y) / (x - sqrt (x² - (2 * val - y) * y)))
                     ((- (2 * val - y)) / (- (x - sqrt (x² - (2 * val - y) * y)))).
        fold (Rsqr x).
        lra.
        rewrite <- atan2_atan_Q1Q2; [|lra].
        rewrite atan2_atan_Q1; [|lra|lra].
        fieldrewrite ((- (x - sqrt (x² - (2 * val - y) * y)))/(- (2 * val - y)))
                     ((x - sqrt (x² - (2 * val - y) * y))/ (2 * val - y)).
        lra.
        lra.
      - fieldrewrite ((2 * val - y) / (x - sqrt (x² - (2 * val - y) * y)))
                     ((- (2 * val - y)) / (- (x - sqrt (x² - (2 * val - y) * y)))).
        fold (Rsqr x).
        lra.
        rewrite <- atan2_atan_Q1Q2; [|lra].
        rewrite <- e, Rmult_0_r, Rminus_0_r, Rminus_0_r.
        rewrite atan2_atan_Q2; [|lra|].
        fieldrewrite (- (x - sqrt x²) / - (2 * val)) ((x - sqrt x²) / (2 * val)).
        lra.
        lra.
        rewrite sqrt_Rsqr_abs.
        rewrite Rabs_left; [|lra].
        lra.
  }

  eapply ex_derive_ext_loc; eauto.
  unfold θ1_alt.
  auto_derive; repeat split; auto.
  + apply straightcond in phase.
    setr (x² + y² - 2 * r * y); lra.
  +  assert ((x + - sqrt (x² + - ((2 * r + - y) * y))) < 0) as nn. {
       specialize (sqrt_pos (x² + - ((2 * r + - y) * y))) as sqp.
       lra. }
     lra.
Qed.

Lemma theta1_ex_derive_posr :
  forall r x y 
         (phase : straight r 0 0 0 x y)
         (rgt0 : 0 < r),
    ex_derive (θ1 x y) r.
Proof.
  intros.
  destruct (Rle_lt_dec 0 y).
  destruct (total_order_T 0 x); [destruct s|].
  apply theta1_Q1_ex_derive; try assumption.
  apply theta1_py_ex_derive; try auto.
  apply straightcond in phase.
  destruct r0. assumption.
  rewrite <- e, <- H, Rmult_0_r, Rsqr_0, Rplus_0_r in phase.
  lra.
  apply theta1_Q2_ex_derive; try assumption.
  apply theta1_Q34_ex_derive; try assumption.
Qed.
(* end hide *)

Lemma theta1_ex_derive_posr_gen :
  forall θ₀ x₀ y₀ x₁ y₁ r (phase : straight r θ₀ x₀ y₀ x₁ y₁) (rgt0 : 0 < r),
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    ex_derive (θ1 x y) r.
Proof.
  intros.
  apply straight_rot in phase.
  change (straight r 0 0 0 x y) in phase.
  apply theta1_ex_derive_posr; assumption.
Qed.

(* begin hide *)
Lemma Darm_deriv_s :
  forall x y r
         (phase : straight r 0 0 0 x y)
         (rgt0 : 0 < r),
    is_derive (fun s : R => (sqrt ((x - s * sin (θ1 x y s))² +
                          (y - s * (1 - cos (θ1 x y s)))²))) r
              (-sin (θ1 x y r) + ((y - r) * cos (θ1 x y r) - x * sin (θ1 x y r)) * Derive (θ1 x y) r).
Proof.
  intros.
  specialize (theta1_ex_derive_posr _ _ _ phase rgt0 ) as t1pe.
  set (θ' := (Derive (θ1 x y))) in *.
  set (θ := (θ1 x y)) in *.

  assert ((fun x0 : R => θ x0) = θ) as id. {
    apply functional_extensionality. auto. }
  assert (Derive θ = θ') as id2. unfold θ'. reflexivity.

  set (D1 := (fun r => sqrt ((x - r * sin (θ r))² +
                             (y - r * (1 - cos (θ r)))²))) in *.
  set (D2 := (fun r => x * cos (θ r) + (y - r) * sin (θ r))).
  assert (is_derive D2 r (-sin (θ r) + ((y - r) * cos (θ r) - x * sin (θ r)) * θ' r)).
  { unfold D2.
    auto_derive; auto.
    rewrite id, id2.
    field.
  }
  eapply is_derive_ext_loc; eauto; simpl.
  unfold locally, ball; simpl; unfold AbsRing_ball, minus, plus, opp; simpl.
  assert (0 < (Rmin r (if (Rlt_le_dec 0 y) then ((x² + y²)*/(2*y) - r) else r))) as Q1.
  { apply Rmin_glb_lt; auto.
    destruct Rlt_le_dec; auto.
    apply straightcond in phase.
    apply Rlt_Rminus, (Rmult_lt_reg_r (2 * y));[lra|].
    rewrite Rmult_assoc, Rinv_l; lra.
  }
  exists (mkposreal _ Q1); simpl; intros val Hball.
  apply Rabs_def2 in Hball as [P1 P2].
  assert (0 < val) as Q2.
  { unfold minus, plus, opp in P2; simpl in P2.
    rewrite <- Rmax_opp_Rmin in P2.
    apply Rmax_Rlt in P2 as [P2 P3]; lra.
  }
  assert (straight val 0 0 0 x y) as Q3.
  { apply condstraight.
    unfold minus, plus, opp in P1; simpl in P1.
    apply Rmin_def in P1 as [P1 P3].
    destruct Rlt_le_dec.
    - setl (val * ( 2 * y)).
      apply (Rmult_lt_reg_r (/(2 * y)));
        [apply Rinv_0_lt_compat; lra|].
      rewrite Rmult_assoc, Rinv_r; lra.
    - apply straightcond in phase.
      destruct (Rle_lt_or_eq_dec _ _ r0) as [ylt | yeq].
      + apply Rlt_trans with (r2 := 0).
        * setl (-((2 * val) * (-y))).
          setr (-0).
          apply Ropp_lt_contravar.
          repeat apply Rmult_lt_0_compat; lra.
        * apply Rplus_le_lt_0_compat; [apply Rle_0_sqr| apply Rsqr_pos_lt; lra].
      + rewrite yeq, Rmult_0_r in *; assumption.
  }
  unfold D1, D2, θ.
  symmetry.
  apply Darm_simpl; auto.
  intro; lra.
Qed.

Lemma path_dist_deriv_s :
  forall x y r
         (phase : straight r 0 0 0 x y)
         (rgt0 : 0 < r),
    Derive (θ1 x y) r * (x - r * sin (θ1 x y r)) =
     cos (θ1 x y r) - (cos (θ1 x y r))².
Proof.
  intros.
  specialize (theta1_ex_derive_posr _ _ _ phase rgt0 ) as t1pe.
  set (θ' := (Derive (θ1 x y))) in *.
  set (θ := (θ1 x y)) in *.

  assert ((fun x0 : R => θ x0) = θ) as id. {
    apply functional_extensionality. auto. }
  assert (Derive θ = θ') as id2. unfold θ'. reflexivity.

  assert (is_derive (fun r:R => (x - r * sin (θ r)) * sin (θ r)) r
                    ((x - (r * sin (θ r))) * (θ' r * cos (θ r))
                     - (sin (θ r) + r * (θ' r * cos (θ r))) * sin (θ r))) as xad. {
    auto_derive.
    rewrite id.
    repeat split; auto.
    rewrite id.
    rewrite id2.
    field. }

  assert (is_derive (fun r:R => (y - r * (1 - cos (θ r))) * cos (θ r)) r
                    ((y - (r * (1 - cos (θ r)))) * (θ' r * - sin (θ r))
                     - ((1 - cos (θ r)) + r * (θ' r * sin (θ r))) * cos (θ r))) as yad. {
    auto_derive.
    rewrite id.
    repeat split; auto.
    rewrite id.
    rewrite id2.
    field. }
  assert (r <> 0) as rne0. lra.
  specialize (fct1 _ _ _ phase rne0) as fct1'.
  assert (θ1 x y = θ) as id3. unfold θ. reflexivity.
  rewrite id3 in fct1'.
  change ((fun r => (x - r * sin (θ r)) * sin (θ r)) r =
          (fun r => (y - r * (1 - cos (θ r))) * cos (θ r)) r) in fct1'.
  set (fy := (fun r => (y - r * (1 - cos (θ r))) * cos (θ r))) in *.
  set (fx := (fun r => (x - r * sin (θ r)) * sin (θ r))) in *.
  apply is_derive_unique in xad.
  apply is_derive_unique in yad.
  assert (locally r (fun t => fy t = fx t)) as lfe.
  { unfold locally.
    assert (0 < (Rmin r (if (Rlt_le_dec 0 y) then ((x² + y²)*/(2*y) - r) else r))) as Q1.
    { apply Rmin_glb_lt; auto.
      destruct Rlt_le_dec; auto.
      apply straightcond in phase.
      apply Rlt_Rminus, (Rmult_lt_reg_r (2 * y));[lra|].
      rewrite Rmult_assoc, Rinv_l; lra.
    }
    exists (mkposreal _ Q1); simpl; intros val Hball.
    unfold ball in Hball; simpl in *; unfold AbsRing_ball in Hball.
    apply Rabs_def2 in Hball as [P1 P2].
    assert (0 < val) as Q2.
    { unfold minus, plus, opp in P2; simpl in P2.
      rewrite <- Rmax_opp_Rmin in P2.
      apply Rmax_Rlt in P2 as [P2 P3]; lra.
    }
    assert (straight val 0 0 0 x y) as Q3.
    { apply condstraight.
      unfold minus, plus, opp in P1; simpl in P1.
      apply Rmin_def in P1 as [P1 P3].
      destruct Rlt_le_dec.
      - setl (val * ( 2 * y)).
        apply (Rmult_lt_reg_r (/(2 * y)));
        [apply Rinv_0_lt_compat; lra|].
        rewrite Rmult_assoc, Rinv_r; lra.
      - apply straightcond in phase.
        destruct (Rle_lt_or_eq_dec _ _ r0) as [ylt | yeq].
        + apply Rlt_trans with (r2 := 0).
          * setl (-((2 * val) * (-y))).
            setr (-0).
            apply Ropp_lt_contravar.
            repeat apply Rmult_lt_0_compat; lra.
          * apply Rplus_le_lt_0_compat; [apply Rle_0_sqr| apply Rsqr_pos_lt; lra].
        + rewrite yeq, Rmult_0_r in *; assumption.
    }
    unfold fy, fx, θ.
    symmetry.
    apply fct1; auto.
    lra.
  } 
  specialize (Derive_ext_loc _ _ _ lfe) as de.
  rewrite xad, yad in de.
  assert (θ' r * ((x  - r * sin (θ r)) * (cos (θ r))² +
                  (y - r * (1 - cos (θ r))) * cos (θ r) * sin (θ r)) =
          ((sin (θ r))² + (cos (θ r))² - cos (θ r)) * cos (θ r)) as Q1.
  { apply (Rplus_eq_reg_r (((-2 * r * sin (θ r) * cos (θ r) -
                            (y - r) * sin (θ r)) * θ' r - (sin (θ r))²) * cos (θ r))).
    setr (((y - r * (1 - cos (θ r))) * (θ' r * - sin (θ r)) -
          (1 - cos (θ r) + r * (θ' r * sin (θ r))) * cos (θ r)) * cos (θ r)).
    setl (((x - r * sin (θ r)) * (θ' r * cos (θ r)) - (sin (θ r) +
                 r * (θ' r * cos (θ r))) * sin (θ r)) * cos (θ r)).
    symmetry; apply Rmult_eq_compat_r; assumption.
  }
  unfold fx, fy in fct1'.
  rewrite <- fct1', Rmult_assoc, <- Rmult_plus_distr_l, Rplus_comm, sin2_cos2 in Q1;
    fold (Rsqr (sin (θ r))) in Q1.
  rewrite sin2_cos2, Rmult_1_r, Rmult_minus_distr_r, Rmult_1_l in Q1.
  assumption.
Qed.

Lemma full_path_dist_deriv_s :
  forall x y r
         (phase : straight r 0 0 0 x y)
         (rgt0 : 0 < r),
    Derive (fun s => s * (θ1 x y) s + (sqrt ((x - s * sin (θ1 x y s))² +
                                             (y - s * (1 - cos (θ1 x y s)))²))) r =
    ((θ1 x y r) - sin (θ1 x y r)).
Proof.
  intros.
  specialize (theta1_ex_derive_posr _ _ _ phase rgt0 ) as t1pe.

  set (θ' := (Derive (θ1 x y))) in *.
  set (θ := (θ1 x y)) in *.

  assert ((fun x0 : R => θ x0) = θ) as id. {
    apply functional_extensionality. auto. }
  assert (Derive θ = θ') as id2. unfold θ'. reflexivity.

  rewrite Derive_plus;
    [rewrite Derive_mult, Derive_id, Rmult_1_l; auto; try auto_derive; auto
    |auto_derive; rewrite id; assumption
    | auto_derive; rewrite id; repeat split; auto].
  + unfold θ, θ'.
    rewrite (is_derive_unique _ _ _ (Darm_deriv_s _ _ _ phase rgt0)).
    setl ( θ1 x y r - sin (θ1 x y r) +
           ((r + (y - r) * cos (θ1 x y r) - x * sin (θ1 x y r)) * Derive (θ1 x y) r)).
    rewrite fct2; auto; lra.
  + specialize (str_noton _ _ _ phase (θ r)) as Q1.
    specialize (Rplus_le_le_0_compat (x + - (r * sin (θ r)))²
                                     (y + - (r * (1 + - cos (θ r))))²
                                     (Rle_0_sqr _) (Rle_0_sqr _)) as Q2.
    destruct (Rle_lt_or_eq_dec _ _ Q2) as [Q3 | Q3]; [assumption|].
    apply eq_sym, Rplus_sqr_eq_0 in Q3; contradiction.
Qed.
  
Lemma full_path_dist_ex_derive_s :
  forall x y r
         (phase : straight r 0 0 0 x y)
         (rgt0 : 0 < r),
    ex_derive (fun s => s * (θ1 x y) s + (sqrt ((x - s * sin (θ1 x y s))² +
                                                (y - s * (1 - cos (θ1 x y s)))²))) r.
Proof.
  intros.
  specialize (theta1_ex_derive_posr _ _ _ phase rgt0 ) as t1pe.

  intros; auto_derive; repeat split; auto.
  specialize (str_noton _ _ _ phase (θ1 x y r)) as Q1.
  specialize (Rplus_le_le_0_compat (x + - (r * sin (θ1 x y r)))²
                                   (y + - (r * (1 + - cos (θ1 x y r))))²
                                   (Rle_0_sqr _) (Rle_0_sqr _)) as Q2.
  destruct (Rle_lt_or_eq_dec _ _ Q2) as [Q3 | Q3]; [assumption|].
  apply eq_sym, Rplus_sqr_eq_0 in Q3; contradiction.
Qed.

Lemma full_path_dist_is_derive_s :
  forall x y r
         (phase : straight r 0 0 0 x y)
         (rgt0 : 0 < r),
    is_derive (fun s => s * (θ1 x y) s + (sqrt ((x - s * sin (θ1 x y s))² +
                                                (y - s * (1 - cos (θ1 x y s)))²))) r
              ((θ1 x y r) - sin (θ1 x y r)).
Proof.
  intros.
  specialize (theta1_ex_derive_posr _ _ _ phase rgt0 ) as t1pe.

  specialize (Derive_correct _ _ (full_path_dist_ex_derive_s _ _ _ phase rgt0)) as Q1.
  rewrite full_path_dist_deriv_s in Q1; auto.
Qed.


(* end hide *)

Lemma full_path_dist_is_derive :
  forall θ₀ x₀ y₀ x₁ y₁ r (phase : straight r θ₀ x₀ y₀ x₁ y₁) (rgt0 : 0 < r),
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    is_derive (fun s => s * (θ1 x y) s + (sqrt ((x - s * sin (θ1 x y s))² +
                                                (y - s * (1 - cos (θ1 x y s)))²))) r
              ((θ1 x y r) - sin (θ1 x y r)).
Proof.
  intros.
  apply straight_rot in phase.
  change (straight r 0 0 0 x y) in phase.
  apply full_path_dist_is_derive_s; assumption.
Qed.



(* begin hide *)
Lemma chord_length_std :
  forall x y r
         (phase : turning r 0 0 0 x y)
         (yne0 : y <> 0),
    let θmax := calcθ₁ 0 0 0 x y in
      (r * (1 - cos θmax))² + (r * sin θmax)² = y² + x².
Proof.
  intros.
  assert (r = (x² + y²)/ (2 * y)) as rd. {
    unfold turning, Tcx, Tcy in phase.
    autorewrite with null in phase.
    rewrite Rsqr_minus in phase.
    apply (Rmult_eq_reg_r (2 * y)); try lra.
    apply (Rplus_eq_reg_r (r² - 2 * r * y)).
    setl (r²).
    setr (x² + (y² + r² - 2 * y * r)); try assumption.
  }
  rewrite rd.
  unfold θmax.
  rewrite calcth1_atan2_s.
  apply chord_length; assumption.
Qed.

Lemma r_std_deriv_0 :
  forall x y,
    let θm := calcθ₁ 0 0 0 x y in
    cos θm <> 1 ->
    Derive (fun θ => (x * sin θ - y * cos θ) / (1 - cos θ)) θm = 0.
Proof.
  intros.
  unfold θm in *. clear θm.
  rewrite calcth1_atan2_s in *.
  rewrite <- signeq0_eqv.
  rewrite (r_std_deriv_sign); try assumption.
  rewrite signeq0_eqv.

  unfold atan2 in *.
  destruct (pre_atan2 y x) as [t [[tl tu] [yd xd]]].
  set (M := sqrt (y² + x²)) in *.
  rewrite yd, xd.
  setl (M * ((cos (2 * t) * cos t + sin (2 * t) * sin t) - cos t)).
  rewrite <- cos_minus.
  fieldrewrite (2 * t - t) (t).
  field.
Qed.

Lemma r_std_deriv_ex :
  forall x y (no : ~(x = 0 /\ y = 0)),
    let θm := calcθ₁ 0 0 0 x y in
    forall θ (tbnd : θm / 2 < θ < θm),
    ex_derive (fun θ => (x * sin θ - y * cos θ) / (1 - cos θ)) θ.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.

  destruct (Req_dec θm 0) as [tmeq0 |tmne0];
    [rewrite tmeq0, <- RmultRinv in tbnd;
     autorewrite with null in tbnd;
     lra|].

  assert (- 2 * PI < θm <= 2 * PI) as [tml tmu]. {
    unfold θm, calcθ₁.
    arn.
    specialize (atan2_bound _ _ no) as [lb ub].
    lra. }
  destruct (Rle_dec θm 0) as [[tmlt0| tmeq0] |tmgt0]; try lra.
  apply Rnot_le_lt in tmgt0.
  clear tml.
  destruct tmu as [tmlt2pi | tmeq2pi].
  
  + assert (cos θm <> 1) as ctmne1. {
      intro costmeq1.
      unfold θm,calcθ₁ in *.
      autorewrite with null in *.
      specialize (atan2_bound _ _ no) as [alb aub].
      apply (Rmult_le_compat_l 2) in aub; try lra.
      apply (Rmult_lt_compat_l 2) in alb; try lra.
      destruct (Rle_dec 0 (2 * atan2 y x)).
      apply cos_eq_1_2PI_0 in costmeq1; try lra.
      apply Rnot_le_lt in n.
      rewrite <- cos_neg in costmeq1.
      apply cos_eq_1_2PI_0 in costmeq1; try lra. }
    
    destruct (Rge_dec 0 y) as [r |zlty].
    exfalso.
    apply Rge_le in r.
    assert (θm < 0) as tmn. {
      unfold θm in *.
      rewrite calcth1_atan2_s in *.
      destruct (Rlt_dec 0 x).
      destruct r.
      specialize (atan2Q4 _ _ r0 H) as [lo hi].
      lra.
      rewrite H in *.
      specialize (atan2_0 _ r0) as z.
      rewrite z in ctmne1.
      exfalso.
      apply ctmne1.
      arn.
      reflexivity.
      apply Rnot_lt_le in n.
      destruct r.
      destruct n.
      specialize (atan2Q3 _ _ H0 H) as [lo hi].
      lra.
      rewrite H0 in *.
      specialize (atan2_mPI2 _ H) as z.
      rewrite z.
      lra.
      destruct n.
      rewrite H in *.
      specialize (atan2_PI _ H0) as z.
      rewrite z in ctmne1.
      exfalso.
      apply ctmne1.
      apply cos_2PI.
      exfalso.
      apply no.
      split; assumption. }
    
    destruct tbnd as [tbl tbu].
    lra.
    
    apply Rnot_ge_lt in zlty.
    specialize (atan2_bound _ _ no) as [a2lb a2ub].
    
    assert (0 < θm) as tmlb. {
      unfold θm in *.
      rewrite calcth1_atan2_s in *.
      lra. }
    
    assert (θm < 2 * PI) as tmub. {
      unfold θm in *.
      rewrite calcth1_atan2_s in *.
      destruct a2ub.
      lra.
      rewrite H in *.
      exfalso.
      apply ctmne1.
      apply cos_2PI. }
    
    destruct tbnd as [tlb tub].
    
    assert (θ < 2*PI) as tuub. {
      apply (Rlt_trans _ θm); assumption. }
    
    assert (cos θ <> 1). {
      intro coseq1.
      apply cosθeq1 in coseq1.
      rewrite coseq1 in tlb.
      lra.
      split; lra.  }
    
    specialize (r_std_deriv x y _ H) as idv.
    match goal with
    | q : is_derive ?f ?y ?d |- _ => exists d; assumption
    end.
    
  + assert (cos θ <> 1) as ctmne1. {
      intro costeq1.
      apply cos_eq_1_2PI_0 in costeq1; try lra. }
    
    unfold θm, calcθ₁ in tmeq2pi.
    autorewrite with null in tmeq2pi.
    
    assert (atan2 y x = PI) as at2eq2pi; try lra.
    specialize (r_std_deriv x y _ ctmne1) as idv.
    match goal with
    | q : is_derive ?f ?y ?d |- _ => exists d; assumption
    end.
Qed.

Lemma r_std_deriv_pos :
  forall x y (no : ~(x = 0 /\ y = 0)),
    let θm := calcθ₁ 0 0 0 x y in
    forall θ (tbnd : θm / 2 < θ < θm),
    0 < Derive (fun θ => (x * sin θ - y * cos θ) / (1 - cos θ)) θ.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.

  destruct (Req_dec θm 0) as [tmeq0 |tmne0];
    [rewrite tmeq0, <- RmultRinv in tbnd;
     autorewrite with null in tbnd;
     lra|].

  assert (- 2 * PI < θm <= 2 * PI) as [tml tmu]. {
    unfold θm, calcθ₁.
    arn.
    specialize (atan2_bound _ _ no) as [lb ub].
    lra. }
  destruct (Rle_dec θm 0) as [[tmlt0| tmeq0] |tmgt0]; try lra.
  apply Rnot_le_lt in tmgt0.
  clear tml.
  destruct tmu as [tmlt2pi | tmeq2pi].
  
  assert (cos θm <> 1) as ctmne1. {
    intro costmeq1.
    unfold θm,calcθ₁ in *.
    autorewrite with null in *.
    specialize (atan2_bound _ _ no) as [alb aub].
    apply (Rmult_le_compat_l 2) in aub; try lra.
    apply (Rmult_lt_compat_l 2) in alb; try lra.
    destruct (Rle_dec 0 (2 * atan2 y x)).
    apply cos_eq_1_2PI_0 in costmeq1; try lra.
    apply Rnot_le_lt in n.
    rewrite <- cos_neg in costmeq1.
    apply cos_eq_1_2PI_0 in costmeq1; try lra. }
  
  destruct (Rge_dec 0 y) as [r |zlty].
  exfalso.
  apply Rge_le in r.
  assert (θm < 0) as tmn. {
  unfold θm in *.
  rewrite calcth1_atan2_s in *.
  destruct (Rlt_dec 0 x).
  destruct r.
  specialize (atan2Q4 _ _ r0 H) as [lo hi].
  lra.
  rewrite H in *.
  specialize (atan2_0 _ r0) as z.
  rewrite z in ctmne1.
  exfalso.
  apply ctmne1.
  arn.
  reflexivity.
  apply Rnot_lt_le in n.
  destruct r.
  destruct n.
  specialize (atan2Q3 _ _ H0 H) as [lo hi].
  lra.
  rewrite H0 in *.
  specialize (atan2_mPI2 _ H) as z.
  rewrite z.
  lra.
  destruct n.
  rewrite H in *.
  specialize (atan2_PI _ H0) as z.
  rewrite z in ctmne1.
  exfalso.
  apply ctmne1.
  apply cos_2PI.
  exfalso.
  apply no.
  split; assumption. }

  destruct tbnd as [tbl tbu].
  lra.
  
  apply Rnot_ge_lt in zlty.
  specialize (atan2_bound _ _ no) as [a2lb a2ub].
  
  assert (0 < θm) as tmlb. {
    unfold θm in *.
    rewrite calcth1_atan2_s in *.
    lra. }

  assert (θm < 2 * PI) as tmub. {
    unfold θm in *.
    rewrite calcth1_atan2_s in *.
    destruct a2ub.
    lra.
    rewrite H in *.
    exfalso.
    apply ctmne1.
    apply cos_2PI. }

  destruct tbnd as [tlb tub].

  assert (θ < 2*PI) as tuub. {
    apply (Rlt_trans _ θm); assumption. }

  assert (cos θ <> 1). {
    intro coseq1.
    apply cosθeq1 in coseq1.
    rewrite coseq1 in tlb.
    lra.
    split; lra.  }
  
  rewrite <- signeq1_eqv.
  rewrite (r_std_deriv_sign); try assumption.
  rewrite signeq1_eqv.

  specialize (r_std_deriv_0 _ _ ctmne1) as ddef.
  change (Derive (fun θ : R => (x * sin θ - y * cos θ) / (1 - cos θ))
           θm = 0) in ddef.
  rewrite <- signeq0_eqv in ddef.
  rewrite (r_std_deriv_sign) in ddef; try assumption.
  rewrite signeq0_eqv in ddef.

  set (f := (fun t:R => x * (cos t - 1) + y * sin t)) in *.
  change (f θm = 0) in ddef.
  change (0 < f θ).
  set (f' := (fun t:R => - x * sin t + y * cos t)) in *.
  assert (forall t:R, is_derive f t (f' t)) as idf. {
    intros.
    unfold f.
    auto_derive.
    constructor.
    unfold f'.
    field. }

  assert (f' (θm/2) = 0) as f'eq0. {
    unfold θm.
    rewrite calcth1_atan2_s in *.
    fieldrewrite (2 * atan2 y x / 2) (atan2 y x).
    unfold atan2.
    destruct (pre_atan2 y x) as [t [[tl tu] [yd xd]]].
    set (M := sqrt (y² + x²)) in *.
    unfold f'.
    rewrite xd, yd.
    field. }

  assert (f 0 = 0) as fO. {
    unfold f.
    arn. field. }

  assert (0 < x² + y²) as ssq. {
    apply Rplus_le_lt_0_compat; try apply Rle_0_sqr.
    apply Rsqr_pos_lt.
    lra.
  }

  assert (0 < sqrt (x² + y²)) as sssq. {
    apply sqrt_lt_R0.
    assumption. }

  assert (0 < f (θm / 2)) as ftm2gt0. {
    unfold f, θm.
    rewrite calcth1_atan2_s in *.
    fieldrewrite (2 * atan2 y x / 2) (atan2 y x).
    rewrite atan2_cos_id, atan2_sin_id; try assumption.
    repeat rewrite <- Rsqr_pow2.
    setr ((x² + y²) / sqrt (x² + y²) - x).
    intro sq0.
    rewrite <- sqrt_0 in sq0.
    apply sqrt_inj in sq0;
      try (right; reflexivity).
    change (x² + y² = 0) in sq0.
    apply no.
    split;
      [|rewrite Rplus_comm in sq0];
      apply Rplus_sqr_eq_0_l in sq0;
      assumption.
    left; assumption.
    rewrite <- (sqrt_Rsqr (x² + y²)) at 1;
      try (left; assumption).
    rewrite <- sqrt_div;
      try assumption; try apply Rle_0_sqr.
    fieldrewrite ((x² + y²)² / (x² + y²))
                 (x² + y²).
    intro.
    change (x² + y² = 0) in H0.
    rewrite H0 in ssq.
    lra.
    apply (Rplus_lt_reg_r x).
    setl x.
    setr (sqrt (x² + y²)).

    destruct (Rlt_dec x 0).
    apply (Rlt_trans _ 0); try assumption.
    apply Rnot_lt_le in n.
    rewrite <- (sqrt_Rsqr x) at 1; try assumption.
    apply sqrt_lt_1.
    apply Rle_0_sqr.
    left; assumption.

    apply (Rplus_lt_reg_r (- x²)).
    setl 0.
    setr (y²).
    apply Rsqr_pos_lt.
    lra. }

  assert (forall t, θm/2 < t <= PI/2 -> f' t < 0) as f'lt0. {
    intros t [tl tu].
    unfold f' in *.
    apply (Rplus_lt_reg_r (x * sin t)).
    arn.
    setl (y * cos t).
    destruct (Rlt_dec 0 x).
      ++ apply (Rlt_trans _ (y*cos (θm / 2))).
         apply (Rmult_lt_reg_r (/ y)).
         zltab.
         setl (cos t). lra.
         setr (cos (θm / 2)). lra.
         apply cos_decreasing_1; lra.
         unfold f' in f'eq0.
         apply Rplus_opp_r_uniq in f'eq0.
         rewrite f'eq0.
         setl (x * sin (θm / 2)).
         apply (Rmult_lt_reg_r (/ x)).
         zltab.
         setl (sin (θm / 2)). lra.
         setr (sin t). lra.
         apply sin_increasing_1; lra.
    
      ++ apply Rnot_lt_le in n.
         destruct n as [n |e].
         +++ exfalso.
             unfold f in ddef.
             apply Rplus_opp_r_uniq in f'eq0.
             assert (0 < y * cos (θm / 2)) as ctr1. {
               zltab.
               apply cos_gt_0; lra. }
             assert (y * cos (θm / 2) <= 0) as ctr2. {
               rewrite f'eq0.
               rewrite <- Ropp_0.
               apply Ropp_le_contravar.
               zltab.
               apply sin_ge_0; lra. }
             lra.
         +++ exfalso. rewrite e in *.
             autorewrite with null in f'eq0.
             apply Rmult_integral in f'eq0.
             destruct f'eq0.
             lra.
             apply cosθeq0 in H0.
             destruct H0; rewrite H0 in tl; lra.
             split; lra. }
  
  assert (forall t, θm / 2 < t <= PI -> f' t < 0) as f'lt1. {
    intros t [tl tu].
    unfold f' in *.
    destruct (Rle_dec t (PI/2)).
    apply f'lt0.
    split; assumption.
    apply Rnot_le_lt in n.
    apply (Rplus_lt_reg_r (x * sin t)).
    arn.
    setl (y * cos t).
    
    destruct (Rlt_dec 0 x).
    ++ assert (y * cos (PI/2) < x * sin (PI/2)) as pi2i. {
         rewrite sin_PI2, cos_PI2.
         arn.
         assumption. }
       
       destruct tu as [l | e];
        [ | rewrite e in *;
            arn;
            apply Ropp_lt_cancel;
            rewrite Ropp_0;
            setr y; try assumption].
       apply (Rlt_trans _ 0).
       setl (- (y * - cos t)).
       apply Ropp_lt_cancel.
       rewrite Ropp_0, Ropp_involutive.
       zltab.
       apply Ropp_lt_cancel.
       rewrite Ropp_0, Ropp_involutive.
       apply cos_lt_0; try lra.
       zltab.
       apply sin_gt_0; lra.
    ++ apply Rnot_lt_le in n0.
       destruct n0 as [l | e];
        [ | rewrite e in *;
            arn;
            apply Ropp_lt_cancel;
            rewrite Ropp_0;
            setr (y * - cos t);
            zltab;
            apply Ropp_lt_cancel;
            rewrite Ropp_0, Ropp_involutive;
            apply cos_lt_0; lra].
       assert (x * sin (PI/2) < y * cos (PI/2)) as pi2i. {
         rewrite sin_PI2, cos_PI2.
         arn.
         assumption. }
       destruct (Rlt_dec (θm / 2) (PI / 2)).
       exfalso.
       assert (y * cos (PI/2) < x * sin (PI/2)) as pi2j. {
         apply Rminus_lt.
         setl ( - x * sin (PI / 2) + y * cos (PI / 2)).
         apply f'lt0.
         split; lra. }
       lra.
       apply Rnot_lt_le in n0.
       apply Rplus_opp_r_uniq in f'eq0.
       assert (y * cos (θm / 2) = x * sin (θm / 2)) as id. lra.
       apply (Rlt_trans _ (x * sin (θm / 2))).
       rewrite <- id.
       apply (Rmult_lt_reg_r (/ y)).
       zltab.
       setl (cos t). lra.
       setr (cos (θm / 2)). lra.
       apply cos_decreasing_1; lra.
       apply (Rmult_lt_reg_r (/ - x)).
       zltab. lra.
       setl (- sin (θm / 2)). lra.
       setr (- sin t). lra.
       apply Ropp_lt_contravar.
       apply sin_decreasing_1; lra. }
  clear f'lt0.

  assert (f' θm < 0) as f'tmlt0. {
    unfold f' in *.
    fieldrewrite (θm) (θm/2 + θm/2).
    rewrite sin_plus, cos_plus.
    setl (- (x * sin (θm / 2)) * cos (θm / 2)
          + - x * cos (θm / 2) * sin (θm / 2)
          + (y * cos (θm / 2)) * cos (θm / 2)
            - y * sin (θm / 2) * sin (θm / 2)).
    apply Rplus_opp_r_uniq in f'eq0.
    rewrite f'eq0.
    setl (- (- (- x * sin (θm / 2) ))* cos (θm / 2) 
          - y * sin (θm / 2) * sin (θm / 2)).
    rewrite <- f'eq0.
    setl (- y * ((sin (θm / 2))²+(cos (θm / 2))²)).
    rewrite sin2_cos2.
    lra. }


  assert (forall t : R, 3 * (PI / 2) < t <= θm -> f' t < 0) as f'lt3. {
    intros t [tl [tu |te]].
    unfold f' in *.
    destruct (Rle_dec x 0).
    - destruct r as [l | e].
      apply (Rlt_trans _ (- x * sin θm + y * cos θm)).
      apply Rplus_lt_compat.
      apply (Rmult_lt_reg_r (/ - x)).
      zltab. lra.
      setl (sin t). lra.
      setr (sin θm). lra.
      rewrite <- (sin_period1 t (-1)).
      rewrite <- (sin_period1 θm (-1)).
      apply sin_increasing_1; lra.
      apply (Rmult_lt_reg_r (/ y)).
      zltab. 
      setl (cos t). lra.
      setr (cos θm). lra.
      apply cos_increasing_1; lra.
      assumption.
      exfalso.
      rewrite e in f'tmlt0.
      autorewrite with null in f'tmlt0.
      generalize f'tmlt0.
      clear f'tmlt0.
      apply Rle_not_lt.
      zltab.
      rewrite <- (cos_period1 θm (-1)).
      apply cos_ge_0; lra.
    - exfalso.
      apply Rnot_le_lt in n.
      assert (3 * (PI / 2) < θm) as ctr. lra.
      unfold θm in ctr.
      rewrite calcth1_atan2_s in ctr.
      specialize (atan2Q1 x y n zlty) as [atl atu].
      lra.
    - rewrite te. apply f'tmlt0.
  }
  
  assert (forall t : R, θm / 2 < t <= θm -> f' t < 0) as f'ltn. {
    intros t [tl th].
    destruct (Rlt_dec (3 * (PI / 2)) t).
    apply f'lt3.
    split; lra.
    apply Rnot_lt_le in n.
    destruct (Rle_dec t PI).
    apply f'lt1.
    split; lra.
    apply Rnot_le_lt in n0.
    unfold f'.
    destruct (Rlt_dec 0 x).
    assert (PI < θm) as pilttm. lra.
    specialize (atan2Q1 x y r zlty) as [atl atu].
    unfold θm in pilttm.
    rewrite calcth1_atan2_s in pilttm.
    lra.
    apply Rnot_lt_le in n1.
    destruct n1 as [xlt |xeq].
    assert (f' (3 * (PI / 2)) = x) as f'3pi2lt0. {
      unfold f'.
      rewrite sin_3PI2, cos_3PI2.
      field. }
    destruct n as [tlt |teq].
    (*****)
    unfold f' in f'3pi2lt0.
    apply (Rplus_lt_reg_r (x * sin t)).
    setl (y * cos t).
    arn.
    apply (Rlt_trans _ (y * cos (3 * (PI / 2)))).
    apply (Rmult_lt_reg_r (/ y)).
    zltab. 
    setl (cos t). lra.
    setr (cos (3 * (PI / 2))). lra.
    apply cos_increasing_1; lra.
    rewrite cos_3PI2.
    arn.
    setr (- x * - sin t).
    zltab.
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    apply sin_lt_0; try lra.
    (*****)
    rewrite teq.
    unfold f' in f'3pi2lt0.
    rewrite f'3pi2lt0.
    assumption.
    specialize (atan2_PI2 _ zlty) as at2v.
    assert (PI < θm) as PIlttm. lra.
    unfold θm in PIlttm.
    rewrite calcth1_atan2_s in PIlttm.
    rewrite xeq, at2v in PIlttm.
    lra. }
  
  rewrite <- ddef.
  eapply (derive_decreasing_interv (θm / 2) θm);
    try (split; lra);
    try lra.
  intros.
  rewrite Derive_Reals.
  specialize (idf t).
  apply is_derive_unique in idf.
  rewrite idf.
  eapply f'ltn.
  destruct H0 as [tl tu].
  split;
    try assumption;
    try (left; assumption).

  Unshelve.
  + assert (cos θ <> 1) as ctmne1. {
      intro costeq1.
      apply cos_eq_1_2PI_0 in costeq1; try lra. }

    unfold θm, calcθ₁ in tmeq2pi.
    autorewrite with null in tmeq2pi.

    assert (atan2 y x = PI) as at2eq2pi; try lra.
    apply atan2_PI_impl in at2eq2pi as [xlt0 yeq0]; try assumption.
    specialize (r_std_deriv_sign x y θ ctmne1) as sddef.
    rewrite <- signeq1_eqv.
    rewrite sddef.
    rewrite signeq1_eqv.
    clear sddef.
    rewrite yeq0 in *.
    arn.
    setr (- x * (1 - cos θ)).
    zltab.
    specialize (COS_bound θ) as [clb cub].
    destruct cub as [cub |ceq1] ; try lra.

  + unfold derivable.
    intros.
    apply ex_derive_Reals_0.
    unfold ex_derive.
    exists (f' x0).
    apply idf.
Qed.

Lemma r_std_deriv_pos2 :
  forall x y (no : ~(x = 0 /\ y = 0)),
    let θm := calcθ₁ 0 0 0 x y in
    forall θ (tbnd : θm / 2 + 2 * PI < θ < 2 * PI),
    0 < Derive (fun θ => (x * sin θ - y * cos θ) / (1 - cos θ)) θ.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.

  destruct (Req_dec θm 0) as [tmeq0 |tmne0];
    [rewrite tmeq0, <- RmultRinv in tbnd;
     autorewrite with null in tbnd;
     lra|].

  assert (- 2 * PI < θm <= 2 * PI) as [tml tmu]. {
    unfold θm, calcθ₁.
    arn.
    specialize (atan2_bound _ _ no) as [lb ub].
    lra. }
  destruct (Rle_dec θm 0) as [[tmlt0| tmeq0] |tmgt0]; try lra.
  clear tmu.
  
  assert (cos θm <> 1) as ctmne1. {
    intro costmeq1.
    unfold θm,calcθ₁ in *.
    autorewrite with null in *.
    specialize (atan2_bound _ _ no) as [alb aub].
    apply (Rmult_le_compat_l 2) in aub; try lra.
    apply (Rmult_lt_compat_l 2) in alb; try lra.
    destruct (Rle_dec 0 (2 * atan2 y x)).
    apply cos_eq_1_2PI_0 in costmeq1; try lra.
    apply Rnot_le_lt in n.
    rewrite <- cos_neg in costmeq1.
    apply cos_eq_1_2PI_0 in costmeq1; try lra. }
  
  destruct (Rge_dec y 0) as [r |ylt0].
  + exfalso.
    apply Rge_le in r.
    assert (0 <= θm) as tmn. {
      unfold θm in *.
      rewrite calcth1_atan2_s in *.
      destruct (Rlt_dec 0 x).
      destruct r.
      ++ specialize (atan2Q1 _ _ r0 H) as [lo hi].
         lra.
      ++ rewrite <- H in *.
         specialize (atan2_0 _ r0) as z.
         rewrite z in ctmne1.
         exfalso.
         apply ctmne1.
         arn.
         reflexivity.
      ++ apply Rnot_lt_le in n.
         destruct r.
         destruct n.
         +++ specialize (atan2Q2 _ _ H0 H) as [lo hi].
             lra.
         +++ rewrite H0 in *.
             specialize (atan2_PI2 _ H) as z.
             rewrite z.
             lra.
         +++ destruct n.
             rewrite <- H in *.
             specialize (atan2_PI _ H0) as z.
             rewrite z in ctmne1.
             exfalso.
             apply ctmne1.
             apply cos_2PI.
             exfalso.
             apply no.
             split; auto. }

    destruct tbnd as [tbl tbu].
    lra.
  
  + apply Rnot_ge_lt in ylt0.
    specialize (atan2_bound _ _ no) as [a2lb a2ub].
  
    destruct tbnd as [tlb tub].

    assert (cos θ <> 1). {
      intro coseq1.
      apply cosθeq1 in coseq1.
      rewrite coseq1 in tlb.
      lra.
      split; lra.  }
  
    rewrite <- signeq1_eqv.
    rewrite (r_std_deriv_sign); try assumption.
    rewrite signeq1_eqv.

    clear a2ub.
    assert (atan2 y x < 0) as a2ub. {
      destruct (Rlt_dec 0 x) as [zltx | zgex].
      apply atan2Q4; try assumption.
      apply Rnot_lt_le in zgex.
      destruct zgex as [xlt0 | xeq0].
      apply (Rlt_trans _ (- (PI/2))).
      apply atan2Q3; try assumption.
      lra.
      rewrite xeq0.
      rewrite atan2_mPI2; try lra. }

    assert (PI < θ) as piltt by lra.

    specialize (sin_lt_0 θ piltt tub) as stlt0.
    assert (0 < y * sin θ) as ysgt0. {
      fieldrewrite (y * sin θ) (- y * - sin θ).
      apply Rmult_lt_0_compat; try lra. }

    assert (0 < 1 - cos θ) as zlt1mct. {
      specialize (COS_bound θ) as [cub clb].
      destruct clb as [clb |clb];
        lra. }

    fieldrewrite (x * (cos θ - 1)) (- (x * (1 - cos θ))).
    apply (Rplus_lt_reg_r (x * (1 - cos θ))).
    setr (y * sin θ).
    arn.

    destruct (Rle_dec x 0).
    ++ apply (Rmult_lt_reg_r (/ (1 - cos θ))).
       zltab.
       setl x; try lra.

       apply (Rle_lt_trans _ 0); try assumption.
       apply Rmult_lt_0_compat; try lra.
       zltab.
    ++ apply Rnot_le_lt in n.
       apply (Rmult_lt_reg_r (/ x * / - sin θ)).
       zltab.
       lra.
       setl (- ((1 - cos θ)/sin θ)); try lra.
       setr (- (y/x)); try lra.
       apply Ropp_lt_contravar.
       rewrite <- tant2_2; try lra.

       assert (tan (θm/2) = y/x) as tid. {
         unfold θm.
         rewrite calcth1_atan2_s in *.
         fieldrewrite (2 * atan2 y x / 2) (atan2 y x).
         apply atan2_right_inv; try lra. }
       rewrite <- tid.

       rewrite <- (tan_period (θ / 2) (-1)%Z).
       apply tan_increasing; try lra.
       unfold θm.
       rewrite calcth1_atan2_s in *.
       fieldrewrite (2 * atan2 y x / 2) (atan2 y x).
       setl (- (PI/2)).
       apply atan2Q4; assumption.

       assert (PI/2 < θ / 2 < PI) as [t2lb t2ub]. {
         split; lra. }

       assert (- PI < θ/2 <= PI) as trng2 by lra.
       intro cost2eq0.
       apply (cosθeq0 _ trng2) in cost2eq0.
       lra.
Qed.


Lemma straight_r_dom1_std :
  forall r s  x₁ y₁,
    0 < y₁ -> 
    s < r ->
    straight r 0 0 0 x₁ y₁ ->
    straight s 0 0 0 x₁ y₁.
Proof.
  intros *.
  intros zlty1 sltr sr.
  apply straightcond in sr.
  unfold straight, Tcx, Tcy in *.
  arn.
  rewrite Rsqr_minus.
  apply (Rplus_lt_reg_r (2 * y₁ * s - s²)).
  setl (2 * s * y₁).
  setr (x₁² + y₁²).
  apply (Rlt_trans _ (2 * r * y₁)); try assumption.
  apply (Rmult_lt_reg_r (/ 2 * / y₁)).
  zltab.
  setl s; try lra.
  setr r; try lra.
Qed.

Lemma straight_r_dom2_std :
  forall r s  x₁ y₁,
    y₁ < 0 -> 
    r < s ->
    straight r 0 0 0 x₁ y₁ ->
    straight s 0 0 0 x₁ y₁.
Proof.
  intros *.
  intros zlty1 sltr sr.
  apply straightcond in sr.
  unfold straight, Tcx, Tcy in *.
  arn.
  rewrite Rsqr_minus.
  apply (Rplus_lt_reg_r (2 * y₁ * s - s²)).
  setl (2 * s * y₁).
  setr (x₁² + y₁²).
  apply (Rlt_trans _ (2 * r * y₁)); try assumption.
  apply (Rmult_lt_reg_r (/ 2 * / - y₁)).
  zltab.
  lra.
  setl (- s); try lra.
  setr (- r); try lra.
Qed.

Lemma straight_r_dom3_std :
  forall r s x₁ y₁,
    y₁ = 0 -> 
    straight s 0 0 0 x₁ y₁ ->
    straight r 0 0 0 x₁ y₁.
Proof.
  intros * yeq0.
  unfold straight, Tcx, Tcy in *.
  subst.
  arn.
  intros sts.
  rewrite <- Rsqr_neg.
  rewrite <- Rsqr_neg in sts.
  apply (Rplus_lt_reg_r (- r² + s²)).
  lrag sts.
Qed.

Lemma tm2ltt1 :
  forall x y r (zltr : 0 < r) (zlty : 0 < y)
         (phase : straight r 0 0 0 x y),
    let θmax := calcθ₁ 0 0 0 x y in
    θmax / 2 < θ1 x y r.
Proof.
  intros.
  apply straightcond in phase.
  assert (~ (x = 0 /\ y = 0)) as no; try (intro; lra).

  assert (0 < x² + y²) as ssq. {
    apply Rplus_le_lt_0_compat; try apply Rle_0_sqr.
    apply Rsqr_pos_lt.
    lra.
  }
  
  assert (0 < sqrt (x² + y²)) as sssq. {
    apply sqrt_lt_R0.
    assumption. }

  assert (atan2 y x <> PI) as at2nepi. {
    intro at2eqpi.
    apply atan2_PI_impl in at2eqpi; lra. }

                                      
  
  assert (tan (θmax / 4) = y / (x + sqrt (x² + y²))) as id. {
    unfold θmax,calcθ₁.
    arn.
    fieldrewrite (2 * atan2 y x / 4) (atan2 y x / 2).
    rewrite tant2;
      [| intro ceq0;
         specialize (atan2_bound x y no) as [a2lb a2ub];
         apply (Rmult_le_compat_r (/2)) in a2ub; [|lra];
         repeat rewrite RmultRinv in a2ub;
         apply (Rmult_lt_compat_r (/2)) in a2lb; [|lra];
         repeat rewrite RmultRinv in a2lb;
         apply cosθeq0 in ceq0; [|split; lra];
         destruct ceq0 as [at2pi2 | other]; try lra].
    
    assert (sin (atan2 y x) = y / sqrt (x² + y²)) as sid. {
      unfold atan2.
      destruct pre_atan2 as [a [arng [yd xd]]].
      rewrite Rplus_comm.
      rewrite yd at 1.
      field.
      rewrite Rplus_comm.
      lra.
    }

    assert (cos (atan2 y x) = x / sqrt (x² + y²)) as cid. {
      unfold atan2.
      destruct pre_atan2 as [a [arng [yd xd]]].
      rewrite Rplus_comm.
      rewrite xd at 1.
      field.
      rewrite Rplus_comm.
      lra.
    }

    rewrite sid, cid.
    setl (y / (x + sqrt (x² + y²))); try reflexivity.
    split; try (unfold Rsqr in sssq; lra).
    intro xpseq0.
    change (x + sqrt (x² + y²) = 0) in xpseq0.
    assert (Rabs x < sqrt (x² + y²)) as ax. {
      rewrite <- sqrt_Rsqr_abs.
      apply sqrt_lt_1.
      apply Rle_0_sqr.
      lra.
      apply (Rplus_lt_reg_r (- x²)).
      setl 0.
      setr (y²).
      specialize (Rle_0_sqr y) as y2ge0.
      destruct y2ge0 as [y2gt0|y2eq0];
        [assumption|
         symmetry in y2eq0;
         apply Rsqr_eq_0 in y2eq0; lra ].
    }

    destruct (total_order_T 0 x) as [[zltx |zeqx]|zgtx].
    + rewrite Rabs_right in ax; lra.
    + lra.
    + rewrite Rabs_left in ax; lra.
  }                    
  
  unfold θ1.
  destruct total_order_T as [[zltr2|zeqr] |rgt0]; try lra.
  destruct (total_order_T _ y) as [[zlty2|zeqy] |ygt0]; try lra.
  
  destruct (total_order_T) as [[zltx|zeqx] |xgt0].
  destruct (total_order_T) as [[zlta|zeqa] |agt0].

  + apply (Rmult_lt_reg_r (/2)); try lra.
    setl (θmax / 4).
    setr (atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))).
    apply tan_increasing_pi2.
    unfold θmax, calcθ₁;
      arn;
      specialize (atan2_bound x y no) as [atl [atu|atu2]]; try lra.
    apply atan_bound.
    rewrite atan_right_inv.
    rewrite id.
    specialize (Rplus_lt_le_0_compat _ _ zltx (sqrt_pos (x² - (2 * r - y) * y))) as zltA.
    setr ((x² - (sqrt (x² - (2 * r - y) * y))²)
            / ((2 * r - y)*(x + sqrt (x² - (2 * r - y) * y)))).
    unfold Rsqr in zltA.
    split; lra.
    rewrite Rsqr_sqrt; try (unfold Rsqr in *; lra).

    fieldrewrite (x² - (x² - (2 * r - y) * y)) ((2 * r - y) * y).
    setr (y / (x + sqrt (x² - (2 * r - y) * y))).
    unfold Rsqr in zltA.
    split; lra.
    fieldrewrite (x² - (2 * r - y) * y) (x² + y² - 2 * r * y).
    assert (sqrt (x² + y² - 2 * r * y) < sqrt (x² + y²)) as sro. {
      apply sqrt_lt_1.
      lra.
      left; assumption.
      apply (Rplus_lt_reg_r (- x² - y²)).
      setl (- 2 * r * y).
      setr (- 0).
      setl (- (2 * r * y)).
      apply Ropp_lt_contravar.
      zltab. }

    assert (x² - (2 * r - y) * y = x² + y² - 2 * r * y) as id2. {
      unfold Rsqr. lra. }
    rewrite id2 in zltA.
    assert (0 < x + sqrt (x² + y²)) as zltB. lra.
    
    apply (Rmult_lt_reg_r (/ y * (x + sqrt (x² + y²)) *
                           (x + sqrt (x² + y² - 2 * r * y)))).
    zltab.
    setl ((x + sqrt (x² + y² - 2 * r * y))).
    unfold Rsqr in *; split; lra.
    setr ((x + sqrt (x² + y²))).
    unfold Rsqr in *; split; lra.
    lra.

  + symmetry in zeqa.
    apply Rminus_diag_uniq in zeqa.
    apply (Rmult_lt_reg_r (/2 )).
    lra.
    setl (θmax / 4).
    setr (atan (y / (2 * x))).
    apply tan_increasing_pi2.
    unfold θmax, calcθ₁;
      arn;
      specialize (atan2_bound x y no) as [atl [atu|atu2]]; try lra.
    apply atan_bound.
    rewrite atan_right_inv.
    rewrite id.
    apply (Rmult_lt_reg_r (/ y * (2 * x) * (x + sqrt (x² + y²)))).
    zltab.
    setl (2 * x).
    unfold Rsqr in *.
    split; lra.
    setr ((x + sqrt (x² + y²))).
    lra.
    apply (Rplus_lt_reg_r (-x)).
    setl x.
    setr (sqrt (x² + y²)).
    rewrite <- (Rabs_right x) at 1.
    rewrite <- (sqrt_Rsqr_abs x).
    apply sqrt_lt_1.
    ++ apply Rle_0_sqr.
    ++ left. assumption.
    ++ apply (Rplus_lt_reg_r (-(x²))).
       setl 0.
       setr (y²).
       apply Rlt_0_sqr.
       lra.
    ++ lra.
  + apply (Rmult_lt_reg_r (/2)); try lra.
    setl (θmax / 4).
    setr (atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))).
    apply tan_increasing_pi2.
    unfold θmax, calcθ₁;
      arn;
      specialize (atan2_bound x y no) as [atl [atu|atu2]]; try lra.
    apply atan_bound.
    rewrite atan_right_inv.
    rewrite id.
    specialize (Rplus_lt_le_0_compat _ _ zltx (sqrt_pos (x² - (2 * r - y) * y))) as zltA.
    setr ((x² - (sqrt (x² - (2 * r - y) * y))²)
            / ((2 * r - y)*(x + sqrt (x² - (2 * r - y) * y)))).
    unfold Rsqr in zltA.
    split; lra.
    rewrite Rsqr_sqrt; try (unfold Rsqr in *; lra).

    fieldrewrite (x² - (x² - (2 * r - y) * y)) ((2 * r - y) * y).
    setr (y / (x + sqrt (x² - (2 * r - y) * y))).
    unfold Rsqr in zltA.
    split; lra.
    fieldrewrite (x² - (2 * r - y) * y) (x² + y² - 2 * r * y).
    assert (sqrt (x² + y² - 2 * r * y) < sqrt (x² + y²)) as sro. {
      apply sqrt_lt_1.
      lra.
      left; assumption.
      apply (Rplus_lt_reg_r (- x² - y²)).
      setl (- 2 * r * y).
      setr (- 0).
      setl (- (2 * r * y)).
      apply Ropp_lt_contravar.
      zltab. }

    assert (x² - (2 * r - y) * y = x² + y² - 2 * r * y) as id2. {
      unfold Rsqr. lra. }
    rewrite id2 in zltA.
    assert (0 < x + sqrt (x² + y²)) as zltB. lra.
    
    apply (Rmult_lt_reg_r (/ y * (x + sqrt (x² + y²)) *
                           (x + sqrt (x² + y² - 2 * r * y)))).
    zltab.
    setl ((x + sqrt (x² + y² - 2 * r * y))).
    unfold Rsqr in *; split; lra.
    setr ((x + sqrt (x² + y²))).
    unfold Rsqr in *; split; lra.
    lra.
  + destruct (total_order_T) as [[zlta|zeqa] |agt0].
    ++ exfalso.
       rewrite <- zeqx, Rsqr_0, Rplus_0_l in phase.
       assert (y² < 2 * r * y) as p2. {
         apply (Rmult_lt_reg_r (/ y)).
         zltab.
         unfold Rsqr.
         setl y; try lra.
         setr (2 * r); try lra. }
         lra.
    ++ exfalso.
       rewrite <- zeqx, Rsqr_0, Rplus_0_l in phase.
       symmetry in zeqa.
       apply Rminus_diag_uniq_sym in zeqa.
       rewrite <- zeqa in phase.
       unfold Rsqr in phase.
       lra.
    ++ apply (Rmult_lt_reg_r (/2)); try lra.
       setl (θmax / 4).
       setr (atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))).
       apply tan_increasing_pi2.
       unfold θmax, calcθ₁;
         arn;
         specialize (atan2_bound x y no) as [atl [atu|atu2]]; try lra.
       apply atan_bound.
       rewrite atan_right_inv.
       rewrite id.
       
       assert (0 < x + sqrt (x² - (2 * r - y) * y)) as zltA. {
         apply th2_num_sign.
         setr ((- (2 * r - y)) * y).
         apply Rmult_lt_0_compat; lra. }
       
       setr ((x² - (sqrt (x² - (2 * r - y) * y))²)
               / ((2 * r - y)*(x + sqrt (x² - (2 * r - y) * y)))).
       unfold Rsqr in zltA.
       split; lra.
       rewrite Rsqr_sqrt; try (unfold Rsqr in *; lra).
       
       fieldrewrite (x² - (x² - (2 * r - y) * y)) ((2 * r - y) * y).
       setr (y / (x + sqrt (x² - (2 * r - y) * y))).
       unfold Rsqr in zltA.
       split; lra.
       fieldrewrite (x² - (2 * r - y) * y) (x² + y² - 2 * r * y).
       assert (sqrt (x² + y² - 2 * r * y) < sqrt (x² + y²)) as sro. {
         apply sqrt_lt_1.
         lra.
         left; assumption.
         apply (Rplus_lt_reg_r (- x² - y²)).
         setl (- 2 * r * y).
         setr (- 0).
         setl (- (2 * r * y)).
         apply Ropp_lt_contravar.
         zltab. }
       
       assert (x² - (2 * r - y) * y = x² + y² - 2 * r * y) as id2. {
         unfold Rsqr. lra. }
       rewrite id2 in zltA.
       assert (0 < x + sqrt (x² + y²)) as zltB. lra.
       
       apply (Rmult_lt_reg_r (/ y * (x + sqrt (x² + y²)) *
                              (x + sqrt (x² + y² - 2 * r * y)))).
       zltab.
       setl ((x + sqrt (x² + y² - 2 * r * y))).
       unfold Rsqr in *; split; lra.
       setr ((x + sqrt (x² + y²))).
       unfold Rsqr in *; split; lra.
       lra.
       
  + set (A := ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))) in *.
    specialize (atan_bound A) as [atl atu].
    assert (- PI < θmax / 2 < PI) as [tml tmu]. {
      specialize (atan2_bound x y no) as [at2l at2u].
      unfold θmax,calcθ₁.
      arn.
      fieldrewrite (2 * atan2 y x / 2) (atan2 y x).
      lra. }
    destruct (total_order_T) as [[zlta|zeqa] |agt0].
    ++ lra.
    ++ lra.
    ++ unfold A in *.
       apply (Rmult_lt_reg_r (/2)); try lra.
       setl (θmax / 4).
       setr (atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))).
       apply tan_increasing_pi2.
       lra.
       apply atan_bound.
       rewrite atan_right_inv.
       rewrite id.

       assert (0 < x + sqrt (x² - (2 * r - y) * y)) as zltA. {
         apply th2_num_sign.
         setr ((- (2 * r - y)) * y).
         apply Rmult_lt_0_compat; lra. }

       setr ((x² - (sqrt (x² - (2 * r - y) * y))²)
               / ((2 * r - y)*(x + sqrt (x² - (2 * r - y) * y)))).
       unfold Rsqr in zltA.
       split; lra.
       rewrite Rsqr_sqrt; try (unfold Rsqr in *; lra).
       
       fieldrewrite (x² - (x² - (2 * r - y) * y)) ((2 * r - y) * y).
       setr (y / (x + sqrt (x² - (2 * r - y) * y))).
       unfold Rsqr in zltA.
       split; lra.
       fieldrewrite (x² - (2 * r - y) * y) (x² + y² - 2 * r * y).
       assert (sqrt (x² + y² - 2 * r * y) < sqrt (x² + y²)) as sro. {
         apply sqrt_lt_1.
         lra.
         left; assumption.
         apply (Rplus_lt_reg_r (- x² - y²)).
         setl (- 2 * r * y).
         setr (- 0).
         setl (- (2 * r * y)).
         apply Ropp_lt_contravar.
         zltab. }
       
       assert (x² - (2 * r - y) * y = x² + y² - 2 * r * y) as id2. {
         unfold Rsqr. lra. }
       rewrite id2 in zltA.
       assert (0 < x + sqrt (x² + y²)) as zltB. lra.
       
       apply (Rmult_lt_reg_r (/ y * (x + sqrt (x² + y²)) *
                              (x + sqrt (x² + y² - 2 * r * y)))).
       zltab.
       setl ((x + sqrt (x² + y² - 2 * r * y))).
       unfold Rsqr in *; split; lra.
       setr ((x + sqrt (x² + y²))).
       unfold Rsqr in *; split; lra.
       lra.
Qed.

Lemma t1lttm2 :
  forall x y r (zltr : r < 0) (zlty : y < 0)
         (phase : straight r 0 0 0 x y),
    let θmax := calcθ₁ 0 0 0 x y in
    θ1 x y r < θmax / 2.
Proof.
  intros.
  apply straightcond in phase.
  assert (~ (x = 0 /\ y = 0)) as no; try (intro; lra).

  assert (0 < x² + y²) as ssq. {
    apply Rplus_le_lt_0_compat; try apply Rle_0_sqr.
    apply Rsqr_pos_lt.
    lra.
  }
  
  assert (0 < sqrt (x² + y²)) as sssq. {
    apply sqrt_lt_R0.
    assumption. }

  assert (atan2 y x <> PI) as at2nepi. {
    intro at2eqpi.
    apply atan2_PI_impl in at2eqpi; lra. }

                                      
  
  assert (tan (θmax / 4) = y / (x + sqrt (x² + y²))) as id. {
    unfold θmax,calcθ₁.
    arn.
    fieldrewrite (2 * atan2 y x / 4) (atan2 y x / 2).
    rewrite tant2;
      [| intro ceq0;
         specialize (atan2_bound x y no) as [a2lb a2ub];
         apply (Rmult_le_compat_r (/2)) in a2ub; [|lra];
         repeat rewrite RmultRinv in a2ub;
         apply (Rmult_lt_compat_r (/2)) in a2lb; [|lra];
         repeat rewrite RmultRinv in a2lb;
         apply cosθeq0 in ceq0; [|split; lra];
         destruct ceq0 as [at2pi2 | other]; try lra].
    
    assert (sin (atan2 y x) = y / sqrt (x² + y²)) as sid. {
      unfold atan2.
      destruct pre_atan2 as [a [arng [yd xd]]].
      rewrite Rplus_comm.
      rewrite yd at 1.
      field.
      rewrite Rplus_comm.
      lra.
    }

    assert (cos (atan2 y x) = x / sqrt (x² + y²)) as cid. {
      unfold atan2.
      destruct pre_atan2 as [a [arng [yd xd]]].
      rewrite Rplus_comm.
      rewrite xd at 1.
      field.
      rewrite Rplus_comm.
      lra.
    }

    rewrite sid, cid.
    setl (y / (x + sqrt (x² + y²))); try reflexivity.
    split; try (unfold Rsqr in sssq; lra).
    intro xpseq0.
    change (x + sqrt (x² + y²) = 0) in xpseq0.
    assert (Rabs x < sqrt (x² + y²)) as ax. {
      rewrite <- sqrt_Rsqr_abs.
      apply sqrt_lt_1.
      apply Rle_0_sqr.
      lra.
      apply (Rplus_lt_reg_r (- x²)).
      setl 0.
      setr (y²).
      specialize (Rle_0_sqr y) as y2ge0.
      destruct y2ge0 as [y2gt0|y2eq0];
        [assumption|
         symmetry in y2eq0;
         apply Rsqr_eq_0 in y2eq0; lra ].
    }

    destruct (total_order_T 0 x) as [[zltx |zeqx]|zgtx].
    + rewrite Rabs_right in ax; lra.
    + lra.
    + rewrite Rabs_left in ax; lra.
  }                    
  
  unfold θ1.
  destruct total_order_T as [[zltr2|zeqr] |rgt0]; try lra.
  destruct (total_order_T _ y) as [[zlty2|zeqy] |ygt0]; try lra.
  
  destruct (total_order_T) as [[zltx|zeqx] |xgt0].
  destruct (total_order_T) as [[zlta|zeqa] |agt0].

  + apply (Rmult_lt_reg_r (/2)); try lra.
    setr (θmax / 4).
    setl (atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))).
    apply tan_increasing_pi2.
    apply atan_bound.
    unfold θmax, calcθ₁;
      arn;
      specialize (atan2_bound x y no) as [atl [atu|atu2]]; try lra.
    rewrite atan_right_inv.
    rewrite id.
    specialize (Rplus_lt_le_0_compat _ _ zltx (sqrt_pos (x² - (2 * r - y) * y))) as zltA.
    setl ((x² - (sqrt (x² - (2 * r - y) * y))²)
            / ((2 * r - y)*(x + sqrt (x² - (2 * r - y) * y)))).
    unfold Rsqr in zltA.
    split; lra.
    rewrite Rsqr_sqrt; try (unfold Rsqr in *; lra).

    fieldrewrite (x² - (x² - (2 * r - y) * y)) ((2 * r - y) * y).
    setl (y / (x + sqrt (x² - (2 * r - y) * y))).
    unfold Rsqr in zltA.
    split; lra.
    fieldrewrite (x² - (2 * r - y) * y) (x² + y² - 2 * r * y).
    assert (sqrt (x² + y² - 2 * r * y) < sqrt (x² + y²)) as sro. {
      apply sqrt_lt_1.
      lra.
      left; assumption.
      apply (Rplus_lt_reg_r (- x² - y²)).
      setl (- 2 * r * y).
      setr (- 0).
      setl (- (2 * r * y)).
      apply Ropp_lt_contravar.
      setr (2 * (-r) * (-y)).
      zltab. }

    assert (x² - (2 * r - y) * y = x² + y² - 2 * r * y) as id2. {
      unfold Rsqr. lra. }
    rewrite id2 in zltA.
    assert (0 < x + sqrt (x² + y²)) as zltB. lra.
    
    apply (Rmult_lt_reg_r (/ - y * (x + sqrt (x² + y²)) *
                           (x + sqrt (x² + y² - 2 * r * y)))).
    zltab.
    lra.
    setr (- (x + sqrt (x² + y² - 2 * r * y))).
    unfold Rsqr in *; split; lra.
    setl (- (x + sqrt (x² + y²))).
    unfold Rsqr in *; split; lra.
    lra.

  + symmetry in zeqa.
    apply Rminus_diag_uniq in zeqa.
    apply (Rmult_lt_reg_r (/2 )).
    lra.
    setr (θmax / 4).
    setl (atan (y / (2 * x))).
    apply tan_increasing_pi2.
    apply atan_bound.
    unfold θmax, calcθ₁;
      arn;
      specialize (atan2_bound x y no) as [atl [atu|atu2]]; try lra.
    rewrite atan_right_inv.
    rewrite id.
    apply (Rmult_lt_reg_r (/ - y * (2 * x) * (x + sqrt (x² + y²)))).
    zltab.
    lra.
    setr (- (2 * x)).
    unfold Rsqr in *.
    split; lra.
    setl (- (x + sqrt (x² + y²))).
    lra.
    apply (Rplus_lt_reg_r (x)).
    setr (-x).
    setl (-(sqrt (x² + y²))).
    rewrite <- (Rabs_right x) at 2; try lra.
    rewrite <- (sqrt_Rsqr_abs x).
    apply Ropp_lt_contravar.
    apply sqrt_lt_1.
    ++ apply Rle_0_sqr.
    ++ left. assumption.
    ++ apply (Rplus_lt_reg_r (-(x²))).
       setl 0.
       setr (y²).
       apply Rlt_0_sqr.
       lra.
  + apply (Rmult_lt_reg_r (/2)); try lra.
    setr (θmax / 4).
    setl (atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))).
    apply tan_increasing_pi2.
    apply atan_bound.
    unfold θmax, calcθ₁;
      arn;
      specialize (atan2_bound x y no) as [atl [atu|atu2]]; try lra.
    rewrite atan_right_inv.
    rewrite id.
    specialize (Rplus_lt_le_0_compat _ _ zltx (sqrt_pos (x² - (2 * r - y) * y))) as zltA.
    setl ((x² - (sqrt (x² - (2 * r - y) * y))²)
            / ((2 * r - y)*(x + sqrt (x² - (2 * r - y) * y)))).
    unfold Rsqr in zltA.
    split; lra.
    rewrite Rsqr_sqrt; try (unfold Rsqr in *; lra).

    fieldrewrite (x² - (x² - (2 * r - y) * y)) ((2 * r - y) * y).
    setl (y / (x + sqrt (x² - (2 * r - y) * y))).
    unfold Rsqr in zltA.
    split; lra.
    fieldrewrite (x² - (2 * r - y) * y) (x² + y² - 2 * r * y).
    assert (sqrt (x² + y² - 2 * r * y) < sqrt (x² + y²)) as sro. {
      apply sqrt_lt_1.
      lra.
      left; assumption.
      apply (Rplus_lt_reg_r (- x² - y²)).
      setl (- 2 * r * y).
      setr (- 0).
      setl (- (2 * (- r) * (-y))).
      apply Ropp_lt_contravar.
      zltab. }

    assert (x² - (2 * r - y) * y = x² + y² - 2 * r * y) as id2. {
      unfold Rsqr. lra. }
    rewrite id2 in zltA.
    assert (0 < x + sqrt (x² + y²)) as zltB. lra.
    
    apply (Rmult_lt_reg_r (/ - y * (x + sqrt (x² + y²)) *
                           (x + sqrt (x² + y² - 2 * r * y)))).
    zltab.
    lra.
    setr (- (x + sqrt (x² + y² - 2 * r * y))).
    unfold Rsqr in *; split; lra.
    setl (- (x + sqrt (x² + y²))).
    unfold Rsqr in *; split; lra.
    lra.
  + destruct (total_order_T) as [[zlta|zeqa] |agt0].
    ++ apply (Rmult_lt_reg_r (/2)); try lra.
       setr (θmax / 4).
       setl (atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))).
       apply tan_increasing_pi2.
       apply atan_bound.
       unfold θmax, calcθ₁;
         arn;
         specialize (atan2_bound x y no) as [atl [atu|atu2]]; try lra.
       rewrite atan_right_inv.
       rewrite id.
       
       assert (0 < x + sqrt (x² - (2 * r - y) * y)) as zltA. {
         apply th2_num_sign.
         setr ((2 * r - y) * (-y)).
         apply Rmult_lt_0_compat; lra. }
       
       setl ((x² - (sqrt (x² - (2 * r - y) * y))²)
               / ((2 * r - y)*(x + sqrt (x² - (2 * r - y) * y)))).
       unfold Rsqr in zltA.
       split; lra.
       rewrite Rsqr_sqrt; try (unfold Rsqr in *; lra).
       
       fieldrewrite (x² - (x² - (2 * r - y) * y)) ((2 * r - y) * y).
       setl (y / (x + sqrt (x² - (2 * r - y) * y))).
       unfold Rsqr in zltA.
       split; lra.
       fieldrewrite (x² - (2 * r - y) * y) (x² + y² - 2 * r * y).
       assert (sqrt (x² + y² - 2 * r * y) < sqrt (x² + y²)) as sro. {
         apply sqrt_lt_1.
         lra.
         left; assumption.
         apply (Rplus_lt_reg_r (- x² - y²)).
         setl (- 2 * r * y).
         setr (- 0).
         setl (- (2 * (-r) * (-y))).
         apply Ropp_lt_contravar.
         zltab. }
       
       assert (x² - (2 * r - y) * y = x² + y² - 2 * r * y) as id2. {
         unfold Rsqr. lra. }
       rewrite id2 in zltA.
       assert (0 < x + sqrt (x² + y²)) as zltB. lra.
       
       apply (Rmult_lt_reg_r (/ - y * (x + sqrt (x² + y²)) *
                              (x + sqrt (x² + y² - 2 * r * y)))).
       zltab.
       lra.
       setr (- (x + sqrt (x² + y² - 2 * r * y))).
       unfold Rsqr in *; split; lra.
       setl (- (x + sqrt (x² + y²))).
       unfold Rsqr in *; split; lra.
       lra.
    ++ exfalso.
       rewrite <- zeqx, Rsqr_0, Rplus_0_l in phase.
       symmetry in zeqa.
       apply Rminus_diag_uniq_sym in zeqa.
       rewrite <- zeqa in phase.
       unfold Rsqr in phase.
       lra.
    ++ exfalso.
       rewrite <- zeqx, Rsqr_0, Rplus_0_l in phase.
       assert (y² < 2 * r * y) as p2. {
         apply (Rmult_lt_reg_r (/ - y)).
         zltab.
         unfold Rsqr.
         lra.
         setl (-y); try lra.
         setr (2 * (-r)); try lra. }
         lra.
       
  + set (A := ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))) in *.
    specialize (atan_bound A) as [atl atu].
    assert (- PI < θmax / 2 < PI) as [tml tmu]. {
      specialize (atan2_bound x y no) as [at2l at2u].
      unfold θmax,calcθ₁.
      arn.
      fieldrewrite (2 * atan2 y x / 2) (atan2 y x).
      lra. }
    destruct (total_order_T) as [[zlta|zeqa] |agt0].
    ++ unfold A in *.
       apply (Rmult_lt_reg_r (/2)); try lra.
       setr (θmax / 4).
       setl (atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))).
       apply tan_increasing_pi2.
       apply atan_bound.
       lra.
       rewrite atan_right_inv.
       rewrite id.

       assert (0 < x + sqrt (x² - (2 * r - y) * y)) as zltA. {
         apply th2_num_sign.
         setr ((2 * r - y) * (-y)).
         apply Rmult_lt_0_compat; lra. }

       setl ((x² - (sqrt (x² - (2 * r - y) * y))²)
               / ((2 * r - y)*(x + sqrt (x² - (2 * r - y) * y)))).
       unfold Rsqr in zltA.
       split; lra.
       rewrite Rsqr_sqrt; try (unfold Rsqr in *; lra).
       
       fieldrewrite (x² - (x² - (2 * r - y) * y)) ((2 * r - y) * y).
       setl (y / (x + sqrt (x² - (2 * r - y) * y))).
       unfold Rsqr in zltA.
       split; lra.
       fieldrewrite (x² - (2 * r - y) * y) (x² + y² - 2 * r * y).
       assert (sqrt (x² + y² - 2 * r * y) < sqrt (x² + y²)) as sro. {
         apply sqrt_lt_1.
         lra.
         left; assumption.
         apply (Rplus_lt_reg_r (- x² - y²)).
         setl (- 2 * r * y).
         setr (- 0).
         setl (- (2 * (-r) * (-y))).
         apply Ropp_lt_contravar.
         zltab. }
       
       assert (x² - (2 * r - y) * y = x² + y² - 2 * r * y) as id2. {
         unfold Rsqr. lra. }
       rewrite id2 in zltA.
       assert (0 < x + sqrt (x² + y²)) as zltB. lra.
       
       apply (Rmult_lt_reg_r (/ - y * (x + sqrt (x² + y²)) *
                              (x + sqrt (x² + y² - 2 * r * y)))).
       zltab.
       lra.
       setr (- (x + sqrt (x² + y² - 2 * r * y))).
       unfold Rsqr in *; split; lra.
       setl (- (x + sqrt (x² + y²))).
       unfold Rsqr in *; split; lra.
       lra.
    ++ lra.
    ++ lra.
Qed.

Lemma tinrng :
  forall θ₀ x₀ y₀ x₁ y₁ r
         (phaser : straight r θ₀ x₀ y₀ x₁ y₁),
    let θr := θ1 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) r in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (stp : 0 < r * θr < Rabs r * 2 * PI),
    (0 < θmax /\ (θmax/2 < θr < θmax \/ - 2*PI < θr < θmax/2 - 2*PI)) \/
    (θmax < 0 /\ (θmax < θr < θmax/2 \/ θmax/2 + 2*PI < θr < 2*PI)).
Proof.
  intros.
  apply straight_rot in phaser.
  unfold θmax.
  clear θmax.
  rewrite calc_angle_std in *.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  set (θmax := calcθ₁ 0 0 0 x y) in *.
  unfold θr in *.
  destruct stp as [rtlb rtub].

  generalize rtlb; intro zner; apply rtp_zner in zner.
  generalize rtlb; rewrite Rmult_comm; intro znet; apply rtp_zner in znet.
  assert (r <> 0) as rne0. lra.
  specialize (theta1_rsgn_lim _ _ _ rne0 phaser) as [rgtr rltr].
  specialize (theta1_rng _ _ _ rne0 phaser) as [tlb tub].
  
  destruct (total_order_T 0 r) as [s |zgtr]; [destruct s as [zltr| zeqr]|].
  + specialize (rgtr zltr);
         destruct rgtr as [zltt |zeqt]; [ clear rltr |lra].
    destruct (total_order_T 0 y) as [s |zgty]; [destruct s as [zlty| zeqy]|].
    ++ specialize (root_ordering_rpos_left _ _ _ zltr zlty phaser)
        as [rol rou].
       change (θ1 x y r < θmax) in rol.
       change (θmax < θ2 x y r) in rou.
       left.
       split; try lra.
       left.
       split; try assumption.
       apply tm2ltt1; assumption.
    ++ destruct (total_order_T 0 x) as [s |zgtx];
         [destruct s as [zltx| zeqx]|].
       +++ assert (θ1 x y r = 0) as t1eq0. {
             unfold θ1.
             destruct total_order_T; [destruct s|]; try lra.
             destruct total_order_T; [destruct s|]; try lra.
             destruct total_order_T; [destruct s|]; try lra. }
           lra.
       +++ apply straightcond in phaser.
           rewrite <- zeqy, <- zeqx in phaser.
           autorewrite with null in phaser.
           lra.
       +++ assert (θ1 x y r = 2 * atan (x / r) + 2 * PI) as t1eq0. {
             unfold θ1.
             destruct total_order_T; [destruct s|]; try lra.
             destruct total_order_T; [destruct s|]; try lra.
             destruct total_order_T; [destruct s|]; try lra.
             rewrite <- e.
             arn.
             rewrite sqrt_Rsqr_abs, Rabs_left; try lra.
             fieldrewrite ((x - - x) / (2 * r)) (x / r); try lra. }
           assert (θmax = 2 * PI) as tmeq0. {
             unfold θmax,calcθ₁.
             arn.
             rewrite <- zeqy.
             apply Rmult_eq_compat_l.
             rewrite atan2_PI; try lra. }
           left.
           split; try lra.
           left.
           rewrite t1eq0, tmeq0.
           split; try lra.
           apply (Rmult_lt_reg_r (/ 2)); try lra.
           apply (Rplus_lt_reg_r (-PI)).
           setl (- PI / 2).
           setr (atan (x / r)).
           apply (atan_bound (x/r)).
    ++ specialize (root_ordering_rpos_right _ _ _ zltr zgty phaser)
         as [rol rou].
       change (θ2 x y r < θmax / 2 + 2 * PI) in rol.
       change (θmax / 2 + 2 * PI < θ1 x y r) in rou.
       lra.
  + lra.
  + specialize (rltr zgtr);
      destruct rltr as [tltz |teqz]; [ clear rgtr |lra].
    destruct (total_order_T 0 y) as [s |zgty]; [destruct s as [zlty| zeqy]|].
    ++ specialize (root_ordering_rneg_left _ _ _ zgtr zlty phaser)
        as [rol rou].
       change (θ1 x y r < θmax / 2 - 2 * PI) in rol.
       change (θmax / 2 - 2 * PI < θ2 x y r) in rou.
       lra.
    ++ destruct (total_order_T 0 x) as [s |zgtx];
         [destruct s as [zltx| zeqx]|].
       +++ assert (θ1 x y r = 0) as t1eq0. {
             unfold θ1.
             destruct total_order_T; [destruct s|]; try lra.
             destruct total_order_T; [destruct s|]; try lra.
             destruct total_order_T; [destruct s|]; try lra. }
           lra.
       +++ apply straightcond in phaser.
           rewrite <- zeqy, <- zeqx in phaser.
           autorewrite with null in phaser.
           lra.
       +++ assert (θ1 x y r = 2 * atan (x / r) - 2 * PI) as t1eq0. {
             unfold θ1.
             destruct total_order_T; [destruct s|]; try lra.
             destruct total_order_T; [destruct s|]; try lra.
             destruct total_order_T; [destruct s|]; try lra.
             rewrite <- e.
             arn.
             rewrite sqrt_Rsqr_abs, Rabs_left; try lra.
             fieldrewrite ((x - - x) / (2 * r)) (x / r); try lra. }
           assert (θmax = 2 * PI) as tmeq0. {
             unfold θmax,calcθ₁.
             arn.
             rewrite <- zeqy.
             apply Rmult_eq_compat_l.
             rewrite atan2_PI; try lra. }
           left.
           split; try lra.
           right.
           rewrite t1eq0, tmeq0.
           split; try lra.
           apply (Rplus_lt_reg_r (2 * PI)).
           apply (Rmult_lt_reg_r (/ 2)); try lra.
           setr (PI / 2).
           setl (atan (x / r)).
           apply (atan_bound (x/r)).
    ++ specialize (root_ordering_rneg_right _ _ _ zgtr zgty phaser)
         as [rol rou].
       change (θ2 x y r < θmax) in rol.
       change (θmax < θ1 x y r) in rou.
       right.
       split; try lra.
       left.
       split; try assumption.
       apply t1lttm2; assumption.
Qed.

Lemma tmax_radius :
  forall x y (nx : y <> 0),
    let θmax := calcθ₁ 0 0 0 x y in
    (x² + y²) / (2 * y) = (x * sin θmax - y * cos θmax) / (1 - cos θmax).
Proof.
  intros.
  rewrite Rplus_comm.
  assert (~ (x = 0 /\ y = 0)) as nO; try lra.

  assert (cos θmax <> 1) as ctmne1. {
    unfold θmax.
    rewrite (calcth1_atan2_s x y) in *.
    clear θmax.
    unfold atan2.
    destruct pre_atan2 as [q [[ql qu] [yd xd]]].
    intro c2a2eq1.
    destruct (Rle_dec 0 q) as [zleq | zgtq].
    + apply cos_eq_1_2PI_0 in c2a2eq1; try lra.
      destruct c2a2eq1 as [tqeq0 | qeq2pi].
      assert (q = 0) as qeq0; try lra.
      rewrite qeq0, sin_0 in yd.
      autorewrite with null in yd.
      lra.
      assert (q = PI) as qeqpi; try lra.
      rewrite qeqpi, sin_PI in yd.
      autorewrite with null in yd.
      lra.
    + apply Rnot_le_lt in zgtq.
      rewrite <- cos_neg in c2a2eq1.
      assert (- (2 * q) = 2 * -q) as id; try lra.
      rewrite id in c2a2eq1; clear id.
      apply cos_eq_1_2PI_0 in c2a2eq1; try lra. }

  unfold θmax in *.
  rewrite (calcth1_atan2_s x y) in *.
  clear θmax.
  unfold atan2 in *.
  destruct pre_atan2 as [q [[ql qu] [yd xd]]].
  rewrite yd at 2 3.
  rewrite xd at 3.
  specialize (posss x y nO) as zltx2y2.
  rewrite Rplus_comm in zltx2y2.
  assert (0 < sqrt (y² + x²)) as ssq;
    try (apply sqrt_lt_R0; assumption).
  rewrite <- (sqrt_def (y² + x²)) at 1;
    try (left; assumption).
  fieldrewrite (sqrt (y² + x²) * cos q * sin (2 * q) -
                sqrt (y² + x²) * sin q * cos (2 * q))
               (sqrt (y² + x²) * (sin (2 * q) * cos q  -
                                   cos (2 * q) * sin q)).
  rewrite <- sin_minus.
  assert (sin q <> 0) as sinqne0. {
    intro sinqeq0.
    apply nx.
    rewrite yd, sinqeq0.
    arn.
    reflexivity. }
    
  fieldrewrite (2 * q - q) q.
  rewrite <- RmultRinv.
  repeat rewrite Rinv_mult_distr; try lra.
  
  setl (sqrt (y² + x²) * / 2 * / sin q).
  split; try assumption.
  unfold Rsqr in ssq.
  intro sqrteq0.
  rewrite sqrteq0 in ssq.
  lra.
  apply (Rmult_eq_reg_r ((/ sqrt (y² + x²)) * sin q));
    [| apply Rmult_integral_contrapositive_currified;
       zltab].
  setl (1/2).
  split; zltab.
  unfold Rsqr in ssq.
  intro sqrteq0.
  rewrite sqrteq0 in ssq.
  lra.
  repeat rewrite <- RmultRinv.
  apply (Rmult_eq_reg_r (2 * (1 - cos (2 * q))));
    try zltab.
  setr (2 * (sin q)²).
  split; zltab.
  unfold Rsqr in ssq.
  intro sqrteq0.
  rewrite sqrteq0 in ssq.
  lra.
  setl (1 - cos (2 * q)).
  apply (Rplus_eq_reg_r (cos (2 * q) - 2 * sin q * sin q)).
  symmetry.
  setl (cos (2 * q)).
  setr (1 - 2 * sin q * sin q).
  apply cos_2a_sin.
Qed.

Lemma t1eqtm :
  forall x y (nO : ~ (x = 0 /\ y = 0)),
    let θmax := calcθ₁ 0 0 0 x y in
    let r := (y² + x²) / (2 * y) in
    y <> 0 -> θ1 x y r = θmax.
Proof.
  intros *.
  intros nO.
  intros *.
  intros yne0.
  assert (y <> 0 \/ x <> 0) as n2; try lra.

  specialize (posss _ _ nO) as zltx2y2.
  unfold θ1, θmax.
  rewrite (calcth1_atan2_s x y) in *.
  unfold atan2.
  clear θmax.
  destruct pre_atan2 as [q [[ql qu] [yd xd]]].
  assert (x² - (2 * r - y) * y = 0) as z. {
    unfold r.
    setl 0; try assumption.
    reflexivity. }
  rewrite z, sqrt_0.
  arn.
  assert (2 * r - y = x²/y) as id. {
    unfold r.
    apply (Rmult_eq_reg_r y); try lra.
    setl (x²); try assumption.
    setr (x²); try assumption.
    reflexivity. }
  rewrite id.
  set (M := sqrt (y² + x²)) in *.
  assert (0 < M) as zltm;
    try (apply sqrt_lt_R0; lra).
  destruct (total_order_T 0 x); [destruct s|].
  + fieldrewrite (x / (x² / y)) (y / x);
      try lra.
    destruct (total_order_T 0 y); [destruct s|]; try lra.
    ++ assert (0 < x² / y) as gt0. {
         unfold Rsqr.
         rewrite <- RmultRinv.
         zltab. }
       destruct (total_order_T 0 (x² / y));
          [destruct s|]; try lra.
       assert (0 < r) as zltr. {
         unfold r.
         rewrite <- RmultRinv.
         zltab. }
       destruct (total_order_T 0 r);
          [destruct s|]; try lra.
       assert (cos q <> 0) as cqne0. {
         intro cqeq0.
         rewrite cqeq0 in xd.
         autorewrite with null in xd.
         rewrite xd in r0.
         lra. }
       apply Rmult_eq_compat_l.
       assert (0 < q < PI / 2) as qrng. {
         specialize (atan2_val _ _ _ (conj ql qu) n2 yd xd) as qd.
         rewrite <- qd.
         apply atan2Q1; assumption. }
       unfold atan.
       destruct pre_atan as [p [pr tp]].
       apply tan_is_inj.
       assumption.
       lra.
       rewrite tp, yd, xd.
       setl (sin q / cos q); try lra.
       reflexivity.
    ++ assert (x² / y < 0) as gt0. {
         setl (-(x * x * / -y)); try lra.
         rewrite <- Ropp_0.
         apply Ropp_lt_contravar.
         zltab.
         lra. }
       destruct (total_order_T 0 (x² / y));
          [destruct s|]; try lra.
       assert (r < 0) as zltr. {
         unfold r.
         setl (- ((y² + x²) / (2 * - y))); try lra.
         rewrite <- Ropp_0.
         apply Ropp_lt_contravar.
         zltab. }
       destruct (total_order_T 0 r);
          [destruct s|]; try lra.
       assert (cos q <> 0) as cqne0. {
         intro cqeq0.
         rewrite cqeq0 in xd.
         autorewrite with null in xd.
         rewrite xd in r0.
         lra. }
       apply Rmult_eq_compat_l.
       assert (- PI / 2 < q < 0) as qrng. {
         specialize (atan2_val _ _ _ (conj ql qu) n2 yd xd) as qd.
         rewrite <- qd.
         fieldrewrite (- PI / 2) (- (PI / 2)).
         apply atan2Q4; assumption. }
       unfold atan.
       destruct pre_atan as [p [pr tp]].
       apply tan_is_inj.
       assumption.
       lra.
       rewrite tp, yd, xd.
       setl (sin q / cos q); try lra.
       reflexivity.
  + rewrite <- e in *.
    rewrite <- RmultRinv in *.
    autorewrite with null in *.
    clear z nO.
    
    assert (cos q = 0) as cqeq0; 
      try (apply (Rmult_eq_reg_l M); lra).
    apply cosθeq0 in cqeq0; try lra.
    destruct cqeq0 as [qeqpi2 | qeqnpi2].

    rewrite qeqpi2, sin_PI2 in yd.
    assert (0 < y) as zlty; try lra.
    autorewrite with null in *.
    
    assert (0 < r) as zltr. {
      unfold r.
      rewrite <- e.
      arn.
      rewrite <- RmultRinv.
      zltab. }

    destruct total_order_T; [destruct s|]; try lra.
    destruct total_order_T; [destruct s|]; try lra.
    destruct total_order_T; [destruct s|]; try lra.

    rewrite qeqnpi2 in yd.
    assert (- PI / 2 = - (PI / 2)) as id2; try lra.
    rewrite id2 in yd; clear id2.
    rewrite sin_neg, sin_PI2 in yd.
    assert (y < 0) as zlty; try lra.
    autorewrite with null in *.
    
    assert (r < 0) as zltr. {
      unfold r.
      rewrite <- e.
      arn.
      setl (- ((-y) / 2)); try lra. }

    destruct total_order_T; [destruct s|]; try lra.
    destruct total_order_T; [destruct s|]; try lra.
    destruct total_order_T; [destruct s|]; try lra.
    
  + fieldrewrite (x / (x² / y)) (y / x);
      try lra.
    destruct (total_order_T 0 y); [destruct s|]; try lra.
    ++ assert (0 < x² / y) as gt0. {
         setr (-x * -x * / y); try lra.
         zltab. }
       destruct (total_order_T 0 (x² / y));
          [destruct s|]; try lra.
       assert (0 < r) as zltr. {
         unfold r.
         rewrite <- RmultRinv.
         zltab. }
       destruct (total_order_T 0 r);
          [destruct s|]; try lra.
       assert (cos q <> 0) as cqne0. {
         intro cqeq0.
         rewrite cqeq0 in xd.
         autorewrite with null in xd.
         rewrite xd in r0.
         lra. }
       setl (2 * (atan (y / x) + PI)).
       apply Rmult_eq_compat_l.
       assert (PI / 2 < q < PI) as qrng. {
         specialize (atan2_val _ _ _ (conj ql qu) n2 yd xd) as qd.
         rewrite <- qd.
         apply atan2Q2; assumption. }
       unfold atan.
       destruct pre_atan as [p [pr tp]].
       apply (Rplus_eq_reg_r (-PI)).
       setl p.
       setr (q + IZR (- 1) * PI).
       apply tan_is_inj.
       assumption.
       lra.
       rewrite tp, yd, xd.
       setl (sin q / cos q); try lra.
       rewrite tan_period; try assumption.
       reflexivity.
    ++ assert (x² / y < 0) as gt0. {
         setl (-(- x * - x * / -y)); try lra.
         rewrite <- Ropp_0.
         apply Ropp_lt_contravar.
         zltab.
         lra. }
       destruct (total_order_T 0 (x² / y));
          [destruct s|]; try lra.
       assert (r < 0) as zltr. {
         unfold r.
         setl (- ((y² + x²) / (2 * - y))); try lra.
         rewrite <- Ropp_0.
         apply Ropp_lt_contravar.
         zltab. }
       destruct (total_order_T 0 r);
          [destruct s|]; try lra.
       assert (cos q <> 0) as cqne0. {
         intro cqeq0.
         rewrite cqeq0 in xd.
         autorewrite with null in xd.
         rewrite xd in r0.
         lra. }
       setl (2 * (atan (y / x) - PI)).
       apply Rmult_eq_compat_l.
       assert (- PI < q < - PI / 2) as qrng. {
         specialize (atan2_val _ _ _ (conj ql qu) n2 yd xd) as qd.
         rewrite <- qd.
         fieldrewrite (- PI / 2) (- (PI / 2)).
         apply atan2Q3; assumption. }
       unfold atan.
       destruct pre_atan as [p [pr tp]].
       apply (Rplus_eq_reg_r PI).
       setl p.
       setr (q + 1 * PI).
       apply tan_is_inj.
       assumption.
       lra.
       rewrite tan_period; try assumption.
       rewrite tp, yd, xd.
       setl (sin q / cos q); try lra.
       reflexivity.
Qed.
(* end hide *)

Lemma tmax_radius_gen :
  forall θ₀ x₀ y₀ x₁ y₁,
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (tmaxne0 : θmax <> 0)
           (tmaxne2PI : θmax <> 2 * PI),
    (x² + y²) / (2 * y) = (x * sin θmax - y * cos θmax) / (1 - cos θmax).
Proof.
  intros.

  unfold θmax in *; clear θmax.
  rewrite calc_angle_std in *.

  unfold x, y in *; clear x y.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.

  specialize (notid_rot θ₀ _ _ _ _ no) as not.
  simpl in not.
  change (~ (x = 0 /\ y = 0)) in not.
    
  set (θmax := calcθ₁ 0 0 0 x y) in *.

  assert (y <> 0) as yne0. {
    intros yeq0.
    apply thmaxne0impl in tmaxne0.
    apply thmaxnePIimpl in tmaxne2PI.
    lra. }

  apply tmax_radius; assumption.
Qed.

Lemma t1eqtm_gen :
  forall θ₀ x₀ y₀ x₁ y₁,
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let r := (y² + x²) / (2 * y) in
    forall (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (tmaxne0 : θmax <> 0)
           (tmaxne2PI : θmax <> 2 * PI),
      θ1 x y r = θmax.
Proof.
  intros.

  unfold θmax in *; clear θmax.
  rewrite calc_angle_std in *.

  unfold x, y in *; clear x y.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.

  specialize (notid_rot θ₀ _ _ _ _ no) as not.
  simpl in not.
  change (~ (x = 0 /\ y = 0)) in not.
    
  set (θmax := calcθ₁ 0 0 0 x y) in *.

  assert (y <> 0) as yne0. {
    intros yeq0.
    apply thmaxne0impl in tmaxne0.
    apply thmaxnePIimpl in tmaxne2PI.
    lra. }
  apply t1eqtm; assumption.
Qed.

(* begin hide *)

Lemma theta1_Q1_cont :
  forall r x y
         (xeq0 : 0 <= x)
         (ygt0 : 0 < y),
    let rz := (x² + y²) / (2 * y) in
    let θ1_altx :=
        extension_C0 (fun r => r * (2 * (PI / 2 - atan ((x + sqrt (x² - (2 * r - y) * y)) / y)))) 0 rz in
    let θ1_Q1 := extension_C0 (fun r => r * θ1 x y r) 0 rz in
    continuous θ1_Q1 r.
Proof.
  intros.
  assert (θ1_Q1 = θ1_altx) as P.
  { apply functional_extensionality.
    intros t.
    unfold θ1_altx, θ1_Q1, extension_C0.
    specialize (atan2_atan_Q1Q2 y
                                (x + sqrt (x² - (2 * rz - y) * y))
                                ygt0) as Q.
    specialize (atan2_atan_Q1Q2 y
                                (x + sqrt (x² - (2 * t - y) * y))
                                ygt0) as Q0.
    repeat destruct Rbar_le_dec.
    - rewrite <- Q0.
      unfold θ1; simpl in *.
      repeat (destruct total_order_T;[destruct s|]; try lra).
      + assert (0 < (x + sqrt (x² - (2 * t - y) * y))) as P.
        { apply Rplus_lt_le_0_compat;[auto |apply sqrt_pos]. }
        rewrite atan2_atan_Q1Q4, <- RmultRinv; try lra.
        apply Rmult_eq_compat_l.
        apply Rmult_eq_compat_l, f_equal,
        (Rmult_eq_reg_l (x + sqrt (x² - (2 * t - y) * y)));[|lra].
        setl ((x² - (sqrt (x² - (2 * t - y) * y))²) * /(2 * t - y))
        ; try lra.
        rewrite Rsqr_sqrt; try field; try lra.
        unfold rz in r1.
        unfold Rsqr in *.
        fieldrewrite (x * x - (2 * t - y) * y)
                     (x * x + y * y - 2 * t * y). 
        enough (2 * t * y <= x * x + y * y) by lra.
        rewrite <- RmultRinv in r1.
        apply (Rmult_le_compat_r (2 * y)) in r1; [|lra].
        rewrite Rmult_assoc, Rinv_l in r1; try lra.
      + assert (0 < (x + sqrt (x² - (2 * t - y) * y))) as P.
        { apply Rplus_lt_le_0_compat;[auto |apply sqrt_pos]. }
        rewrite atan2_atan_Q1Q4, <- RmultRinv; try lra.
        rewrite <- e, Rmult_0_l, Rminus_0_r, sqrt_Rsqr, (double x)
        ;[reflexivity|lra].
      + assert (0 < (x + sqrt (x² - (2 * t - y) * y))) as P.
        { apply Rplus_lt_le_0_compat;[auto |apply sqrt_pos]. }
        rewrite atan2_atan_Q1Q4, <- RmultRinv; try lra.
        apply Rmult_eq_compat_l.
        apply Rmult_eq_compat_l, f_equal,
        (Rmult_eq_reg_l (x + sqrt (x² - (2 * t - y) * y)));[|lra].
        setl ((x² - (sqrt (x² - (2 * t - y) * y))²) * /(2 * t - y))
        ; try lra.
        rewrite Rsqr_sqrt; try field; try lra.
        unfold rz in r1.
        unfold Rsqr in *.
        fieldrewrite (x * x - (2 * t - y) * y)
                     (x * x + y * y - 2 * t * y). 
        enough (2 * t * y <= x * x + y * y) by lra.
        rewrite <- RmultRinv in r1.
        apply (Rmult_le_compat_r (2 * y)) in r1; [|lra].
        rewrite Rmult_assoc, Rinv_l in r1; try lra.
      + exfalso.
        unfold rz, Rsqr in r1.
        apply (Rmult_le_compat_r (2 * y)) in r1; try lra.
        apply (Rmult_lt_compat_r y) in r4; try lra.
        rewrite <- e, Rmult_0_l, Rplus_0_l, <- RmultRinv,
        Rmult_assoc, Rinv_l in r1; lra.
      + rewrite <- e, <- e0, Rplus_0_l, Rmult_0_l, Rminus_0_r, Rsqr_0,
        sqrt_0.
        rewrite atan2_PI2; lra.
      + do 2 f_equal.
        assert (0 < (x + sqrt (x² - (2 * t - y) * y))) as P.
        { rewrite <- e, Rplus_0_l, Rsqr_0, Rminus_0_l,
          Ropp_mult_distr_l.
          apply sqrt_lt_R0, Rmult_lt_0_compat; lra.
        }
        rewrite atan2_atan_Q1Q4, <- RmultRinv, <- RmultRinv; try lra.
        f_equal.
        rewrite <- e, Rsqr_0, Rplus_0_l,
        <- (Ropp_involutive (/ (2 * t - y)));
          repeat rewrite Rminus_0_l.
        rewrite Rmult_opp_opp, Ropp_inv_permute; try lra.
        assert (0 < sqrt (- ((2 * t - y) * y))) as P0.
        { rewrite Ropp_mult_distr_l.
          apply sqrt_lt_R0, Rmult_lt_0_compat; lra.
        }
        apply (Rmult_eq_reg_l (sqrt (- ((2 * t - y) * y)))); try lra.
        rewrite <- Rmult_assoc, sqrt_def; rewrite Ropp_mult_distr_l;
          [|left; apply Rmult_lt_0_compat; lra].
        rewrite Rmult_comm, <- Rmult_assoc, Rinv_l, Rmult_1_l; try lra.
        rewrite Rmult_comm, Rmult_assoc, Rinv_l, Rmult_1_r; try lra.
        rewrite Ropp_mult_distr_l in *; lra.
      + rewrite <- e; repeat rewrite Rmult_0_l; reflexivity.
    - setoid_rewrite <- Q.
      unfold rz, θ1, Rsqr in *.
      assert ((x * x - (2 * ((x * x + y * y) / (2 * y)) - y) * y) = 0)
        as P.
      { field; lra. }
      assert ((2 * ((x * x + y * y) / (2 * y)) - y) = (x * x */y))
        as P0.
      { field; lra. }
      repeat (destruct total_order_T;[destruct s|]; try lra).
      + assert (0 < (x + sqrt (x² - (2 * rz - y) * y))) as P1.
        { apply Rplus_lt_le_0_compat;[auto |apply sqrt_pos]. }
        rewrite atan2_atan_Q1Q4, <- RmultRinv; unfold rz, Rsqr in *
        ;auto.
        do 3 f_equal.
        setoid_rewrite P.
        setoid_rewrite P0.
        rewrite sqrt_0, Rplus_0_r, Rminus_0_r.
        field; lra.
      + exfalso.
        symmetry in e.
        apply Rminus_diag_uniq, (Rmult_eq_compat_r (2 * y)) in e.
        rewrite <- RmultRinv, Rmult_assoc in e.
        setoid_rewrite Rmult_assoc in e.
        rewrite Rinv_l in e; try lra.
        enough (x * x = 0); try lra.
        destruct (Rmult_integral _ _ H); lra.
      + exfalso.
        setoid_rewrite P0 in r4.
        apply (Rmult_gt_compat_r y) in r4; try lra.
        rewrite Rmult_assoc, Rinv_l, Rmult_0_l, Rmult_1_r in r4;
          try lra.
        specialize (Rle_0_sqr x) as P1; unfold Rsqr in P1; lra.
      + repeat rewrite <- e; repeat rewrite Rmult_0_l; reflexivity.
      + exfalso.
        apply (Rmult_gt_compat_r (2 * y)) in r3; try lra.
        rewrite <- RmultRinv, Rmult_0_l in r3.
        setoid_rewrite Rmult_assoc in r3.
        rewrite Rinv_l, Rmult_1_r in r3; try lra.
        specialize (Rle_0_sqr x) as P1;
          specialize (Rle_0_sqr y) as P2.
        unfold Rsqr in *; lra.
      + exfalso.
        setoid_rewrite P0 in r3.
        rewrite <- e in r3.
        repeat rewrite Rmult_0_l in r3; lra.
      + do 2 f_equal.
        setoid_rewrite P.
        rewrite <- e, sqrt_0, Rplus_0_l, atan2_PI2; lra.
      + exfalso.
        setoid_rewrite P0 in r3.
        rewrite <- e in r3.
        repeat rewrite Rmult_0_l in r3; lra.
      + exfalso.
        apply (Rmult_eq_compat_r y) in P0.
        setoid_rewrite <- e0 in P0.
        rewrite Rmult_0_r, Rminus_0_l, Rmult_assoc, Rinv_l, Rmult_1_r,
        <- Ropp_mult_distr_l in P0; try lra.
        specialize (Rle_0_sqr x) as TMP;
          specialize (Rlt_0_sqr y ltac:(lra)) as TMP0;
          unfold Rsqr in *; lra.
      + exfalso.
        apply (Rmult_gt_compat_r (2 * y)) in r2; try lra.
        rewrite <- RmultRinv, Rmult_0_l in r2.
        setoid_rewrite Rmult_assoc in r2.
        rewrite Rinv_l, Rmult_1_r in r2; try lra.
        specialize (Rle_0_sqr x) as P1;
          specialize (Rle_0_sqr y) as P2.
        unfold Rsqr in *; lra.
    - repeat rewrite Rmult_0_l; reflexivity.
  }
  rewrite P.
  unfold θ1_altx.
  - simpl; unfold rz.
    apply extension_C0_continuous.
    + rewrite <- RmultRinv.
      apply Rle_mult_inv_pos; try lra.
      specialize (Rle_0_sqr x) as P0; specialize (Rle_0_sqr y) as P1.
      lra.
    + intros.
      apply continuity_pt_impl_continuous_pt, continuity_pt_mult,
      continuity_pt_mult;
        [apply continuity_pt_id
        |apply continuity_pt_const; unfold constant; auto | ].
      apply continuity_pt_minus;
        [apply continuity_pt_const; unfold constant; auto|].
      apply(continuity_pt_comp
              (fun z => ((x + sqrt (x² - (2 * z - y) * y))/y)) atan)
      ; [| apply derivable_continuous_pt, derivable_pt_atan].
      apply continuity_pt_div;
        [ |apply continuity_pt_const; unfold constant; auto |lra ].
      apply continuity_pt_plus, (continuity_pt_comp _ sqrt);
        [apply continuity_pt_const; unfold constant; auto| | ].
      * apply derivable_continuous_pt; auto_derive; auto.
      * apply continuity_pt_sqrt; simpl in *; unfold rz in *.
        fieldrewrite (x² - (2 * x0 - y) * y) (x² + y² - x0 * (2 * y)).
        apply (Rmult_le_compat_r (2 * y)) in H0.
        rewrite <- RmultRinv, Rmult_assoc, Rinv_l, Rmult_1_r in H0
        ; try lra.
        lra.
Qed.

Lemma theta1_Q2_cont :
  forall r x y
         (xgt0 : x < 0)
         (ygt0 : 0 < y),
    let rz := (x² + y²) / (2 * y) in
    let θ1_alt := extension_C0 (fun r =>
                                  r * (2 * (PI / 2
                                            - atan ((2 * r - y)
                                                      / (x - sqrt (x² - (2 * r - y) * y)))))) 0 rz in
    let θ1_Q2 := extension_C0 (fun r => r * θ1 x y r) 0 rz in
    continuous θ1_Q2 r.
Proof.
  intros.
  assert (θ1_alt = θ1_Q2) as P.
  { apply functional_extensionality; intro t.
    assert ((x - sqrt (x² - (2 * t - y) * y)) < 0) as nn. {
      specialize (sqrt_pos (x² - (2 * t - y) * y)) as sqp.
      lra. }
    assert (((2 * rz - y) / (x - sqrt (x² - (2 * rz - y) * y)))
            = x/y) as nn2.
    { unfold rz.
      fieldrewrite ((2 * ((x² + y²) / (2 * y)) - y) * y) (x²); [lra|].
      rewrite Rminus_eq_0, sqrt_0, Rminus_0_r.
      fieldrewrite (2 * ((x² + y²) / (2 * y)) - y) (x²/y); try lra.
      unfold Rsqr; field; split; lra.
    }
    unfold θ1_alt, θ1_Q2.
    unfold extension_C0.
    repeat destruct Rbar_le_dec.
    - unfold θ1.
      repeat (destruct total_order_T;[destruct s|]; try lra).
      + fieldrewrite ((2 * t - y) / (x - sqrt (x² - (2 * t - y) * y)))
                   ((- (2 * t - y)) / (- (x - sqrt (x² - (2 * t - y) * y)))).
      fold (Rsqr x).
      lra.
      rewrite <- atan2_atan_Q1Q2 ;[|lra].
      rewrite atan2_atan_Q2; [|lra|lra].
      fieldrewrite ((- (x - sqrt (x² - (2 * t - y) * y)))/(- (2 * t - y)))
                 ((x - sqrt (x² - (2 * t - y) * y))/ (2 * t - y)); lra.
      + fieldrewrite ((2 * t - y) / (x - sqrt (x² - (2 * t - y) * y)))
                   ((- (2 * t - y)) / (- (x - sqrt (x² - (2 * t - y) * y)))).
        * fold (Rsqr x); lra.
        * rewrite <- atan2_atan_Q1Q2; [|lra].
          symmetry in e.
          rewrite e in *.
          rewrite Ropp_0, Rmult_0_l, Rminus_0_r.
          rewrite sqrt_Rsqr_abs.
          rewrite Rabs_left; [|lra].
          fieldrewrite (- (x - - x)) (- (2 * x)).
          rewrite atan2_PI2; lra.
      + fieldrewrite ((2 * t - y) / (x - sqrt (x² - (2 * t - y) * y)))
                     ((- (2 * t - y)) / (- (x - sqrt (x² - (2 * t - y) * y)))).
        * fold (Rsqr x); lra.
        * rewrite <- atan2_atan_Q1Q2; [|lra].
          rewrite atan2_atan_Q1; [|lra|lra].
          fieldrewrite ((- (x - sqrt (x² - (2 * t - y) * y)))/(- (2 * t - y)))
                       ((x - sqrt (x² - (2 * t - y) * y))/ (2 * t - y)); lra.
      + fieldrewrite ((2 * t - y) / (x - sqrt (x² - (2 * t - y) * y)))
                     ((- (2 * t - y)) / (- (x - sqrt (x² - (2 * t - y) * y)))).
        * fold (Rsqr x); lra.
        * rewrite <- atan2_atan_Q1Q2; [|lra].
          rewrite <- e; repeat rewrite Rmult_0_l; reflexivity.
      + exfalso.
        simpl in *; lra.
    - apply f_equal; simpl in *.
      unfold rz, θ1.
      repeat (destruct total_order_T;[destruct s|]; try lra).
      + fold rz.
        rewrite nn2.
        rewrite <- atan2_atan_Q1Q2; try lra.
        rewrite atan2_atan_Q2; try lra.
        assert ((x - sqrt (x² - (2 * rz - y) * y)) / (2 * rz - y) =
                y/x) as P0.
        { unfold rz.
          fieldrewrite ((2 * ((x² + y²) / (2 * y)) - y) * y) (x²);
            [lra|].
          rewrite Rminus_eq_0, sqrt_0, Rminus_0_r.
          fieldrewrite (2 * ((x² + y²) / (2 * y)) - y) (x²/y); try lra.
          unfold Rsqr; field; split; lra.
        }
        rewrite P0; lra.
      + exfalso.
        assert (2 * ((x² + y²) / (2 * y)) - y = x² / y) as P.
        { unfold Rsqr; try field; lra. }
        rewrite P, <- RmultRinv in e.
        symmetry in e.
        destruct (Rmult_integral _ _ e).
        * apply Rsqr_eq_0 in H; lra.
        * apply (Rmult_eq_compat_r y) in H.
          rewrite Rinv_l in H; lra.
      + exfalso.
        assert (2 * ((x² + y²) / (2 * y)) - y = x² / y) as P.
        { unfold Rsqr; try field; lra. }
        rewrite P, <- RmultRinv in r4.
        specialize (Rle_0_sqr x) as P0.
        apply (Rmult_gt_compat_r y) in r4; try lra.
        rewrite Rmult_assoc, Rinv_l, Rmult_0_l in r4; lra.
      + exfalso.
        apply (Rmult_eq_compat_r (2 * y)) in e.
        rewrite <- RmultRinv, Rmult_assoc, Rinv_l,
        Rmult_0_l, Rmult_1_r in e; try lra.
        symmetry in e.
        apply Rplus_sqr_eq_0 in e; destruct e; lra.
      + exfalso.
        apply (Rmult_gt_compat_r (2 * y)) in r1; try lra.
        rewrite <- RmultRinv, Rmult_assoc, Rinv_l,
        Rmult_0_l, Rmult_1_r in r1; try lra.
        specialize (Rle_0_sqr x) as P; specialize (Rle_0_sqr y) as P0;
          lra.
    - repeat rewrite Rmult_0_l; reflexivity.
  }
  rewrite <- P.
  unfold θ1_alt, rz.
  apply extension_C0_continuous.
  - rewrite <- RmultRinv.
    apply Rle_mult_inv_pos; try lra.
    specialize (Rle_0_sqr x) as P0; specialize (Rle_0_sqr y) as P1.
    lra.
  - intros.
    apply continuity_pt_impl_continuous_pt, continuity_pt_mult,
    continuity_pt_mult;
        [apply continuity_pt_id
        |apply continuity_pt_const; unfold constant; auto | ].
    apply continuity_pt_minus;
      [apply continuity_pt_const; unfold constant; auto|].
    apply (continuity_pt_comp _ atan);
      [|apply derivable_continuous_pt, derivable_pt_atan].
    apply continuity_pt_div.
    + apply derivable_continuous_pt; auto_derive; auto.
    + apply continuity_pt_minus;
        [apply continuity_pt_const; unfold constant; auto|].
      apply (continuity_pt_comp _ sqrt);
        [apply derivable_continuous_pt; auto_derive; auto|].
      apply continuity_pt_sqrt; simpl in *.
      apply (Rmult_le_compat_r (2 * y)) in H0; try lra.
      rewrite <- RmultRinv, Rmult_assoc, Rinv_l, Rmult_1_r in H0;
        try lra.
      unfold Rsqr in *; lra.
    + specialize (sqrt_pos (x² - (2 * x0 - y) * y)) as P0; lra.
Qed.

Lemma cont_dist_posy : forall x y r,
    let rz := (x² + y²) / (2 * y) : R in 
    let arcl := fun (x y r : R) => r * θ1 x y r in
    let arclx := fun x y => extension_C0 (arcl x y) 0 rz in
    let arml := fun (x y r : R) => sqrt (x² - (2 * r - y) * y) in
    let armlx := fun x y => extension_C0 (arml x y) 0 rz in
    let d := fun r : R => plus (arclx x y r) (armlx x y r) in
    forall (zlty : 0 < y)
           (rbnd : 0 <= r <= rz),
      continuous d r.
Proof.
  intros.
  rename d into d3.
  
  assert (0 = sqrt (x² - (2 * rz - y) * y)) as zdef. {
    unfold rz.
    rewrite <- sqrt_0.
    apply f_equal.
    unfold Rsqr.
    field; lra. }

  assert (0 < rz) as rlerz. {
    unfold rz.
    apply (Rmult_lt_reg_r (2 * y)).
    zltab.
    arn.
    setr (x² + y²); try lra.
    apply posss.
    intros [xd yd].
    rewrite yd in zlty.
    lra. }

  unfold d3.
  apply (continuous_plus (arclx x y)).
  - unfold arclx, arcl.
    destruct (Rle_lt_dec 0 x) as [xgez | xlt0].
    * apply theta1_Q1_cont; auto.
    * apply theta1_Q2_cont; auto.
  - assert (forall r, 0 <= r <= rz -> x² - (2 * r - y) * y >= 0) as ag0. {
      rewrite <- sqrt_0 in zdef.
      apply sqrt_inj in zdef; try lra.
      intros *.
      intros [lb ub].
      apply Rle_ge.
      rewrite zdef.
      apply (Rplus_le_reg_r (- x² - y²)).
      apply (Rmult_le_reg_r (/ 2 * / y)).
      zltab.
      unfold Rsqr.
      setl (-rz); try lra.
      setr (- r0); try lra.
      right.
      unfold rz, Rsqr.
      field; lra. }
    unfold armlx.
    apply extension_C0_continuous; simpl; try lra; intros.
    unfold arml.
    apply (continuous_comp _ sqrt);
      [|apply continuity_pt_impl_continuous_pt;
        apply continuity_pt_sqrt; specialize (ag0 x0); lra].
    specialize (ex_derive_continuous
                  (fun x1 : R_UniformSpace => x² - (2 * x1 - y) * y) x0)
      as P0; apply P0; auto_derive; auto.
Qed.

Lemma path_stdR:
  forall θ₀ x₀ y₀ x₁ y₁ r θ D rtp,
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    path_segment D (Hx r θ₀ x₀ θ rtp) (Hy r θ₀ y₀ θ rtp)
                 (mkpt x₀ y₀) (mkpt x₁ y₁) ->
    path_segment D (Hx r 0 0 θ rtp) (Hy r 0 0 θ rtp)
                 (mkpt 0 0) (mkpt x y).
Proof.
  intros.
  addzner.
  split; intros;
  destruct H.
  + apply Hx_cont.
  + apply Hy_cont.
  + apply f_equal2.
    ++ unfold Hx.
       unfold extension_cont.
       destruct Rle_dec.
       +++ unfold Hxarc.
           rewrite sin0r.
           rewrite sin_0. field.
       +++ exfalso.
           apply n. left.
           assumption.
    ++ unfold Hy.
       unfold extension_cont.
       destruct Rle_dec.
       +++ unfold Hyarc.
           setl (- (r * cos (0 / r + 0)) + r * cos 0 + 0).
           rewrite cos0r.
           rewrite cos_0. field.
       +++ exfalso.
           apply n. left.
           assumption.
  + inversion bbnd as [[hx1 hy1]].
    inversion abnd as [[hx0 hy0]].
    unfold Hx,Hy in hx1,hy1,hx0,hy0.
    unfold Hx,Hy.
    unfold extension_cont in *.
    destruct Rle_dec;
      destruct Rle_dec;
      apply f_equal2.
    ++ unfold Hxarc, Hyarc in *.
       unfold x.
       rewrite sin_plus in hx1.
       rewrite sin_plus.
       rewrite cos_plus in hy1.
       clear - hx1 hy1.
       autorewrite with null.
       rewrite Rmult_minus_distr_l in hy1.
       rewrite Rmult_plus_distr_l in hx1.
       assert ((x₁ - x₀) * cos θ₀ = r * sin (D / r) * cos θ₀ * cos θ₀ +
                                    r * cos (D / r) * sin θ₀ * cos θ₀ -
                                    r * sin θ₀ * cos θ₀) as id1. {
         rewrite <- hx1.
         field.
       }
       assert ((y₁ - y₀) * sin θ₀ = - r * (cos (D / r) * cos θ₀) * sin θ₀ +
                                    r * (sin (D / r) * sin θ₀) * sin θ₀ +
                                    r * cos θ₀ * sin θ₀) as id2. {
         rewrite <- hy1.
         field.
       }
       rewrite id1, id2.
       setr (r * sin (D / r) *((sin θ₀)² + (cos θ₀)²)).
       rewrite sin2_cos2.
       field.
    ++ unfold Hxarc, Hyarc in *.
       unfold y.
       rewrite sin_plus in hx1.
       rewrite cos_plus.
       rewrite cos_plus in hy1.
       clear - hx1 hy1.
       autorewrite with null.
       rewrite Rmult_minus_distr_l in hy1.
       rewrite Rmult_plus_distr_l in hx1.
       assert (- (x₁ - x₀) * sin θ₀ = - r * sin (D / r) * cos θ₀ * sin θ₀ -
                                    r * cos (D / r) * sin θ₀ * sin θ₀ +
                                    r * sin θ₀ * sin θ₀) as id1. {
         rewrite <- hx1.
         field.
       }
       assert ((y₁ - y₀) * cos θ₀ = - r * (cos (D / r) * cos θ₀) * cos θ₀ +
                                    r * (sin (D / r) * sin θ₀) * cos θ₀ +
                                    r * cos θ₀ * cos θ₀) as id2. {
         rewrite <- hy1.
         field.
       }
       rewrite id1, id2.
       setr (- r * cos (D / r) *((sin θ₀)² + (cos θ₀)²) + r * ((sin θ₀)² + (cos θ₀)²)).
       rewrite sin2_cos2.
       field.
    ++ exfalso.
       apply n. left.
       assumption.
    ++ exfalso.
       apply n. left.
       assumption.
    ++ unfold Hxlin, Hylin in *.
       unfold Hxarc, Hyarc in hx1, hy1.
       unfold Hxarc.
       rewrite sin_plus, cos_plus in hx1, hy1.
       rewrite sin_plus, cos_plus.
       autorewrite with null.
       unfold x.
       assert ((x₁ - x₀) * cos θ₀ = (D - r * θ) * (cos θ₀ * cos θ - sin θ₀ * sin θ) * cos θ₀ +
                                    r * (sin (r * θ / r) * cos θ₀ * cos θ₀ +
                                         cos (r * θ / r) * sin θ₀ * cos θ₀)
                                    - r * sin θ₀ * cos θ₀) as id. {
         rewrite <- hx1.
         field. }
       assert ((y₁ - y₀) * sin θ₀ = (D - r * θ) * (sin θ₀ * cos θ + cos θ₀ * sin θ) * sin θ₀ +
                                    - r * (cos (r * θ / r) * cos θ₀ * sin θ₀ -
                                           sin (r * θ / r) * sin θ₀ * sin θ₀) +
                                           r * cos θ₀ * sin θ₀) as id2. {
         rewrite <- hy1.
         field. }
       rewrite id, id2.
       setr ((D - r * θ) * (cos θ * ((sin θ₀)² + (cos θ₀)²))
             + r * sin (r * θ / r) * ((sin θ₀)² + (cos θ₀)²)).
       rewrite sin2_cos2.
       field.
    ++ unfold Hxlin, Hylin in *.
       unfold Hxarc, Hyarc in hx1, hy1.
       unfold Hyarc.
       rewrite sin_plus, cos_plus in hx1, hy1.
       rewrite sin_plus, cos_plus.
       autorewrite with null.
       unfold y.
       assert (- (x₁ - x₀) * sin θ₀ = - (D - r * θ) * (cos θ₀ * cos θ - sin θ₀ * sin θ) * sin θ₀ -
                                    r * (sin (r * θ / r) * cos θ₀ * sin θ₀ +
                                         cos (r * θ / r) * sin θ₀ * sin θ₀)
                                    + r * sin θ₀ * sin θ₀) as id. {
         rewrite <- hx1.
         field. }
       assert ((y₁ - y₀) * cos θ₀ = (D - r * θ) * (sin θ₀ * cos θ + cos θ₀ * sin θ) * cos θ₀ +
                                    - r * (cos (r * θ / r) * cos θ₀ * cos θ₀ -
                                           sin (r * θ / r) * sin θ₀ * cos θ₀) +
                                           r * cos θ₀ * cos θ₀) as id2. {
         rewrite <- hy1.
         field. }
       rewrite id, id2.
       setr ((D - r * θ) * ( sin θ * ((sin θ₀)² + (cos θ₀)²))
             - r * cos (r * θ / r) * ((sin θ₀)² + (cos θ₀)²)
             + r * ((sin θ₀)² + (cos θ₀)²)).
       rewrite sin2_cos2.
       field.
    ++ exfalso.
       apply n0. left.
       assumption.
    ++ exfalso.
       apply n0. left.
       assumption.
  + intros.
    apply H_len; [ assumption|left; assumption ].
Qed.

Lemma path_stdL:
  forall θ₀ x₀ y₀ x₁ y₁ r θ D rtp,
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    path_segment D (Hx r 0 0 θ rtp) (Hy r 0 0 θ rtp)
                 (mkpt 0 0) (mkpt x y) ->
    path_segment D (Hx r θ₀ x₀ θ rtp) (Hy r θ₀ y₀ θ rtp)
                 (mkpt x₀ y₀) (mkpt x₁ y₁).
Proof.
  intros.
  addzner.
  split; intros;
    destruct H.
  + apply Hx_cont.
  + apply Hy_cont.
  + apply f_equal2.
    ++ unfold Hx.
       unfold extension_cont.
       destruct Rle_dec.
       +++ unfold Hxarc.
           fieldrewrite (0 / r + θ₀) θ₀; try lra.
       +++ exfalso.
           apply n. left.
           assumption.
    ++ unfold Hy.
       unfold extension_cont.
       destruct Rle_dec.
       +++ unfold Hyarc.
           fieldrewrite (0 / r + θ₀) θ₀; try lra.
       +++ exfalso.
           apply n. left.
           assumption.
  + inversion bbnd as [[hx1 hy1]].
    inversion abnd as [[hx0 hy0]].
    rewrite hx0 in hy0.
    unfold Hx,Hy in hx1,hy1,hx0,hy0.
    unfold Hx,Hy.
    unfold extension_cont in *.
    destruct Rle_dec;
      destruct Rle_dec;
      apply f_equal2.
    ++ unfold Hxarc, Hyarc in *.
       unfold x in hx1.
       unfold y in hy1.
       rewrite sin_plus in hx1.
       rewrite sin_plus.
       rewrite cos_plus in hy1.
       clear - hx1 hy1.
       autorewrite with null in *.
       rewrite Rmult_plus_distr_l.
       repeat rewrite <- Rmult_assoc.
       assert (r * cos (D / r) = r + (x₁ - x₀) * sin θ₀ - (y₁ - y₀) * cos θ₀) as hy1p. {
         apply (Rplus_eq_reg_r (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ - r * cos (D/r))).
         lrag hy1. }
       rewrite hx1, hy1p.
       setl (x₁ * ((sin θ₀)² + (cos θ₀)²) - x₀ * ((sin θ₀)² + (cos θ₀)²) + x₀).
       rewrite sin2_cos2.
       field.
    ++ unfold Hxarc, Hyarc in *.
       unfold x in hx1.
       unfold y in hy1.
       rewrite sin_plus in hx1.
       rewrite cos_plus.
       rewrite cos_plus in hy1.
       clear - hx1 hy1.
       autorewrite with null in *.
       rewrite Rmult_minus_distr_l.
       repeat rewrite <- Rmult_assoc.
       assert (r * cos (D / r) = r + (x₁ - x₀) * sin θ₀ - (y₁ - y₀) * cos θ₀) as hy1p. {
         apply (Rplus_eq_reg_r (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ - r * cos (D/r))).
         lrag hy1. }
       fieldrewrite (- r * cos (D / r) * cos θ₀) (- (r * cos (D / r)) * cos θ₀).
       fieldrewrite (- r * sin (D / r) * sin θ₀) (- (r * sin (D / r)) * sin θ₀).
       rewrite hx1, hy1p.
       setl (y₁ * ((sin θ₀)² + (cos θ₀)²) - y₀ * ((sin θ₀)² + (cos θ₀)²) + y₀).
       rewrite sin2_cos2.
       field.
    ++ exfalso.
       apply n. left.
       assumption.
    ++ exfalso.
       apply n. left.
       assumption.
    ++ unfold Hxlin, Hylin in *.
       unfold Hxarc, Hyarc in hx1, hy1.
       unfold Hxarc.
       rewrite sin_plus, cos_plus in hx1, hy1.
       rewrite sin_plus, cos_plus.
       autorewrite with null in *.
       unfold x in hx1.
       unfold y in hy1.
       assert ((D - r * θ) * cos θ = - r * sin (r * θ / r) +
                                     (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) as hx1p. {
         apply (Rplus_eq_reg_r (r * sin (r * θ / r))).
         lrag hx1. }
       assert ((D - r * θ) * sin θ =
               r * cos (r * θ / r) - r + - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) as hy1p. {
         apply (Rplus_eq_reg_r (- r * cos (r * θ / r) + r)).
         lrag hy1. }
       assert (r * θ / r = θ) as rtrid.
       rewrite <- RmultRinv;
         field; auto.
       rewrite rtrid in *; clear rtrid.
       setl (cos θ₀ * ((D - r * θ) * cos θ) - sin θ₀ * ((D - r * θ) * sin θ) +
             (r * (sin θ * cos θ₀ + cos θ * sin θ₀) - r * sin θ₀ + x₀)).
       rewrite hx1p, hy1p.
       setl ((x₁ - x₀) * ((sin θ₀)² + (cos θ₀)²) + x₀).
       rewrite sin2_cos2.
       field.
    ++ unfold Hxlin, Hylin in *.
       unfold Hxarc, Hyarc in hx1, hy1.
       unfold Hyarc.
       rewrite sin_plus, cos_plus in hx1, hy1.
       rewrite sin_plus, cos_plus.
       autorewrite with null in *.
       unfold x in hx1.
       unfold y in hy1.
       assert ((D - r * θ) * cos θ = - r * sin (r * θ / r) +
                                     (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) as hx1p. {
         apply (Rplus_eq_reg_r (r * sin (r * θ / r))).
         lrag hx1. }
       assert ((D - r * θ) * sin θ =
               r * cos (r * θ / r) - r + - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) as hy1p. {
         apply (Rplus_eq_reg_r (- r * cos (r * θ / r) + r)).
         lrag hy1. }
       assert (r * θ / r = θ) as rtrid.
       rewrite <- RmultRinv;
         field; auto.
       rewrite rtrid in *; clear rtrid.
       setl (sin θ₀ * ((D - r * θ) * cos θ) + cos θ₀ * ((D - r * θ) * sin θ) +
             (- r * (cos θ * cos θ₀ - sin θ * sin θ₀) + r * cos θ₀ + y₀)).
       rewrite hx1p, hy1p.
       setl ((y₁ - y₀) * ((sin θ₀)² + (cos θ₀)²) + y₀).
       rewrite sin2_cos2.
       field.
    ++ exfalso.
       apply n0. left.
       assumption.
    ++ exfalso.
       apply n0. left.
       assumption.
  + intros.
    apply H_len; [ assumption|left; assumption ].
Qed.

Lemma path_std:
  forall θ₀ x₀ y₀ x₁ y₁ r θ D rtp,
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    path_segment D (Hx r θ₀ x₀ θ rtp) (Hy r θ₀ y₀ θ rtp)
                 (mkpt x₀ y₀) (mkpt x₁ y₁) <->
    path_segment D (Hx r 0 0 θ rtp) (Hy r 0 0 θ rtp)
                 (mkpt 0 0) (mkpt x y).
Proof.
  intros.
  split.
  intros.
  apply path_stdR; assumption.
  apply path_stdL; assumption.
Qed.
(* end hide *)
  
(* not colinear *)
Lemma npx_straight :
  forall θ₀ x₀ y₀ x₁ y₁ r θr stp Dr
         (phase : straight r θ₀ x₀ y₀ x₁ y₁)
         (P : path_segment Dr (Hx r θ₀ x₀ θr stp) (Hy r θ₀ y₀ θr stp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    θmax <> 0.
Proof.
  intros.
  apply straight_rot in phase.
  apply path_std in P.
  unfold θmax.
  rewrite calc_angle_std in *.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  apply thmaxne0.
  eapply npx_straight_s; try eassumption.
Qed.

(* begin hide *)

Lemma straight_npx_s :
  forall x y r θ stp D
         (phase : straight r 0 0 0 x y)
         (px : 0 < x /\ y = 0),
    ~ path_segment D (Hx r 0 0 θ stp) (Hy r 0 0 θ stp)
      (mkpt 0 0) (mkpt x y).
Proof.
  intros.
  destruct px as [xgt0 yeq0].
  intro P.
  eapply npx_straight_s.
  apply phase.
  apply P.
  lra.
Qed.

(* end hide *)

Lemma straight_npx :
  forall θ₀ x₀ y₀ x₁ y₁ r θr stp D
         (phase : straight r θ₀ x₀ y₀ x₁ y₁),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmeq0 : θmax = 0),
      ~ path_segment D (Hx r θ₀ x₀ θr stp) (Hy r θ₀ y₀ θr stp)
                        (mkpt x₀ y₀) (mkpt x₁ y₁).
Proof.
  intros.
  intro P.
  eapply npx_straight; try eassumption.
Qed.


(* We prove the correctness of a more general form for r here,
accounting for rotation and translation of our craft in the plane. The
final point 'p' in the paper here can be expressed as

p = ( (x₁ - x₀)*cos θ₀ + (y₁ - y₀)* sin θ₀,
      -(x₁ - x₀)*sin θ₀ + (y₁ - y₀)* cos θ₀)  *)

(* begin hide *)
Theorem turnpath_arc_parameters :
  forall (x₀ y₀ x₁ y₁ θ₀  : R),
    let θ₁ := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    let r := sqrt ((y₁ - y₀)²+(x₁ - x₀)²)/(2*sin (θ₁/2)) in
    forall
      (sinnneg : sin (θ₁/2) <> 0) (* exclude points on x-axis *)
      (zner : 0 <> r),             (* exclude zero-length path (origin) *)
      let D := mknonnegreal (r*θ₁) (turn_params_consist x₀ y₀ x₁ y₁ θ₀ sinnneg zner) in
      turning r θ₀ x₀ y₀ x₁ y₁ /\
      path_segment D (Hxarc r θ₀ x₀) (Hyarc r θ₀ y₀) (mkpt x₀ y₀) (mkpt x₁ y₁).
Proof.
  intros.
  
  generalize (turn_params_consist x₀ y₀ x₁ y₁ θ₀ sinnneg zner) as zlert1;
    intro; change (0 <= r * θ₁) in zlert1.

  generalize (turnpath_parameters_range x₀ y₀ x₁ y₁ θ₀ sinnneg zner) as t1le2PI;
    intro; change (r * θ₁ < 2 * Rabs r * PI ) in t1le2PI.

  set (pathx := (Hxarc r θ₀ x₀)).
  set (pathy := (Hyarc r θ₀ y₀)).

  assert (forall d : R,
             0 <= d ->
             is_RInt (magnitude (Derive pathx) (Derive pathy)) 0 d d)
    as dparam. intros.

  generalize (H_arclen r θ₀ x₀ y₀ 0 d zner) as dparam; intro.
  assert (d - 0 = d) as ddef. field. rewrite ddef in dparam.
  assumption.

  assert (forall d, continuous pathx d) as xcont; intros.
  apply Hxarc_cont; try assumption.
  assert (forall d, continuous pathy d) as ycont; intros.
  apply Hyarc_cont; try assumption.
  assert (mkpt (pathx 0) (pathy 0) = mkpt x₀ y₀) as apt.
  unfold pathx, pathy, Hx, Hy, extension_cont, Hxarc, Hyarc.

  fieldrewrite (0 / r + θ₀) (θ₀). auto. 
  fieldrewrite (r * sin θ₀ - r * sin θ₀ + x₀) (x₀).
  fieldrewrite (- r * cos θ₀ + r * cos θ₀ + y₀) (y₀).
  reflexivity.

  generalize (turnpath_parameters_on_arc x₀ y₀ x₁ y₁ θ₀ sinnneg zner) as bdef;
    intro; inversion_clear bdef as [x1def y1def];
      change (x₁ = Hxarc r θ₀ x₀ (r*θ₁)) in x1def;
      change (y₁ = Hyarc r θ₀ y₀ (r*θ₁)) in y1def.

  assert (mkpt (pathx D) (pathy D) = mkpt x₁ y₁) as bpt.
  unfold D, pathx, pathy. simpl.
  rewrite x1def, y1def. reflexivity.

  split.
  apply turnpath_parameters_turning; try assumption.
  apply (path_intro D pathx pathy (mkpt x₀ y₀) (mkpt x₁ y₁)); assumption.
Qed.
(* end hide *)

Theorem turnpath_parameters :
  forall (x₀ y₀ x₁ y₁ θ₀ θc : R),
    let θ₁ := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    let r := sqrt ((y₁ - y₀)²+(x₁ - x₀)²)/(2*sin (θ₁/2)) in
    forall
      (inturn : r * θ₁ <= r * θc)  (* any path that turns at least that much *)
      (sinnneg : sin (θ₁/2) <> 0)  (* exclude points on x-axis *)
      zner rtp,             (* exclude zero-length path (origin) *)
      let D := mknonnegreal (r*θ₁) (turn_params_consist x₀ y₀ x₁ y₁ θ₀ sinnneg zner) in
      turning r θ₀ x₀ y₀ x₁ y₁ /\
      path_segment D (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp) (mkpt x₀ y₀) (mkpt x₁ y₁).
Proof.
  intros.
  
  generalize (turn_params_consist x₀ y₀ x₁ y₁ θ₀ sinnneg zner) as zlert1;
    intro; change (0 <= r * θ₁) in zlert1.

  generalize (turnpath_parameters_range x₀ y₀ x₁ y₁ θ₀ sinnneg zner) as t1le2PI;
    intro; change (r * θ₁ < 2 * Rabs r * PI ) in t1le2PI.

  set (pathx := (Hx r θ₀ x₀ θc rtp)).
  set (pathy := (Hy r θ₀ y₀ θc rtp)).

  assert (forall d : R,
             0 <= d ->
             is_RInt (magnitude (Derive pathx) (Derive pathy)) 0 d d)
    as dparam. intros.

  assert (0 <= r * θc) as zlertc. apply (Rle_trans _ (r * θ₁)); assumption.
  generalize (H_len r θ₀ θc x₀ y₀ d H zlertc) as dparam; try assumption; intro.
  apply dparam.

  assert (forall d, continuous pathx d) as xcont; intros.
   apply Hx_cont; try assumption.
  assert (forall d, continuous pathy d) as ycont; intros.
  apply Hy_cont; try assumption.
  assert (mkpt (pathx 0) (pathy 0) = mkpt x₀ y₀) as apt.
  unfold pathx, pathy, Hx, Hy, extension_cont, Hxarc, Hyarc.
  destruct (Rle_dec 0 (r * θc));
    [ | exfalso; apply n; apply (Rle_trans _ (r*θ₁)); assumption].
  fieldrewrite (0 / r + θ₀) (θ₀). auto. 
  fieldrewrite (r * sin θ₀ - r * sin θ₀ + x₀) (x₀).
  fieldrewrite (- r * cos θ₀ + r * cos θ₀ + y₀) (y₀).
  reflexivity.

  generalize (turnpath_parameters_on_arc x₀ y₀ x₁ y₁ θ₀ sinnneg zner) as bdef;
    intro; inversion_clear bdef as [x1def y1def];
      change (x₁ = Hxarc r θ₀ x₀ (r*θ₁)) in x1def;
      change (y₁ = Hyarc r θ₀ y₀ (r*θ₁)) in y1def.

  assert (mkpt (pathx D) (pathy D) = mkpt x₁ y₁) as bpt.
  unfold D, pathx, pathy. simpl.
  rewrite x1def, y1def.
  unfold Hx, Hy, extension_cont.
  destruct (Rle_dec (r * θ₁) (r * θc)).
  reflexivity.

  exfalso. apply n. assumption.

  split.
  apply turnpath_parameters_turning; try assumption.
  apply (path_intro D pathx pathy (mkpt x₀ y₀) (mkpt x₁ y₁)); assumption.
Qed.

(* begin hide *)
Theorem intro_theta_path_std : forall (x y θc : R),
    let θmax := calcθ₁ 0 0 0 x y in
    forall (tcrng : θmax / 2 < θc < θmax \/
                    -2 * PI < θc < θmax / 2 - 2 * PI \/
                    θmax < θc < θmax / 2 \/
                    θmax / 2 + 2 * PI < θc < 2 * PI),
      let r := (x * sin θc - y * cos θc)
                 / (1 - cos θc) in
      let D := r*θc + calcL r 0 0 0 x y θc in
      forall (phase : straight r 0 0 0 x y)
             (nnX : ~( r < 0 /\ θmax = 2*PI)),
      exists rtp Dnnpf,
        path_segment (mknonnegreal D Dnnpf) (Hx r 0 0 θc rtp)
                     (Hy r 0 0 θc rtp) (mkpt 0 0) (mkpt x y).
Proof.
  intros.
  rename tcrng into tcrng2.
  specialize (tcrng_form2 _ _ _ _ _ _  tcrng2) as [tcps [tcn tmaxne0]].
  change (θmax <> 0) in tmaxne0.
  assert ((0 < θmax -> θmax / 2 < θc < θmax \/
                       -2 * PI < θc < θmax / 2 - 2 * PI) /\
          (θmax < 0 -> θmax < θc < θmax / 2 \/
                       θmax / 2 + 2 * PI < θc < 2 * PI)) as tcrng;
    [split; [apply tcps| apply tcn]|].
  clear tcrng2 tcn tcps.

  specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as notid.
  generalize (ottb_r_thetac_lb _ _ _ _ _ _ notid tmaxne0 tcrng)
    as rclb; intro.
  simpl in rclb.
  autorewrite with null in rclb.
  change (0 < r * θc) in rclb.
  assert (r <> 0) as rne0. intro req0. rewrite req0 in rclb. lra.

  specialize (ottb_r_thetac_ub
                0 0 0 x y θc notid tmaxne0 tcrng) as rcub.
  autorewrite with null in rcub.
  simpl in rcub.
  change (r * θc < 2 * Rabs r * PI) in rcub.
  rewrite (Rmult_comm 2) in rcub.
  assert (0 < r * θc < Rabs r * 2 * PI) as rcompat. {
    split; assumption. }
  
  exists rcompat.

  generalize phase; intro ns.
  apply straight_not_stationary2 in ns.
  specialize (rotated_straight_path_equiv _ _ _ _ _ ns tmaxne0) as nst.
  
  assert (cos θc <> 1) as den. {
    assert (~ ((x - 0) * cos 0 + (y - 0) * sin 0 = 0 /\
               - (x - 0) * sin 0 + (y - 0) * cos 0 = 0)) as notO2. {
      clear - nst.
      intros [xd yd]. apply nst. clear nst.
      split; [right; symmetry|]; assumption.
      }
    clear - tcrng tmaxne0 notO2.
    destruct tcrng as [tmgt0 tmlt0].
    unfold θmax. unfold calcθ₁ in *.
    specialize (atan2_bound _ _ notO2) as [at2l at2u].
    apply (Rmult_lt_compat_l 2) in at2l; [|lra].
    change (2 * - PI < θmax) in at2l.
    apply (Rmult_le_compat_l 2) in at2u; [|lra].
    change (θmax <= 2 * PI) in at2u.
    destruct (total_order_T 0 θmax) as [[zlttm |zeqtm] |zgttm].
    - specialize (tmgt0 zlttm) as [[plb pub] | [nlb nub]]; clear tmlt0.
      -- intro costceq1.
         apply cos_eq_1_2PI_0 in costceq1; try lra.
      -- intro costceq1.
         rewrite <- cos_neg in costceq1.
         apply cos_eq_1_2PI_0 in costceq1; try lra.
    - exfalso. apply tmaxne0. auto.
    - apply Rgt_lt in zgttm.
      specialize (tmlt0 zgttm) as [[plb pub] | [nlb nub]]; clear tmgt0.
      -- intro costceq1.
         rewrite <- cos_neg in costceq1.
         apply cos_eq_1_2PI_0 in costceq1; try lra.
      -- intro costceq1.
         apply cos_eq_1_2PI_0 in costceq1; try lra.
    }

  assert ((~ (r < 0 /\
              (x - 0) * cos 0 + (y - 0) * sin 0 < 0 /\
              - (x - 0) * sin 0 + (y - 0) * cos 0 = 0))) as nnX2. {
    clear - nnX.
    intros [rlt0 altnnX].
    apply nnX.
    split ; [assumption| apply nxaxiscond; assumption].
  }

  assert (x * sin θc - y * cos θc =
          (x - 0) * sin (0 + θc) - (y - 0) * cos (0 + θc)) as id. {
    arn.
    reflexivity. }

  unfold r in phase, rne0, nnX2.
  rewrite id in phase, rne0, nnX2.
  specialize (straight_path_exists 0 0 0 x y θc
                                   notid tmaxne0 tcrng phase rne0 nnX2) as Ldir.
  
  specialize (ottb_parameters_compat_L _ _ _ _ _ _
                                       tmaxne0 tcrng Ldir phase) as zltL.
  autorewrite with null in zltL.
  change (0 < calcL r 0 0 0 x y θc) in zltL.
  set (L := calcL r 0 0 0 x y θc) in *.
  set (pathx := Hx r 0 0 θc rcompat).
  set (pathy := Hy r 0 0 θc rcompat).

  specialize (ottb_r_thetac_ub
                _ _ _ _ _ _ notid tmaxne0 tcrng) as zlerthcle2rPIub.
  assert (0 <= r * θc < 2 * Rabs r * PI) as zlerthcle2rPI. {
    split. left. assumption.
    simpl in zlerthcle2rPIub.
    autorewrite with null in zlerthcle2rPIub.
    assumption. }

  unfold calcL, Hxarc, Hyarc in *.
  inversion_clear zlerthcle2rPI as [zlertc rtclt2rPI].
  assert (forall d : R,
             0 <= d ->
             is_RInt (magnitude (Derive pathx) (Derive pathy)) 0 d d)
    as dparam. intros.

  apply (H_len r 0 θc 0 0); try assumption. auto.
  assert (forall d, continuous pathx d) as xcont; intros.
  apply Hx_cont; try assumption. 
  assert (forall d, continuous pathy d) as ycont; intros.
  apply Hy_cont; try assumption. 
  assert (mkpt (pathx 0) (pathy 0) = mkpt 0 0) as bpt.
  unfold pathx, pathy, Hx, Hy, extension_cont, Hxarc, Hyarc.
  destruct (Rle_dec 0 (r * θc)); [ | exfalso; apply n; assumption].
  fieldrewrite (0 / r + 0) (0).
  clear - rclb.
  apply rtp_zner in rclb.
  lra.
  fieldrewrite (r * sin 0 - r * sin 0 + 0) (0).
  fieldrewrite (- r * cos 0 + r * cos 0 + 0) (0).
  reflexivity.

  
  assert (pathx D = x) as endx. {
    (*rewrite dist. *)
    unfold D.
    unfold pathx, Hx, Hxlin, extension_cont.
    unfold Hxarc at 2.
    destruct (Rle_dec (r * θc + L) (r * θc)).
    exfalso.
    assert (L <= 0) as Lle0. {
      apply (Rplus_le_reg_l (r * θc)). setr (r * θc). assumption. }
    lra.
    
    destruct (Req_EM_T 0 (cos (0 + θc))) as [zeqcost | znecost] ; [
      symmetry in zeqcost; generalize (coseq0_sinneq0 _ zeqcost) as
          sintne0; intro |
      generalize (not_eq_sym znecost) as costne0; intro]. 
    
    - setl (L * cos (0 + θc) + r * sin (r * θc / r + 0) - r * sin 0 + 0).
      unfold L, Hyarc. 
      fieldrewrite (r * θc / r + 0) (0 + θc). intro. rewrite H in *. lra.
      apply (Rmult_eq_reg_l (sin (0+θc))); [| assumption].
      apply (Rplus_eq_reg_l (- sin (0+θc) * x)). setr 0.
      setl ( (y - 0) * cos (0 + θc)
             - (x - 0) * sin (0 + θc)
             + r * (cos (0 + θc) * cos (0 + θc) + 
                    sin (0 + θc) * sin (0 + θc))
               - r * (cos 0 * cos (0 + θc) + 
              sin 0 * sin (0 + θc))
           ); [ assumption|].
      repeat rewrite <- cos_minus.
      fieldrewrite (0 + θc - (0 + θc)) 0. rewrite cos_0.
      fieldrewrite (0 - (0 + θc)) (- θc). rewrite cos_neg.
      apply (Rplus_eq_reg_r ( r * (cos θc - 1))).
      setl ((y - 0) * cos (0 + θc) - (x - 0) * sin (0 + θc)).
      setr ( - r * (1 - cos θc)). unfold r.
      setr ((y - 0) * cos (θc) - (x - 0) * sin (θc)).
      intro. apply den. apply (Rplus_eq_reg_l (- cos θc)).
      setl 0. setr (1 - cos θc). symmetry. assumption.
      arn.
      reflexivity.
    - setl (L * cos (0 + θc) + r * sin (r * θc / r + 0) - r * sin 0 + 0).
      unfold L, Hxarc. 
      fieldrewrite (r * θc / r + 0) (0 + θc). intro. rewrite H in *. lra.
      apply (Rmult_eq_reg_l (cos (0+θc))); [| assumption].
      setl (cos (0 + θc) * x); [ assumption |]. reflexivity.
  }
  
  assert (pathy D = y) as endy. {
    unfold D.
    unfold pathy, Hy, Hylin, extension_cont.
    unfold Hyarc at 2.
    destruct (Rle_dec (r * θc + L) (r * θc)).
    - exfalso.
      assert (L <= 0) as Lle0.
      apply (Rplus_le_reg_l (r * θc)). setr (r * θc). assumption.
      lra.
    -  destruct (Req_EM_T 0 (cos (0 + θc))) as [zeqcost | znecost]; [
         symmetry in zeqcost; generalize (coseq0_sinneq0 _ zeqcost) as
             sintne0; intro |
         generalize (not_eq_sym znecost) as costne0; intro].
       -- setl (L * sin (0 + θc) - r * cos (r * θc / r + 0) +
                r * cos 0 + 0).
          unfold L, Hyarc. 
          fieldrewrite (r * θc / r + 0) (0 + θc). intro. rewrite H in *. lra.
          apply (Rmult_eq_reg_l (sin (0+θc))); [| assumption].
          setl (sin (0 + θc) * y); [ assumption |]. reflexivity.
       -- setl (L * sin (0 + θc) - r * cos (r * θc / r + 0) +
                r * cos 0 + 0).
          unfold L, Hyarc. 
          fieldrewrite (r * θc / r + 0) (0 + θc). intro. rewrite H in *. lra.
          apply (Rmult_eq_reg_l (cos (0+θc))); [| assumption].
          apply (Rplus_eq_reg_l (- cos (0+θc) * y)). setr 0.
          setl ( (x - 0) * sin (0 + θc)
                 - (y - 0) * cos (0 + θc)
                 + r * (cos 0 * cos (0 + θc) +
                        sin 0 * sin (0 + θc))
                   - r * (cos (0 + θc) * cos (0 + θc) +
                          sin (0 + θc) * sin (0 + θc))
               ) ;[ assumption |].
          
          repeat rewrite <- cos_minus.
          fieldrewrite (0 + θc - (0 + θc)) 0. rewrite cos_0.
          fieldrewrite (0 - (0 + θc)) (- θc). rewrite cos_neg.
          apply (Rplus_eq_reg_r ( - r * (cos θc - 1))).
          apply (Rmult_eq_reg_l (-1)).
          setl (((y - 0) * cos (0 + θc) - (x - 0) * sin (0 + θc))).
          setr (r * (cos θc - 1)). unfold r.
          setr ((y - 0) * cos (θc) - (x - 0) * sin (θc)).
          intro. apply den. apply (Rplus_eq_reg_l (- cos θc)).
          setl 0. setr (1 - cos θc). symmetry. assumption.
          arn.
          reflexivity.
          discrR.
  }

  assert ({| ptx := pathx D; pty := pathy D |} = {| ptx := x; pty := y |}).
  rewrite endx, endy. reflexivity.

  assert (0 < D) as Dpos. {
    unfold D.
    apply Rplus_lt_0_compat;
      try assumption. }

  exists (Rlt_le _ _ Dpos).
  apply path_intro; assumption.
Qed.
(* end hide *)

Theorem intro_theta_path : forall (x₀ y₀ x₁ y₁ θ₀ θc : R),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tcrng : θmax / 2 < θc < θmax \/
                    -2 * PI < θc < θmax / 2 - 2 * PI \/
                    θmax < θc < θmax / 2 \/
                    θmax / 2 + 2 * PI < θc < 2 * PI),
      let r := ((x₁ - x₀) * sin (θ₀ + θc) - (y₁ - y₀) * cos (θ₀ + θc)) /
                                (1 - cos θc) in
      let D := r*θc + calcL r θ₀ x₀ y₀ x₁ y₁ θc in
      forall (phase : straight r θ₀ x₀ y₀ x₁ y₁)
             (nnX : ~( r < 0 /\ θmax = 2*PI)),
      exists rtp Dnnpf,
        path_segment (mknonnegreal D Dnnpf) (Hx r θ₀ x₀ θc rtp)
                     (Hy r θ₀ y₀ θc rtp) (mkpt x₀ y₀) (mkpt x₁ y₁).
Proof.
  intros.
  set (Ldx := x₁ - Hxarc r θ₀ x₀ (r * θc)) in *.
  set (Ldy := y₁ - Hyarc r θ₀ y₀ (r * θc)) in *.

  rename tcrng into tcrng2.
  specialize (tcrng_form2 _ _ _ _ _ _  tcrng2) as [tcps [tcn tmaxne0]].
  change (θmax <> 0) in tmaxne0.
  assert ((0 < θmax -> θmax / 2 < θc < θmax \/
                       -2 * PI < θc < θmax / 2 - 2 * PI) /\
          (θmax < 0 -> θmax < θc < θmax / 2 \/
                       θmax / 2 + 2 * PI < θc < 2 * PI)) as tcrng;
    [split; [apply tcps| apply tcn]|].
  clear tcrng2 tcn tcps.

  specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as notid.
  generalize (ottb_r_thetac_lb _ _ _ _ _ _ notid tmaxne0 tcrng)
    as rclb; intro; unfold r in rclb; change (0 < r * θc) in rclb.
  assert (r <> 0) as rne0. intro req0. rewrite req0 in rclb. lra.

  specialize (ottb_r_thetac_ub
                θ₀ x₀ y₀ x₁ y₁ θc notid tmaxne0 tcrng) as rcub.
  simpl in rcub.
  change (r * θc < 2 * Rabs r * PI) in rcub.
  rewrite (Rmult_comm 2) in rcub.
  assert (0 < r * θc < Rabs r * 2 * PI) as rcompat. {
    split; assumption. }
  
  exists rcompat.

  generalize phase; intro ns.
  apply straight_not_stationary2 in ns.
  specialize (rotated_straight_path_equiv _ _ _ _ _ ns tmaxne0) as nst.
  
  assert (cos θc <> 1) as den. {
    assert (~ ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ = 0 /\
               - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ = 0)) as notO2. {
      clear - nst.
      intros [xd yd]. apply nst. clear nst.
      split; [right; symmetry|]; assumption.
      }
    clear - tcrng tmaxne0 notO2.
    destruct tcrng as [tmgt0 tmlt0].
    unfold θmax. unfold calcθ₁ in *.
    specialize (atan2_bound _ _ notO2) as [at2l at2u].
    apply (Rmult_lt_compat_l 2) in at2l; [|lra].
    change (2 * - PI < θmax) in at2l.
    apply (Rmult_le_compat_l 2) in at2u; [|lra].
    change (θmax <= 2 * PI) in at2u.
    destruct (total_order_T 0 θmax) as [[zlttm |zeqtm] |zgttm].
    - specialize (tmgt0 zlttm) as [[plb pub] | [nlb nub]]; clear tmlt0.
      -- intro costceq1.
         apply cos_eq_1_2PI_0 in costceq1; try lra.
      -- intro costceq1.
         rewrite <- cos_neg in costceq1.
         apply cos_eq_1_2PI_0 in costceq1; try lra.
    - exfalso. apply tmaxne0. auto.
    - apply Rgt_lt in zgttm.
      specialize (tmlt0 zgttm) as [[plb pub] | [nlb nub]]; clear tmgt0.
      -- intro costceq1.
         rewrite <- cos_neg in costceq1.
         apply cos_eq_1_2PI_0 in costceq1; try lra.
      -- intro costceq1.
         apply cos_eq_1_2PI_0 in costceq1; try lra.
    }

  assert ((~ (r < 0 /\
              (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ < 0 /\
              - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ = 0))) as nnX2. {
    clear - nnX.
    intros [rlt0 altnnX].
    apply nnX.
    split ; [assumption| apply nxaxiscond; assumption].
  }

  
  specialize (straight_path_exists x₀ y₀ θ₀ x₁ y₁ θc
                                   notid tmaxne0 tcrng phase rne0 nnX2) as Ldir.
  change (exists k : Z, atan2 Ldy Ldx = θ₀ + θc + 2 * IZR k * PI) in Ldir.
  specialize (ottb_parameters_compat_L _ _ _ _ _ _
                                       tmaxne0 tcrng Ldir phase) as zltL.
  change (0 < calcL r θ₀ x₀ y₀ x₁ y₁ θc) in zltL.
  set (L := calcL r θ₀ x₀ y₀ x₁ y₁ θc) in *.
  set (pathx := Hx r θ₀ x₀ θc rcompat).
  set (pathy := Hy r θ₀ y₀ θc rcompat).

  specialize (ottb_r_thetac_ub
                _ _ _ _ _ _ notid tmaxne0 tcrng) as zlerthcle2rPIub.
  assert (0 <= r * θc < 2 * Rabs r * PI) as zlerthcle2rPI.
  split. left. assumption. assumption.

  unfold calcL, Hxarc, Hyarc in *.
  inversion_clear zlerthcle2rPI as [zlertc rtclt2rPI].
  assert (forall d : R,
             0 <= d ->
             is_RInt (magnitude (Derive pathx) (Derive pathy)) 0 d d)
    as dparam. intros.

  apply (H_len r θ₀ θc x₀ y₀); try assumption. auto.
  assert (forall d, continuous pathx d) as xcont; intros.
  apply Hx_cont; try assumption. 
  assert (forall d, continuous pathy d) as ycont; intros.
  apply Hy_cont; try assumption. 
  assert (mkpt (pathx 0) (pathy 0) = mkpt x₀ y₀) as bpt.
  unfold pathx, pathy, Hx, Hy, extension_cont, Hxarc, Hyarc.
  destruct (Rle_dec 0 (r * θc)); [ | exfalso; apply n; assumption].
  fieldrewrite (0 / r + θ₀) (θ₀). assumption.
  fieldrewrite (r * sin θ₀ - r * sin θ₀ + x₀) (x₀).
  fieldrewrite (- r * cos θ₀ + r * cos θ₀ + y₀) (y₀).
  reflexivity.

  
  assert (pathx D = x₁) as endx. {
    (*rewrite dist. *)
    unfold D.
    unfold pathx, Hx, Hxlin, extension_cont.
    unfold Hxarc at 2.
    destruct (Rle_dec (r * θc + L) (r * θc)).
    exfalso.
    assert (L <= 0) as Lle0. {
      apply (Rplus_le_reg_l (r * θc)). setr (r * θc). assumption. }
    lra.
    
    destruct (Req_EM_T 0 (cos (θ₀ + θc))) as [zeqcost | znecost] ; [
      symmetry in zeqcost; generalize (coseq0_sinneq0 _ zeqcost) as
          sintne0; intro |
      generalize (not_eq_sym znecost) as costne0; intro]. 
    
    - setl (L * cos (θ₀ + θc) + r * sin (r * θc / r + θ₀) - r * sin θ₀ + x₀).
      unfold L, Hyarc. 
      fieldrewrite (r * θc / r + θ₀) (θ₀ + θc). intro. rewrite H in *. lra.
      apply (Rmult_eq_reg_l (sin (θ₀+θc))); [| assumption].
      apply (Rplus_eq_reg_l (- sin (θ₀+θc) * x₁)). setr 0.
      setl ( (y₁ - y₀) * cos (θ₀ + θc)
             - (x₁ - x₀) * sin (θ₀ + θc)
             + r * (cos (θ₀ + θc) * cos (θ₀ + θc) + 
                    sin (θ₀ + θc) * sin (θ₀ + θc))
               - r * (cos θ₀ * cos (θ₀ + θc) + 
              sin θ₀ * sin (θ₀ + θc))
           ); [ assumption|].
      repeat rewrite <- cos_minus.
      fieldrewrite (θ₀ + θc - (θ₀ + θc)) 0. rewrite cos_0.
      fieldrewrite (θ₀ - (θ₀ + θc)) (- θc). rewrite cos_neg.
      apply (Rplus_eq_reg_r ( r * (cos θc - 1))).
      setl ((y₁ - y₀) * cos (θ₀ + θc) - (x₁ - x₀) * sin (θ₀ + θc)).
      setr ( r * (cos θc - 1)). unfold r.
      setr ((y₁ - y₀) * cos (θ₀ + θc) - (x₁ - x₀) * sin (θ₀ + θc)).
      intro. apply den. apply (Rplus_eq_reg_l (- cos θc)).
      setl 0. setr (1 - cos θc). symmetry. assumption.
      reflexivity.
    -   setl (L * cos (θ₀ + θc) + r * sin (r * θc / r + θ₀) - r * sin θ₀ + x₀).
        unfold L, Hxarc. 
        fieldrewrite (r * θc / r + θ₀) (θ₀ + θc). intro. rewrite H in *. lra.
        apply (Rmult_eq_reg_l (cos (θ₀+θc))); [| assumption].
        setl (cos (θ₀ + θc) * x₁); [ assumption |]. reflexivity.
  }
  
  assert (pathy D = y₁) as endy. {

    unfold D.
    unfold pathy, Hy, Hylin, extension_cont.
    unfold Hyarc at 2.
    destruct (Rle_dec (r * θc + L) (r * θc)).
    - exfalso.
      assert (L <= 0) as Lle0.
      apply (Rplus_le_reg_l (r * θc)). setr (r * θc). assumption.
      lra.
    -  destruct (Req_EM_T 0 (cos (θ₀ + θc))) as [zeqcost | znecost]; [
         symmetry in zeqcost; generalize (coseq0_sinneq0 _ zeqcost) as
             sintne0; intro |
         generalize (not_eq_sym znecost) as costne0; intro].
       -- setl (L * sin (θ₀ + θc) - r * cos (r * θc / r + θ₀) +
                r * cos θ₀ + y₀).
          unfold L, Hyarc. 
          fieldrewrite (r * θc / r + θ₀) (θ₀ + θc). intro. rewrite H in *. lra.
          apply (Rmult_eq_reg_l (sin (θ₀+θc))); [| assumption].
          setl (sin (θ₀ + θc) * y₁); [ assumption |]. reflexivity.
       -- setl (L * sin (θ₀ + θc) - r * cos (r * θc / r + θ₀) +
                r * cos θ₀ + y₀).
          unfold L, Hyarc. 
          fieldrewrite (r * θc / r + θ₀) (θ₀ + θc). intro. rewrite H in *. lra.
          apply (Rmult_eq_reg_l (cos (θ₀+θc))); [| assumption].
          apply (Rplus_eq_reg_l (- cos (θ₀+θc) * y₁)). setr 0.
          setl ( (x₁ - x₀) * sin (θ₀ + θc)
                 - (y₁ - y₀) * cos (θ₀ + θc)
                 + r * (cos θ₀ * cos (θ₀ + θc) +
                        sin θ₀ * sin (θ₀ + θc))
                   - r * (cos (θ₀ + θc) * cos (θ₀ + θc) +
                          sin (θ₀ + θc) * sin (θ₀ + θc))
               ) ;[ assumption |].
          
          repeat rewrite <- cos_minus.
          fieldrewrite (θ₀ + θc - (θ₀ + θc)) 0. rewrite cos_0.
          fieldrewrite (θ₀ - (θ₀ + θc)) (- θc). rewrite cos_neg.
          apply (Rplus_eq_reg_r ( - r * (cos θc - 1))).
          apply (Rmult_eq_reg_l (-1)).
          setl (((y₁ - y₀) * cos (θ₀ + θc) - (x₁ - x₀) * sin (θ₀ + θc))).
          setr (r * (cos θc - 1)). unfold r.
          setr ((y₁ - y₀) * cos (θ₀ + θc) - (x₁ - x₀) * sin (θ₀ + θc)).
          intro. apply den. apply (Rplus_eq_reg_l (- cos θc)).
          setl 0. setr (1 - cos θc). symmetry. assumption.
          reflexivity.
          discrR.
  }

  assert ({| ptx := pathx D; pty := pathy D |} = {| ptx := x₁; pty := y₁ |}).
  rewrite endx, endy. reflexivity.

  assert (0 < D) as Dpos. {
    unfold D.
    apply Rplus_lt_0_compat;
      try assumption. }

  exists (Rlt_le _ _ Dpos).
  apply path_intro; assumption.
Qed.

(* begin hide *)
Theorem intro_turning_path_std : forall (x y r : R),
    let θmax := calcθ₁ 0 0 0 x y in
    forall (phase : turning r 0 0 0 x y)
           (yne0 : y <> 0),
      exists rtp,
        path_segment (mknonnegreal (r * θmax) (nna _ _ rtp))
                     (Hx r 0 0 θmax rtp) (Hy r 0 0 θmax rtp)
                     (mkpt 0 0) (mkpt x y).
Proof.
  intros.
  assert ( ~(x = 0 /\ y = 0)) as no; try lra.
  assert (r = (x² + y²)/ (2 * y)) as rd. {
    unfold turning, Tcx, Tcy in phase.
    autorewrite with null in phase.
    rewrite Rsqr_minus in phase.
    apply (Rmult_eq_reg_r (2 * y)); try lra.
    apply (Rplus_eq_reg_r (r² - 2 * r * y)).
    setl (r²).
    setr (x² + (y² + r² - 2 * y * r)); try assumption.
  }
  specialize PI_RGT_0 as pigt0.
  assert (0 < r * θmax) as zltrtm. {
    unfold θmax, calcθ₁, Tcx, Tcy.
    arn.

    destruct (total_order_T 0 y); [destruct s|].
    + zltab.
      rewrite rd.
      apply (Rmult_lt_reg_r (2*y)); try lra.
      setl 0.
      setr (x² + y²); try lra.
      apply Rplus_le_lt_0_compat.
      apply Rle_0_sqr.
      unfold Rsqr.
      zltab.
      destruct (total_order_T 0 x) ; [destruct s|].
      apply atan2Q1; assumption.
      rewrite <- e, atan2_PI2; lra.
      specialize atan2Q2 as [atl atu]; try eassumption.
      lra.
    + lra.
    + setr (2 * -r * - atan2 y x).
      zltab.
      rewrite rd.
      apply (Rmult_lt_reg_r (2 * - y)); try lra.
      setl 0.
      setr (x² + y²); try lra.
      apply Rplus_le_lt_0_compat.
      apply Rle_0_sqr.
      unfold Rsqr.
      setr (- y * -y).
      zltab.
      destruct (total_order_T 0 x) ; [destruct s|].
      specialize atan2Q4 as [atl atu]; try eassumption.
      lra.
      rewrite <- e, atan2_mPI2; lra.
      specialize (atan2Q3 x y) as [atl atu]; try eassumption.
      setl (-0).
      apply Ropp_lt_contravar.
      apply (Rlt_trans _ (-(PI/2))); lra. }

  assert (- 2 * PI < θmax < 2 * PI) as [tml tmu]. {
    unfold θmax, calcθ₁.
    arn.
    specialize (atan2_bound _ _ no) as [atl atu].
    destruct atu as [atu |ateq].
    split; apply (Rmult_lt_reg_r (/2)); try lra.
    exfalso.
    apply atan2_PI_impl in ateq; lra. }

  assert (r * θmax < Rabs r * 2 * PI) as rtmltr2p. {
    destruct (Rge_dec r 0).
    rewrite Rabs_right; try assumption.
    destruct r0 as [rgt0 |req0].
    apply (Rmult_lt_reg_r (/r)); try lra.
    zltab.
    auto.
    lrag tmu.
    exfalso.
    rewrite req0 in zltrtm.
    lra.
    apply Rnot_ge_lt in n.
    rewrite Rabs_left; try assumption.
    setl (-(-r * θmax)).
    setr (- (-r * (- 2 * PI))).
    apply Ropp_lt_contravar.
    apply (Rmult_lt_reg_r (/ - r)).
    zltab.
    lra.
    lrag tml. }

  assert (0 <= r * θmax) as Dnnpf; try lra.
  assert (0 < r * θmax < Rabs r * 2 * PI) as rtp; try lra.
  exists rtp.
  set (D := {| nonneg := r * θmax; cond_nonneg := Dnnpf |}) in *.

  constructor.
  + apply Hx_cont.
  + apply Hy_cont.
  + unfold Hx, Hy, extension_cont, Hxarc, Hyarc.
    destruct Rle_dec; try lra.
    rewrite <- RmultRinv.
    arn.
    reflexivity.
  + unfold Hx, Hy, extension_cont, Hxarc, Hyarc.
    destruct Rle_dec; try lra.
    rewrite <- RmultRinv.
    unfold D.
    simpl.
    arn.
    fieldrewrite (r * θmax * / r) (θmax); try lra.
    intro req0.
    rewrite req0 in zltrtm.
    lra.
    fieldrewrite (- r * cos θmax + r) (r * (1 - cos θmax)).
    assert (θmax = 2 * atan2 y x) as tmd. {
      unfold θmax.
      rewrite calcth1_atan2_s.
      auto. }
    
    destruct (Rlt_dec 0 r) as [zltr | zger].
    ++ assert (0 < θmax) as zlttm. {
         clear - zltrtm zltr.
         apply (Rmult_lt_reg_l r); try assumption.
         setl 0; assumption. }

       
       assert (0 < θmax < 2 * PI) as tmr. {
         split; try assumption. }
       
       specialize (chord_property _ _ zltr tmr) as at2d.
       simpl in at2d.
       unfold atan2 in at2d.
       destruct pre_atan2 as [q [qrng [yd xd]]].
       rewrite tmd in at2d.
       
       assert (q = atan2 y x) as qd; try lra.
       unfold atan2 in qd.
       destruct pre_atan2 as [s [srng [ys xs]]].
       assert ((r * (1 - cos θmax))² + (r * sin θmax)² = y² + x²) as me;
         try (apply chord_length_std; assumption).

       rewrite me in xd, yd.
       rewrite tmd in *.
       rewrite <- at2d in *.
       rewrite qd in *.
       rewrite <- yd in ys.
       rewrite <- xd in xs.
       rewrite xs, ys.
       auto.
    ++ apply Rnot_lt_le in zger.
       destruct zger as [zgtr |zeqr].
       assert (θmax < 0) as zlttm. {
         clear - zltrtm zgtr.
         apply (Rmult_lt_reg_l (-r)); try lra. }
       
       assert (- 2 * PI < θmax < 0) as tmr. {
         split; try assumption. }
       
       specialize (chord_property_neg _ _ zgtr tmr) as at2d.
       simpl in at2d.
       unfold atan2 in at2d.
       destruct pre_atan2 as [q [qrng [yd xd]]].
       rewrite tmd in at2d.
       
       assert (q = atan2 y x) as qd; try lra.
       unfold atan2 in qd.
       destruct pre_atan2 as [s [srng [ys xs]]].
       assert ((r * (1 - cos θmax))² + (r * sin θmax)² = y² + x²) as me;
         try (apply chord_length_std; assumption).
       
       rewrite me in xd, yd.
       rewrite tmd in *.
       rewrite <- at2d in *.
       rewrite qd in *.
       rewrite <- yd in ys.
       rewrite <- xd in xs.
       rewrite xs, ys.
       auto.
       exfalso.
       clear - zltrtm zeqr.
       subst.
       lra.
    ++ simpl in n.
       apply Rnot_le_lt in n.
       lra.
  + intros.
    apply H_len; assumption.
Qed.
(* end hide *)

Theorem intro_turning_path : forall (θ₀ x₀ y₀ x₁ y₁ r : R),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (phase : turning r θ₀ x₀ y₀ x₁ y₁)
           (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (tmaxne0 : θmax <> 0)
           (tmaxne2PI : θmax <> 2 * PI)
           (rne0 : r <> 0),
      exists rtp,
        path_segment (mknonnegreal (r * θmax) (nna _ _ rtp))
                     (Hx r θ₀ x₀ θmax rtp) (Hy r θ₀ y₀ θmax rtp)
                     (mkpt x₀ y₀) (mkpt x₁ y₁).
Proof.
  intros.

  unfold θmax in *; clear θmax.
  rewrite calc_angle_std in *.

  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.

  specialize (notid_rot θ₀ _ _ _ _ no) as not.
  simpl in not.
  change (~ (x = 0 /\ y = 0)) in not.
    
  set (θmax := calcθ₁ 0 0 0 x y) in *.

  assert (y <> 0) as yne0. {
    intros yeq0.
    apply thmaxne0impl in tmaxne0.
    apply thmaxnePIimpl in tmaxne2PI.
    lra. }

  apply turning_rot in phase.
  change (turning r 0 0 0 x y) in phase.

  specialize (intro_turning_path_std _ _ _ phase yne0) as [rtp ps].
  exists rtp.
  rewrite path_std.
  assumption.
Qed.

(* begin hide *)
Theorem intro_r_path_std : forall (x₁ y₁ r : R),
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (phase : straight r 0 0 0 x₁ y₁)
           (tmaxne0 : θmax <> 0)
           (rne0 : r <> 0),
      let θc := θ1 x₁ y₁ r in
      let D := r*θc + calcL r 0 0 0 x₁ y₁ θc in
      forall (nnX : ~( r < 0 /\ θmax = 2*PI)),
      exists rtp Dnnpf, 
        path_segment (mknonnegreal D Dnnpf)
                     (Hx r 0 0 θc rtp) (Hy r 0 0 θc rtp)
                     (mkpt 0 0) (mkpt x₁ y₁).
Proof.
  intros.
  specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as nO.
  specialize (ottb_r_thetac_lb2 _ _ _ _ _ _ nO tmaxne0 rne0 phase) as rclb;
    unfold θc in rclb.
  autorewrite with null in rclb.
  change (0 < r * θc) in rclb.

  specialize (ottb_r_thetac_ub2 _ _ _ _ _ _ phase rne0 tmaxne0)
    as rcub.
  autorewrite with null in rcub.
  change (r * θc < Rabs r * 2 * PI) in rcub.

  assert (0 < r * θc < Rabs r * 2 * PI) as rcompat. {
    split; assumption. }
  
  generalize phase; intro phases.
  apply straight_rot in phases.

  generalize phases; intro ns.
  apply straight_not_stationary2 in ns.
  specialize (rotated_straight_path_equiv _ _ _ _ _ nO tmaxne0) as nst.

  autorewrite with null in *.
  assert ((~ (r < 0 /\
              x₁ < 0 /\
              y₁ = 0))) as nnX2. {
    clear - nnX.
    assert ((~ (r < 0 /\
                (x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 < 0 /\
                - (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = 0))) as gm. {
      intros [rlt0 altnnX].
      apply nnX.
      split ; [assumption| apply nxaxiscond; assumption]. }
    autorewrite with null in gm.
    assumption. }
  
  specialize (straight_path_exists2 _ _ _ _ _ _ phase rne0 tmaxne0) as Ldirg.
  specialize (ottb_parameters2_L_calc
                _ _ _ _ _ _ tmaxne0 rne0 phase ) as Leqvg.
  specialize (Leqvg Ldirg). clear Ldirg.
  autorewrite with null in *.
  change (calcL r 0 0 0 x₁ y₁ θc =
          calcL' r 0 0 0 x₁ y₁ θc) in Leqvg.
  unfold D in *.
  rewrite Leqvg in *.
  rewrite calcL'_inv in *.
  clear Leqvg.
  autorewrite with null in *.

  assert (Hxarc r 0 0 (r*θc) = r * sin θc) as Hxarcdef. {
    unfold Hxarc. rewrite sin_0.
    fieldrewrite (r * θc / r + 0) (θc). assumption. field. }

  assert (Hyarc r 0 0 (r*θc) = r * (1-cos θc)) as Hyarcdef. {
    unfold Hyarc. rewrite cos_0.
    fieldrewrite (r * θc / r + 0) (θc). assumption. field. }

  set (x := x₁) in *.
  set (y := y₁) in *.

  specialize (straight_path_exists2 0 0 0 x y r phases rne0 ) as Ldir.
  assert ((x - 0) * cos 0 + (y - 0) * sin 0 = x) as xid.
  rewrite cos_0, sin_0. field. rewrite xid in Ldir.
  assert (- (x - 0) * sin 0 + (y - 0) * cos 0 = y) as yid.
  rewrite cos_0, sin_0. field. rewrite yid in Ldir.
  set (Ldx := x - Hxarc r 0 0 (r * θc)) in *.
  set (Ldy := y - Hyarc r 0 0 (r * θc)) in *.


  unfold θmax in *.
  clear θmax.
  unfold calcθ₁ in tmaxne0.
  change (calcθ₁ 0 0 0 x y <> 0) in tmaxne0.
  set (θmax := calcθ₁ 0 0 0 x y) in *.

  specialize (Ldir tmaxne0).
  change (exists k : Z, atan2 Ldy Ldx = 0 + θc + 2 * IZR k * PI) in Ldir.
  specialize (ottb_parameters2_L_calc
                _ _ _ _ _ _ tmaxne0 rne0 phases ) as Leqv.
  rewrite xid, yid in Leqv.
  specialize (Leqv Ldir).
  change (calcL r 0 0 0 x y θc = calcL' r 0 0 0 x y θc) in Leqv.

  specialize (ottb_parameters2_compat_L
                _ _ _ _ _ _ tmaxne0 rne0 phases) as zltL.
  rewrite xid, yid in zltL.
  specialize (zltL Ldir).

  change (0 < calcL r 0 0 0 x y θc) in zltL.
  rewrite Leqv in zltL.
  set (L := calcL' r 0 0 0 x y θc) in *.

  set (pathx := Hx r 0 0 θc rcompat).
  set (pathy := Hy r 0 0 θc rcompat).
  specialize (theta1_rng _ _ _ rne0 phases) as [t1lb t1ub].
  change (-2 * PI < θc) in t1lb.
  change (θc < 2 * PI) in t1ub.

  assert (forall d : R,
             0 <= d ->
             is_RInt (magnitude (Derive pathx) (Derive pathy)) 0 d d)
    as dparam. {
    intros d zled.
    apply (H_len r 0 θc 0 0); try (left; assumption). assumption.
  }
  assert (forall d, continuous pathx d) as xcont. {
    intros. apply Hx_cont; try assumption. }
  assert (forall d, continuous pathy d) as ycont. {
    intros. apply Hy_cont; try assumption. }


  assert (mkpt (pathx 0) (pathy 0) = mkpt 0 0) as bpt. {
  unfold pathx, pathy, Hx, Hy, extension_cont, Hxarc, Hyarc.

  destruct (Rle_dec 0 (r * θc)); [ | exfalso; lra].
  fieldrewrite (0 / r + 0) (0). assumption.
  fieldrewrite (r * sin 0 - r * sin 0 + 0) (0).
  fieldrewrite (- r * cos 0 + r * cos 0 + 0) (0).
  reflexivity. }


  assert (θc <> 0) as tcne0. {
    intro tceq0.
    generalize rcompat. intro rcp.
    rewrite tceq0 in rcp.
    clear - rcp.
    lra. }

  assert (0 < 1 - cos θc) as zlt1mcostc. {
    specialize (COS_bound θc) as [clb cub].
    destruct cub as [clt |ceq].
    lra.
    destruct (total_order_T 0 θc) as [[zlttc|zeqtc]|zgttc].
    - exfalso.
      apply cos_eq_1_2PI_0 in ceq ;
        [| left; assumption | left; assumption ].
      clear - t1ub tcne0 ceq.
      destruct ceq as [teq0 | teq2PI]; lra.
    - exfalso.
      clear - zeqtc tcne0.
      lra.
    - exfalso.
      rewrite <- cos_neg in ceq.
      apply cos_eq_1_2PI_0 in ceq;
        [| left; lra| left; lra ].
      clear - t1lb tcne0 ceq.
      destruct ceq as [teq0 | teq2PI]; lra.
  } 
  
  assert (~ (Ldx = 0 /\ Ldy = 0)) as LdxLdyne01. {
    unfold Ldx, Ldy.
    rewrite Hxarcdef, Hyarcdef.
    intros [xn0 yn0].

    apply Rminus_diag_uniq in yn0.
    apply Rminus_diag_uniq in xn0.

    clear - yn0 xn0 phases rne0 t1lb t1ub tcne0 zlt1mcostc. 
    rewrite yn0, xn0 in phases at 1.
    apply straightcond in phases.
    repeat rewrite Rsqr_mult in phases.
    rewrite Rsqr_minus in phases.
    assert (1 < 1) as absurd. {
        
      apply (Rmult_lt_reg_r (2 * r² *(1 - cos θc))).
      apply Rmult_lt_0_compat;
        [apply Rmult_lt_0_compat; [lra| apply Rsqr_pos_lt; try assumption]
        |assumption].
      rewrite Rmult_1_l at 1.
      setr (r² * (1 + 1 - 2*cos θc)).
      rewrite <- (sin2_cos2 θc) at 3.
      setr (r² * (sin θc)² + r² * (1² + (cos θc)² - 2 * 1 * cos θc)).
      setl (2 * r * (r * (1 - cos θc))).
      assumption.
    }
    lra. }

  apply straightcond in phases.

  assert (0 < sqrt (Ldy² + Ldx²)) as zltM. {
    apply sqrt_lt_R0.
    specialize (Rle_0_sqr Ldy) as Ldy2ge0.
    specialize (Rle_0_sqr Ldx) as Ldx2ge0.
    destruct Ldy2ge0 as [Ldy2gt0|Ldy2eq0].
    apply Rplus_lt_le_0_compat; try assumption.
    destruct Ldx2ge0 as [Ldx2gt0|Ldx2eq0].
    apply Rplus_le_lt_0_compat; try assumption.
    right; assumption.
    exfalso. apply LdxLdyne01.
    symmetry in Ldy2eq0.
    apply Rsqr_eq_0 in Ldy2eq0.
    symmetry in Ldx2eq0.
    apply Rsqr_eq_0 in Ldx2eq0.
    split; assumption. }

  clear D.
  set (D := r * θc + L) in *.
  
  assert (pathx D = x₁) as endx. {

    unfold D.

    change (pathx (r * θc + L) = x₁).
    unfold pathx, Hx, Hxlin, extension_cont.

    destruct (Rle_dec (r * θc + L) (r * θc)).
    exfalso.
    assert (L <= 0) as Lle0. {
      apply (Rplus_le_reg_l (r * θc)).
      setr (r * θc). assumption.
    }
    lra.

    fieldrewrite (r * θc + L - r * θc) L.

    clear phase nnX nO pathx pathy dparam xcont ycont bpt.
    apply (Rplus_eq_reg_r (- Hxarc r 0 0 (r * θc))).
    setl (L * cos (0 + θc)).
    setr (x₁ - Hxarc r 0 0 (r * θc)).
    rewrite xxlate_arm, Hxarc_rot.
    rewrite <- Leqv.
    unfold L,calcL.
    
    destruct (Req_EM_T 0 (cos (0 + θc))) as [zeqcost | znecost] ; [
      symmetry in zeqcost; generalize (coseq0_sinneq0 _ zeqcost) as
          sintne0; intro |
      specialize (not_eq_sym znecost) as costne0]. 
    
    - unfold y.
      rewrite Rplus_0_l in *.
      apply (Rmult_eq_reg_r (sin θc)); try assumption.
      apply (Rplus_eq_reg_r (Hyarc r 0 0 (r * θc) * cos (0 + θc)
                             - (x₁ - 0) * sin θc)).
      rewrite cos_plus.
      set (X := Hxarc r 0 0 (r * θc)) in *.
      set (Y := Hyarc r 0 0 (r * θc)) in *.
      arn.
      setl ((y₁) * cos θc - ( x₁ * sin θc)); try assumption.
      setr ((- X) * sin θc + (Y * cos θc)).
      change ((y * cos θc - x * sin θc) =
              (- X * sin θc + Y * cos θc)).
      apply (Rplus_eq_reg_r (x * sin θc - Y * cos θc)).
      setl ((y - Y) * cos θc); try assumption.
      setr ((x - X) * sin θc); try assumption.

      change (Ldy * cos θc = Ldx * sin θc).
      destruct Ldir as [k Ldir].
      unfold atan2 in Ldir.
      destruct (pre_atan2 Ldy Ldx) as [s [srng [Ldydef Ldxdef]]].
      set (M := sqrt (Ldy² + Ldx²)) in *.

      rewrite Ldir in Ldxdef, Ldydef.
      rewrite sin_period1 in Ldydef.
      rewrite cos_period1 in Ldxdef.
      apply (Rmult_eq_compat_r (cos θc)) in Ldydef.
      apply (Rmult_eq_compat_r (sin θc)) in Ldxdef.
      rewrite Ldydef. rewrite Ldxdef. field.

    - unfold x.
      rewrite Rplus_0_l in *.
      apply (Rmult_eq_reg_r (cos θc)); try assumption.
      apply (Rplus_eq_reg_r (Hxarc r 0 0 (r * θc) * cos (0 + θc)
                             - (x₁ - 0) * cos θc)).
      rewrite cos_plus.
      set (X := Hxarc r 0 0 (r * θc)) in *.
      set (Y := Hyarc r 0 0 (r * θc)) in *.

      arn.
      setl 0; try assumption.
      setr 0; try assumption.
      reflexivity.
  }

  assert (pathy D = y₁) as endy. {
    unfold D.

    change (pathy (r * θc + L) = y₁).
    unfold pathy, Hy, Hylin, extension_cont.

    destruct (Rle_dec (r * θc + L) (r * θc)).
    exfalso.
    assert (L <= 0) as Lle0. {
      apply (Rplus_le_reg_l (r * θc)).
      setr (r * θc). assumption.
    }
    lra.

    fieldrewrite (r * θc + L - r * θc) L.

    clear phase nnX nO pathy dparam xcont ycont bpt.
    apply (Rplus_eq_reg_r (- Hyarc r 0 0 (r * θc))).
    setl (L * sin (0 + θc)).
    setr (y₁ - Hyarc r 0 0 (r * θc)).
    rewrite yxlate_arm, Hyarc_rot.
    rewrite <- Leqv.
    unfold L,calcL.

    destruct (Req_EM_T 0 (cos (0 + θc))) as [zeqcost | znecost] ; [
      symmetry in zeqcost; generalize (coseq0_sinneq0 _ zeqcost) as
          sintne0; intro |
      specialize (not_eq_sym znecost) as costne0]. 
    
    - unfold y.
      rewrite Rplus_0_l in *.
      apply (Rmult_eq_reg_r (sin θc)); try assumption.
      apply (Rplus_eq_reg_r (Hyarc r 0 0 (r * θc) * sin (0 + θc)
                             - (y₁ - 0) * sin θc)).
      rewrite sin_plus.
      set (X := Hxarc r 0 0 (r * θc)) in *.
      set (Y := Hyarc r 0 0 (r * θc)) in *.
      arn.
      setl 0; try assumption.
      setr 0; try assumption.
      reflexivity.

    - unfold x.
      rewrite Rplus_0_l in *.
      apply (Rmult_eq_reg_r (cos θc)); try assumption.
      apply (Rplus_eq_reg_r (Hxarc r 0 0 (r * θc) * sin (0 + θc)
                             - (y₁ - 0) * cos θc)).
      rewrite sin_plus.
      set (X := Hxarc r 0 0 (r * θc)) in *.
      set (Y := Hyarc r 0 0 (r * θc)) in *.
      arn.
      
      setl (x₁ * sin θc - y₁ * cos θc); try assumption.
      setr (X * sin θc - Y * cos θc); try assumption.

      apply (Rplus_eq_reg_r (y₁ * cos θc - X * sin θc)).
      setr ((y₁ - Y) * cos θc); try assumption.
      setl ((x₁ - X) * sin θc); try assumption.
      symmetry.
      
      change (Ldy * cos θc = Ldx * sin θc).
      destruct Ldir as [k Ldir].
      unfold atan2 in Ldir.
      destruct (pre_atan2 Ldy Ldx) as [s [srng [Ldydef Ldxdef]]].
      set (M := sqrt (Ldy² + Ldx²)) in *.
      
      rewrite Ldir in Ldxdef, Ldydef.
      rewrite sin_period1 in Ldydef.
      rewrite cos_period1 in Ldxdef.
      apply (Rmult_eq_compat_r (cos θc)) in Ldydef.
      apply (Rmult_eq_compat_r (sin θc)) in Ldxdef.
      rewrite Ldydef. rewrite Ldxdef. field.
    }
    
    assert ({| ptx := pathx D; pty := pathy D |} =
            {| ptx := x₁; pty := y₁ |}).
    rewrite endx, endy. reflexivity.
    exists rcompat.

    assert (0 < D) as Dnnpf. {
      unfold D.
      apply Rplus_lt_0_compat;
        try assumption.
    }

    exists (Rlt_le _ _ Dnnpf).
    apply path_intro; try assumption.
Qed.
(* end hide *)

Theorem intro_r_path : forall (x₀ y₀ x₁ y₁ θ₀ r : R),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (phase : straight r θ₀ x₀ y₀ x₁ y₁)
           (tmaxne0 : θmax <> 0)
           (rne0 : r <> 0),
      let θc := θ1 (  (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
                   (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) r in
      let D := r*θc + calcL r θ₀ x₀ y₀ x₁ y₁ θc in
      forall (nnX : ~( r < 0 /\ θmax = 2*PI)),
      exists rtp Dnnpf, 
        path_segment (mknonnegreal D Dnnpf)
                     (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp)
                     (mkpt x₀ y₀) (mkpt x₁ y₁).
Proof.
  intros.
  specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as nO.
  specialize (ottb_r_thetac_lb2 _ _ _ _ _ _ nO tmaxne0 rne0 phase) as rclb;
    unfold θc in rclb; change (0 < r * θc) in rclb.

  specialize (ottb_r_thetac_ub2 _ _ _ _ _ _ phase rne0 tmaxne0)
    as rcub.
  change (r * θc < Rabs r * 2 * PI) in rcub.

  assert (0 < r * θc < Rabs r * 2 * PI) as rcompat. {
    split; assumption. }
  
  generalize phase; intro phases.
  apply straight_rot in phases.

  generalize phases; intro ns.
  apply straight_not_stationary2 in ns.
  specialize (rotated_straight_path_equiv _ _ _ _ _ nO tmaxne0) as nst.

  assert ((~ (r < 0 /\
              (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ < 0 /\
              - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ = 0))) as nnX2. {
    clear - nnX.
    intros [rlt0 altnnX].
    apply nnX.
    split ; [assumption| apply nxaxiscond; assumption].
  }

  specialize (straight_path_exists2 _ _ _ _ _ _ phase rne0 tmaxne0) as Ldirg.
  specialize (ottb_parameters2_L_calc
                _ _ _ _ _ _ tmaxne0 rne0 phase ) as Leqvg.
  specialize (Leqvg Ldirg). clear Ldirg.
  change (calcL r θ₀ x₀ y₀ x₁ y₁ θc =
          calcL' r θ₀ x₀ y₀ x₁ y₁ θc) in Leqvg.
  unfold D in *.
  rewrite Leqvg in *.
  rewrite calcL'_inv in *.

  clear Leqvg.

  assert (Hxarc r 0 0 (r*θc) = r * sin θc) as Hxarcdef. {
    unfold Hxarc. rewrite sin_0.
    fieldrewrite (r * θc / r + 0) (θc). assumption. field. }

  assert (Hyarc r 0 0 (r*θc) = r * (1-cos θc)) as Hyarcdef. {
    unfold Hyarc. rewrite cos_0.
    fieldrewrite (r * θc / r + 0) (θc). assumption. field. }

  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.

  specialize (straight_path_exists2 0 0 0 x y r phases rne0 ) as Ldir.
  assert ((x - 0) * cos 0 + (y - 0) * sin 0 = x) as xid.
  rewrite cos_0, sin_0. field. rewrite xid in Ldir.
  assert (- (x - 0) * sin 0 + (y - 0) * cos 0 = y) as yid.
  rewrite cos_0, sin_0. field. rewrite yid in Ldir.
  set (Ldx := x - Hxarc r 0 0 (r * θc)) in *.
  set (Ldy := y - Hyarc r 0 0 (r * θc)) in *.


  unfold θmax in *.
  clear θmax.
  unfold calcθ₁ in tmaxne0.
  change (2 * atan2 y x <> 0) in tmaxne0.
  rewrite <- xid in tmaxne0.
  rewrite <- yid in tmaxne0 at 1.
  change (calcθ₁ 0 0 0 x y <> 0) in tmaxne0.
  set (θmax := calcθ₁ 0 0 0 x y) in *.

  specialize (Ldir tmaxne0).
  change (exists k : Z, atan2 Ldy Ldx = 0 + θc + 2 * IZR k * PI) in Ldir.
  specialize (ottb_parameters2_L_calc
                _ _ _ _ _ _ tmaxne0 rne0 phases ) as Leqv.
  rewrite xid, yid in Leqv.
  specialize (Leqv Ldir).
  change (calcL r 0 0 0 x y θc = calcL' r 0 0 0 x y θc) in Leqv.

  specialize (ottb_parameters2_compat_L
                _ _ _ _ _ _ tmaxne0 rne0 phases) as zltL.
  rewrite xid, yid in zltL.
  specialize (zltL Ldir).

  change (0 < calcL r 0 0 0 x y θc) in zltL.
  rewrite Leqv in zltL.
  set (L := calcL' r 0 0 0 x y θc) in *.

  set (pathx := Hx r θ₀ x₀ θc rcompat).
  set (pathy := Hy r θ₀ y₀ θc rcompat).
  specialize (theta1_rng _ _ _ rne0 phases) as [t1lb t1ub].
  change (-2 * PI < θc) in t1lb.
  change (θc < 2 * PI) in t1ub.

  assert (forall d : R,
             0 <= d ->
             is_RInt (magnitude (Derive pathx) (Derive pathy)) 0 d d)
    as dparam. {
    intros d zled.
    apply (H_len r θ₀ θc x₀ y₀); try (left; assumption). assumption.
  }
  assert (forall d, continuous pathx d) as xcont. {
    intros. apply Hx_cont; try assumption. }
  assert (forall d, continuous pathy d) as ycont. {
    intros. apply Hy_cont; try assumption. }


  assert (mkpt (pathx 0) (pathy 0) = mkpt x₀ y₀) as bpt. {
  unfold pathx, pathy, Hx, Hy, extension_cont, Hxarc, Hyarc.

  destruct (Rle_dec 0 (r * θc)); [ | exfalso; lra].
  fieldrewrite (0 / r + θ₀) (θ₀). assumption.
  fieldrewrite (r * sin θ₀ - r * sin θ₀ + x₀) (x₀).
  fieldrewrite (- r * cos θ₀ + r * cos θ₀ + y₀) (y₀).
  reflexivity. }


  assert (θc <> 0) as tcne0. {
    intro tceq0.
    generalize rcompat. intro rcp.
    rewrite tceq0 in rcp.
    clear - rcp.
    lra. }

  assert (0 < 1 - cos θc) as zlt1mcostc. {
    specialize (COS_bound θc) as [clb cub].
    destruct cub as [clt |ceq].
    lra.
    destruct (total_order_T 0 θc) as [[zlttc|zeqtc]|zgttc].
    - exfalso.
      apply cos_eq_1_2PI_0 in ceq ;
        [| left; assumption | left; assumption ].
      clear - t1ub tcne0 ceq.
      destruct ceq as [teq0 | teq2PI]; lra.
    - exfalso.
      clear - zeqtc tcne0.
      lra.
    - exfalso.
      rewrite <- cos_neg in ceq.
      apply cos_eq_1_2PI_0 in ceq;
        [| left; lra| left; lra ].
      clear - t1lb tcne0 ceq.
      destruct ceq as [teq0 | teq2PI]; lra.
  } 
  
  assert (~ (Ldx = 0 /\ Ldy = 0)) as LdxLdyne01. {
    unfold Ldx, Ldy.
    rewrite Hxarcdef, Hyarcdef.
    intros [xn0 yn0].

    apply Rminus_diag_uniq in yn0.
    apply Rminus_diag_uniq in xn0.

    clear - yn0 xn0 phases rne0 t1lb t1ub tcne0 zlt1mcostc. 
    rewrite yn0, xn0 in phases at 1.
    apply straightcond in phases.
    repeat rewrite Rsqr_mult in phases.
    rewrite Rsqr_minus in phases.
    assert (1 < 1) as absurd. {
        
      apply (Rmult_lt_reg_r (2 * r² *(1 - cos θc))).
      apply Rmult_lt_0_compat;
        [apply Rmult_lt_0_compat; [lra| apply Rsqr_pos_lt; try assumption]
        |assumption].
      rewrite Rmult_1_l at 1.
      setr (r² * (1 + 1 - 2*cos θc)).
      rewrite <- (sin2_cos2 θc) at 3.
      setr (r² * (sin θc)² + r² * (1² + (cos θc)² - 2 * 1 * cos θc)).
      setl (2 * r * (r * (1 - cos θc))).
      assumption.
    }
    lra. }

  apply straightcond in phases.

  assert (0 < sqrt (Ldy² + Ldx²)) as zltM. {
    apply sqrt_lt_R0.
    specialize (Rle_0_sqr Ldy) as Ldy2ge0.
    specialize (Rle_0_sqr Ldx) as Ldx2ge0.
    destruct Ldy2ge0 as [Ldy2gt0|Ldy2eq0].
    apply Rplus_lt_le_0_compat; try assumption.
    destruct Ldx2ge0 as [Ldx2gt0|Ldx2eq0].
    apply Rplus_le_lt_0_compat; try assumption.
    right; assumption.
    exfalso. apply LdxLdyne01.
    symmetry in Ldy2eq0.
    apply Rsqr_eq_0 in Ldy2eq0.
    symmetry in Ldx2eq0.
    apply Rsqr_eq_0 in Ldx2eq0.
    split; assumption. }

  clear D.
  set (D := r * θc + L) in *.
  
  assert (pathx D = x₁) as endx. {

    unfold D.

    change (pathx (r * θc + L) = x₁).
    unfold pathx, Hx, Hxlin, extension_cont.

    destruct (Rle_dec (r * θc + L) (r * θc)).
    exfalso.
    assert (L <= 0) as Lle0. {
      apply (Rplus_le_reg_l (r * θc)).
      setr (r * θc). assumption.
    }
    lra.

    fieldrewrite (r * θc + L - r * θc) L.

    clear phase nnX nO pathx pathy dparam xcont ycont bpt.
    apply (Rplus_eq_reg_r (- Hxarc r θ₀ x₀ (r * θc))).
    setl (L * cos (θ₀ + θc)).
    setr (x₁ - Hxarc r θ₀ x₀ (r * θc)).
    rewrite xxlate_arm, Hxarc_rot.
    rewrite <- Leqv.
    unfold L,calcL.
    
    destruct (Req_EM_T 0 (cos (0 + θc))) as [zeqcost | znecost] ; [
      symmetry in zeqcost; generalize (coseq0_sinneq0 _ zeqcost) as
          sintne0; intro |
      specialize (not_eq_sym znecost) as costne0]. 
    
    - unfold y.
      rewrite Rplus_0_l in *.
      apply (Rmult_eq_reg_r (sin θc)); try assumption.
      apply (Rplus_eq_reg_r (Hyarc r 0 0 (r * θc) * cos (θ₀ + θc)
                             - (x₁ - x₀) * sin θc)).
      rewrite cos_plus.
      set (X := Hxarc r 0 0 (r * θc)) in *.
      set (Y := Hyarc r 0 0 (r * θc)) in *.
      setl (- (x₁ - x₀) * sin θ₀* cos θ₀ * cos θc
            - (x₁ - x₀) * (1 - (sin θ₀)²)* sin θc
            + (y₁ - y₀) * cos θ₀* cos θ₀ * cos θc
            - (y₁ - y₀) * cos θ₀* sin θ₀ * sin θc
           ); try assumption.
      rewrite <- cos2.
      setl (((- (x₁ - x₀) * sin θ₀
              + (y₁ - y₀) * cos θ₀ )* cos θc
             - ((x₁ - x₀) * cos θ₀ 
              + (y₁ - y₀) * sin θ₀ )*sin θc
            )* cos θ₀).
      setr ((- X * sin θc + Y * cos θc)* cos θ₀).
      change ((y * cos θc - x * sin θc)*cos θ₀ =
              (- X * sin θc + Y * cos θc) * cos θ₀).
      destruct (Req_dec (cos θ₀) 0) as [costeq0 | costne0];
        [rewrite costeq0, Rmult_0_r, Rmult_0_r; reflexivity|].
      apply (Rmult_eq_reg_r (/ cos θ₀));
        [|apply Rinv_neq_0_compat; assumption].
      apply (Rplus_eq_reg_r (x * sin θc - Y * cos θc)).
      setl ((y - Y) * cos θc); try assumption.
      setr ((x - X) * sin θc); try assumption.

      change (Ldy * cos θc = Ldx * sin θc).
      destruct Ldir as [k Ldir].
      unfold atan2 in Ldir.
      destruct (pre_atan2 Ldy Ldx) as [s [srng [Ldydef Ldxdef]]].
      set (M := sqrt (Ldy² + Ldx²)) in *.

      rewrite Ldir in Ldxdef, Ldydef.
      rewrite sin_period1 in Ldydef.
      rewrite cos_period1 in Ldxdef.
      apply (Rmult_eq_compat_r (cos θc)) in Ldydef.
      apply (Rmult_eq_compat_r (sin θc)) in Ldxdef.
      rewrite Ldydef. rewrite Ldxdef. field.

    - unfold x.
      rewrite Rplus_0_l in *.
      apply (Rmult_eq_reg_r (cos θc)); try assumption.
      apply (Rplus_eq_reg_r (Hxarc r 0 0 (r * θc) * cos (θ₀ + θc)
                             - (x₁ - x₀) * cos θc)).
      rewrite cos_plus.
      set (X := Hxarc r 0 0 (r * θc)) in *.
      set (Y := Hyarc r 0 0 (r * θc)) in *.

      setl ((- (x₁ - x₀) * (1 - (cos θ₀)²) +
             (y₁ - y₀) * sin θ₀* cos θ₀) * cos θc
            - ((x₁ - x₀) * cos θ₀* sin θ₀ +
               (y₁ - y₀) * sin θ₀* sin θ₀) * sin θc); try assumption.
      rewrite <- sin2.
      setl (((- (x₁ - x₀) * sin θ₀ +
             (y₁ - y₀) * cos θ₀) * cos θc
            - ((x₁ - x₀) * cos θ₀ +
               (y₁ - y₀) * sin θ₀) * sin θc)* sin θ₀); try assumption.
      setr (( - X * sin θc + Y * cos θc)* sin θ₀).
      
      change ((y * cos θc - x * sin θc)*sin θ₀ =
              ( - X * sin θc + Y * cos θc ) * sin θ₀).
      destruct (Req_dec (sin θ₀) 0) as [sinteq0 | sintne0];
        [rewrite sinteq0, Rmult_0_r, Rmult_0_r; reflexivity|].
      apply (Rmult_eq_reg_r (/ sin θ₀));
        [|apply Rinv_neq_0_compat; assumption].
      apply (Rplus_eq_reg_r (x * sin θc - Y * cos θc)).
      setl ((y - Y) * cos θc); try assumption.
      setr ((x - X) * sin θc); try assumption.

      change (Ldy * cos θc = Ldx * sin θc).
      destruct Ldir as [k Ldir].
      unfold atan2 in Ldir.
      destruct (pre_atan2 Ldy Ldx) as [s [srng [Ldydef Ldxdef]]].
      set (M := sqrt (Ldy² + Ldx²)) in *.

      rewrite Ldir in Ldxdef, Ldydef.
      rewrite sin_period1 in Ldydef.
      rewrite cos_period1 in Ldxdef.
      apply (Rmult_eq_compat_r (cos θc)) in Ldydef.
      apply (Rmult_eq_compat_r (sin θc)) in Ldxdef.
      rewrite Ldydef. rewrite Ldxdef. field.
  }
  
  assert (pathy D = y₁) as endy. {
    unfold D.

    change (pathy (r * θc + L) = y₁).
    unfold pathy, Hy, Hylin, extension_cont.

    destruct (Rle_dec (r * θc + L) (r * θc)).
    exfalso.
    assert (L <= 0) as Lle0. {
      apply (Rplus_le_reg_l (r * θc)).
      setr (r * θc). assumption.
    }
    lra.

    fieldrewrite (r * θc + L - r * θc) L.

    clear phase nnX nO pathy dparam xcont ycont bpt.
    apply (Rplus_eq_reg_r (- Hyarc r θ₀ y₀ (r * θc))).
    setl (L * sin (θ₀ + θc)).
    setr (y₁ - Hyarc r θ₀ y₀ (r * θc)).
    rewrite yxlate_arm, Hyarc_rot.
    rewrite <- Leqv.
    unfold L,calcL.

    destruct (Req_EM_T 0 (cos (0 + θc))) as [zeqcost | znecost] ; [
      symmetry in zeqcost; generalize (coseq0_sinneq0 _ zeqcost) as
          sintne0; intro |
      specialize (not_eq_sym znecost) as costne0]. 
    
    - unfold y.
      rewrite Rplus_0_l in *.
      apply (Rmult_eq_reg_r (sin θc)); try assumption.
      apply (Rplus_eq_reg_r (Hyarc r 0 0 (r * θc) * sin (θ₀ + θc)
                             - (y₁ - y₀) * sin θc)).
      rewrite sin_plus.
      set (X := Hxarc r 0 0 (r * θc)) in *.
      set (Y := Hyarc r 0 0 (r * θc)) in *.
      setl ((- (x₁ - x₀) * sin θ₀ * sin θ₀ 
             + (y₁ - y₀) * cos θ₀ * sin θ₀)* cos θc
             - ((x₁ - x₀) * sin θ₀ * cos θ₀
                + (y₁ - y₀) * (1 - (cos θ₀)²))* sin θc);
        try assumption.
      rewrite <- sin2.
      setl (((- (x₁ - x₀) * sin θ₀ 
             + (y₁ - y₀) * cos θ₀) * cos θc -
            ((x₁ - x₀)  * cos θ₀ +
             (y₁ - y₀) * sin θ₀) * sin θc)* sin θ₀).
      setr ((- X * sin θc + Y * cos θc)* sin θ₀).
      change ((y * cos θc - x * sin θc)*sin θ₀ =
              (- X * sin θc + Y * cos θc) * sin θ₀).
      destruct (Req_dec (sin θ₀) 0) as [costeq0 | costne0];
        [rewrite costeq0, Rmult_0_r, Rmult_0_r; reflexivity|].
      apply (Rmult_eq_reg_r (/ sin θ₀));
        [|apply Rinv_neq_0_compat; assumption].
      apply (Rplus_eq_reg_r (x * sin θc - Y * cos θc)).
      setl ((y - Y) * cos θc); try assumption.
      setr ((x - X) * sin θc); try assumption.

      change (Ldy * cos θc = Ldx * sin θc).
      destruct Ldir as [k Ldir].
      unfold atan2 in Ldir.
      destruct (pre_atan2 Ldy Ldx) as [s [srng [Ldydef Ldxdef]]].
      set (M := sqrt (Ldy² + Ldx²)) in *.

      rewrite Ldir in Ldxdef, Ldydef.
      rewrite sin_period1 in Ldydef.
      rewrite cos_period1 in Ldxdef.
      apply (Rmult_eq_compat_r (cos θc)) in Ldydef.
      apply (Rmult_eq_compat_r (sin θc)) in Ldxdef.
      rewrite Ldydef. rewrite Ldxdef. field.

    - unfold x.
      rewrite Rplus_0_l in *.
      apply (Rmult_eq_reg_r (cos θc)); try assumption.
      apply (Rplus_eq_reg_r (Hxarc r 0 0 (r * θc) * sin (θ₀ + θc)
                             - (y₁ - y₀) * cos θc)).
      rewrite sin_plus.
      set (X := Hxarc r 0 0 (r * θc)) in *.
      set (Y := Hyarc r 0 0 (r * θc)) in *.
      
      setl ((x₁ - x₀) * cos θ₀* sin θ₀ * cos θc
            + (x₁ - x₀) * cos θ₀* cos θ₀ * sin θc
            - (y₁ - y₀) * (1 - (sin θ₀)²) * cos θc
            + (y₁ - y₀) * sin θ₀* cos θ₀ * sin θc
           ); try assumption.
      rewrite <- cos2.
      setl ((- (-(x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) * cos θc
             + ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) * sin θc)*
            cos θ₀).
      setr (( X * sin θc - Y * cos θc)* cos θ₀).
      
      change ((- y * cos θc + x * sin θc)*cos θ₀ =
              (X * sin θc - Y * cos θc ) * cos θ₀).
      destruct (Req_dec (cos θ₀) 0) as [sinteq0 | sintne0];
        [rewrite sinteq0, Rmult_0_r, Rmult_0_r; reflexivity|].
      apply (Rmult_eq_reg_r (/ cos θ₀));
        [|apply Rinv_neq_0_compat; assumption].
      apply (Rplus_eq_reg_r (y * cos θc - X * sin θc)).
      setr ((y - Y) * cos θc); try assumption.
      setl ((x - X) * sin θc); try assumption.
      symmetry.
      
      change (Ldy * cos θc = Ldx * sin θc).
      destruct Ldir as [k Ldir].
      unfold atan2 in Ldir.
      destruct (pre_atan2 Ldy Ldx) as [s [srng [Ldydef Ldxdef]]].
      set (M := sqrt (Ldy² + Ldx²)) in *.
      
      rewrite Ldir in Ldxdef, Ldydef.
      rewrite sin_period1 in Ldydef.
      rewrite cos_period1 in Ldxdef.
      apply (Rmult_eq_compat_r (cos θc)) in Ldydef.
      apply (Rmult_eq_compat_r (sin θc)) in Ldxdef.
      rewrite Ldydef. rewrite Ldxdef. field.
    }
    
    assert ({| ptx := pathx D; pty := pathy D |} =
            {| ptx := x₁; pty := y₁ |}).
    rewrite endx, endy. reflexivity.
    exists rcompat.

    assert (0 < D) as Dnnpf. {
      unfold D.
      apply Rplus_lt_0_compat;
        try assumption.
    }

    exists (Rlt_le _ _ Dnnpf).
    apply path_intro; try assumption.
Qed.


Lemma ottb_r_constraints :
  forall (D:nonnegreal) (x₀ y₀ x₁ y₁ r θ₀ θc:R) rtp
         (P : path_segment D (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    (turning r θ₀ x₀ y₀ x₁ y₁ \/ straight r θ₀ x₀ y₀ x₁ y₁).
Proof.
  intros.
  
  addzner.
  assert (0 <= r * θc) as zlerth. lra.
  rewrite (Rmult_comm (Rabs r)) in rtpu.
  rename rtpu into thle2rPI.
  assert (0 <= D) as zleD. destruct D. simpl. assumption.

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

  destruct (Rle_dec D (r*θc)).
  destruct (Rlt_dec D (Rabs r *PI)).
  + left.
    assert (0 <= r * θc < 2 * Rabs r * PI) as rtcorder. split; assumption.
    assert (0 <= nonneg D <= r * θc) as Dorder. split; assumption.
    apply (ottb_distance_turning D x₀ y₀ x₁ y₁ r θ₀ θc rtp P Dorder).
  
  + apply Rnot_lt_ge in n.
    left.
    assert (0 <= r * θc < 2 * Rabs r * PI) as rtcorder. split; assumption.
    assert (0 <= nonneg D <= r * θc) as Dorder. split; assumption.
    apply (ottb_distance_turning D x₀ y₀ x₁ y₁ r θ₀ θc rtp P Dorder).
    
  + right.
    apply Rnot_le_lt in n.
    assert (0 <= r * θc < 2 * Rabs r * PI) as rtcorder. {
    split; assumption. }
    assert (r * θc < nonneg D) as Dorder. assumption.
    apply (ottb_distance_straight
             D x₀ y₀ x₁ y₁ r θ₀ θc rtp P Dorder).
Qed.

(* begin hide *)

Lemma ottb_compute_turning_r_s :
  forall x y r θr stp Dr
         (phase : turning r 0 0 0 x y)
         (no : ~(x=0 /\ y=0))
         (P : path_segment Dr (Hx r 0 0 θr stp) (Hy r 0 0 θr stp)
                           (mkpt 0 0) (mkpt x y)),
    r = (y²+x²)/(2*y).
Proof.
  intros.
  addzner.
  inversion P.
  clear abnd.
  injection bbnd; intros Hyd Hxd.

  unfold Hx, Hy, extension_cont in Hxd, Hyd.
  destruct Rle_dec.

  * unfold turning, Tcx, Tcy in phase.
    autorewrite with null in phase.
    rewrite Rsqr_minus in phase.

    assert (y <> 0) as yne0. {
      intro yeq0.
      rewrite yeq0 in phase.
      autorewrite with null in phase.
      assert (x = 0). {
        apply (Rmult_eq_reg_r x).
        apply (Rplus_eq_reg_r r²).
        symmetry.
        lrag phase.
        lra. }
      lra. }

    apply (Rmult_eq_reg_r (2 * y)); [|lra].
    apply (Rplus_eq_reg_r (- 2 * y * r + r²)).
    setl r².
    setr (x² + (y² + r² - 2 * y * r)); assumption.

    * apply Rnot_le_lt in n.
      specialize (ottb_distance_straight Dr 0 0 _ _ _ _ _ stp P n)
        as phasec.
      unfold straight, turning in phase, phasec.
      lra.
Qed.



Lemma ottb_compute_straight_r_s :
  forall x y r θr stp Dr
         (phase : straight r 0 0 0 x y)
         (P : path_segment Dr (Hx r 0 0 θr stp) (Hy r 0 0 θr stp)
                            (mkpt 0 0) (mkpt x y)),
      r = (x * sin θr - y * cos θr) / (1 - cos θr).
Proof.
  intros.
  addzner.
  inversion P.
  clear abnd.
  injection bbnd; intros Hyd Hxd.
  
  unfold Hx, Hy, extension_cont in Hxd, Hyd.
  destruct Rle_dec.

  * assert (0 <= Dr <= r * θr) as drng. {
      assert (0 <= Dr).
      destruct Dr.
      simpl in *.
      lra.
      split; lra. }
  
    specialize (ottb_distance_turning
                  Dr 0 0 _ _ _ _ _ stp P drng) as phasec.
    
    clear - phase phasec.
    unfold straight, turning in *.
    lra.

  * assert (θr <> 0) as trne0. {
      intro treq0.
      rewrite treq0 in rtpl.
      autorewrite with null in rtpl.
      lra. }
    
    assert (cos θr <> 1) as ctrne1. {
      
      intro ctreq1.
      destruct (Rle_dec 0 θr).
      destruct r0.
      + assert (0 < r) as zltr. {
          apply (Rmult_lt_reg_r θr);
            [assumption|
             arn;
             assumption]. }
        
        apply cosθeq1 in ctreq1; [lra|].
        split.
        lra.
        apply (Rmult_lt_reg_r (Rabs r));
          [rewrite Rabs_right;
           [assumption|
            left; assumption]|].
        rewrite Rabs_right at 1;
          [|left; assumption].
        rewrite Rmult_comm.
        rewrite (Rmult_comm _ (Rabs r)).
        rewrite <- Rmult_assoc.
        assumption.
      + lra.
      + apply Rnot_le_lt in n0.
        assert (r < 0) as zltr. {
          apply (Rmult_lt_reg_r (- θr));
            [lra| arn; lra]. }
        rewrite <- cos_neg in ctreq1.
        apply cosθeq1 in ctreq1; [lra|].
        split;[lra|].
        apply (Rmult_lt_reg_r (Rabs r)).
        rewrite Rabs_left;lra.
        rewrite Rabs_left at 1;
          [setl (r * θr);
           rewrite (Rmult_comm _ (Rabs r));
           rewrite <- Rmult_assoc;
           assumption| assumption]. }
    
    assert (0 < 1 - cos θr) as costr. {
      apply (Rplus_lt_reg_r (cos θr)).
      setr 1.
      arn.
      specialize (COS_bound θr) as [cbl cbu].
      destruct cbu as [cblt | cbe].
      assumption.
      exfalso.
      apply ctrne1.
      assumption. }
    
    apply Rnot_le_lt in n.
    unfold Hxlin in Hxd.
    unfold Hylin in Hyd.
    unfold Hxarc, Hyarc in Hxd, Hyd.
    autorewrite with null in *.
    assert (r * θr / r = θr) as id. {
      field.
      lra. }
    rewrite id in *. clear id.
    apply (Rmult_eq_compat_r (sin θr)) in Hxd.
    apply (Rmult_eq_compat_r (cos θr)) in Hyd.
    apply (Rmult_eq_reg_r (1 - cos θr)); [|lra].
    rewrite <- Hyd, <- Hxd.
    setr (r * ((sin θr)² + (cos θr)²) - r * cos θr);
      [lra| rewrite sin2_cos2; field].
Qed.

Lemma ottb_compute_r_s :
  forall x y r θr stp Dr
         (no : ~(x=0 /\ y=0))
         (P : path_segment Dr (Hx r 0 0 θr stp) (Hy r 0 0 θr stp)
                           (mkpt 0 0) (mkpt x y)),
    (turning r 0 0 0 x y /\ r = (y² + x²) / (2 * y)) \/
    (straight r 0 0 0 x y /\ r = (x * sin θr - y * cos θr) / (1 - cos θr)).
Proof.
  intros.

  specialize (ottb_r_constraints _ _ _ _ _ _ _ _ stp P) as ts.
  destruct ts as [t| s].
  + left.
    split; try assumption.
    eapply ottb_compute_turning_r_s; try eassumption.
  + right.
    split; try assumption.
    eapply ottb_compute_straight_r_s; try eassumption.
Qed.
(* end hide *)


Lemma ottb_compute_r :
  forall θ₀ x₀ y₀ x₁ y₁ r θr stp Dr
         (ni : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
         (P : path_segment Dr (Hx r θ₀ x₀ θr stp) (Hy r θ₀ y₀ θr stp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    let x := (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ in
    let y := - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ in
    (turning r θ₀ x₀ y₀ x₁ y₁ /\ r = (y² + x²) / (2 * y)) \/
    (straight r θ₀ x₀ y₀ x₁ y₁ /\ r = (x * sin θr - y * cos θr) / (1 - cos θr)).
Proof.
  intros.
  unfold x, y in *; clear x y.
  rewrite path_std in P.
  set (x := (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in *.
  set (y := - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in *.

  assert (~(x=0 /\ y=0)) as no. {
    apply notid_rot.
    assumption. }

  apply ottb_compute_r_s in P.
  destruct P as [[c rd]|[c rd]].
  left.
  apply rot_turning in c.
  split; assumption.
  right.
  apply rot_straight in c.
  split; assumption.
  assumption.
Qed.

(* begin hide *)

Lemma ottb_compute_straight_r:
  forall θ₀ x₀ y₀ x₁ y₁ r θr stp Dr
         (phaser : straight r θ₀ x₀ y₀ x₁ y₁)
         (P : path_segment Dr (Hx r θ₀ x₀ θr stp) (Hy r θ₀ y₀ θr stp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    r = ((x₁ - x₀) * sin (θ₀ + θr) - (y₁ - y₀) * cos (θ₀ + θr))
          / (1 - cos θr).
Proof.
  intros.
  apply straight_rot in phaser.
  apply path_std in P.
  rewrite rxlate.
  eapply ottb_compute_straight_r_s;
    try eassumption.
Qed.

      
Lemma ottb_compute_straight_t_s :
  forall x y r θr stp Dr
         (phaser : straight r 0 0 0 x y)
         (P : path_segment Dr (Hx r 0 0 θr stp) (Hy r 0 0 θr stp)
                           (mkpt 0 0) (mkpt x y)),
      θr = θ1 x y r.
Proof.
  intros.
  addzner.

  specialize (npx_straight_s _ _ _ _ stp Dr phaser P) as npx.

  set (θmax := calcθ₁ 0 0 0 x y).
  assert (θmax <> 0) as tmne0. {
    intro tmeq0.
    unfold θmax, calcθ₁ in tmeq0.
    autorewrite with null in tmeq0.
    apply (Rmult_eq_compat_r (/2)) in tmeq0.
    assert (atan2 y x = 0) as at2eq0.
    lrag tmeq0.
    apply atan2_0_impl in at2eq0 as [lb ub].
    apply npx.
    split; lra.
    intro no.
    apply npx.
    split; lra. }

  inversion P.
  clear abnd contx conty pzbydist.
  inversion bbnd as [[Hxd Hyd]].
  clear bbnd.
  rewrite Hxd, Hyd.
  unfold Hx, Hxlin, extension_cont in Hxd, Hyd.
  unfold Hy, Hylin, extension_cont in Hxd, Hyd.
  autorewrite with null in Hxd, Hyd.

  destruct Rle_dec.
  + assert (0 <= Dr <= r * θr) as drng. {
      split.
      apply cond_nonneg.
      assumption. }
    specialize (ottb_distance_turning _ _ _ _ _ _ _ _ stp P drng) as trnc.
    unfold turning in trnc.
    unfold straight in phaser.
    lra.
  + apply Rnot_le_lt in n.
    apply not_eq_sym in zner.
    set (M := (Dr - r * θr)) in *.
    assert (0 < M) as zltM. {
      unfold M.
      lra. }
    
    unfold Hxarc in Hxd.
    unfold Hyarc in Hyd.
    assert (r * θr / r = θr) as id. {
      field.
      lra. }
    rewrite id in *. clear id.
    autorewrite with null in Hxd, Hyd.
    
    assert (x - r * sin θr = M * cos θr) as xarm. {
      apply (Rplus_eq_reg_r (r * sin θr)).
      symmetry.
      lrag Hxd. }
    assert (y - r * (1 - cos θr) = M * sin θr) as yarm. {
      apply (Rplus_eq_reg_r (r * (1 - cos θr))).
      symmetry.
      lrag Hyd. }
    clear Hxd Hyd.
    specialize PI_RGT_0 as pigt0.
    assert (2 * PI > 0) as tpigt0. lra.
    specialize (inrange_mT2T2 θr _ tpigt0) as [k [tlrng thrng]].
    assert (-PI < θr + 2 * IZR k * PI <= PI) as trng; try lra.
    clear tlrng thrng.
    
    specialize (atan2_left_inv _ _ trng zltM) as at2d.
    rewrite sin_period1, cos_period1 in at2d.
    rewrite <- xarm, <- yarm in at2d.
    clear xarm yarm.
    change (κ₂ x y r θr = θr + 2 * IZR k * PI) in at2d.

    rewrite (k2_periodic _ _ _ k) in at2d.
    assert (~ (x - r * sin (θr + 2 * IZR k * PI) = 0 /\
               y - r * (1 - cos (θr + 2 * IZR k * PI)) = 0))
      as no. {
      rewrite <- k2_periodic in at2d.
      rewrite sin_period1, cos_period1.
      unfold κ₂ in at2d.
      clear - phaser zner.
      apply straightcond in phaser.
      intros [xd yd].
      apply Rminus_diag_uniq in xd.
      apply Rminus_diag_uniq in yd.
      rewrite xd, yd in phaser.

      assert (2 * (1 - cos θr) < 2 * (1 - cos θr)) as contr. {
        rewrite Rmult_minus_distr_l at 2.
        setr (1 + 1 - 2 * cos θr).
        rewrite <- (sin2_cos2 θr) at 2.
        apply (Rmult_lt_reg_r (r²)).
        specialize (Rle_0_sqr r) as r2nn.
        destruct r2nn. assumption.
        exfalso.
        symmetry in H.
        apply Rsqr_eq_0 in H.
        lra.
        lrag phaser. }
      lra. }
    
    assert (exists m, κ₂ x y r (θr + 2 * IZR k * PI) =
                      θr + 2 * IZR k * PI + IZR m * PI) as at3d. {
      exists 0%Z.
      lra. }

    rewrite <- (k_extrema_vals _ _ _ _ trng zner no) in at3d.
    rewrite <- k2_periodic in at2d.
    rewrite <- k'_periodic in at3d.
    
    rewrite <- signeq0_eqv in at3d.
    apply (k_prime_theta1_theta2 _ _ _ _ zner phaser)
      in at3d as [m trd].

    destruct trd as [trt1 | trt2].
    ++ specialize (theta1_rsgn_bnd _ _ _ zner phaser)
        as [rp rn].
       destruct (Rlt_dec r 0) as [rlt0 |zltr];
         [|apply Rnot_lt_le in zltr;
           destruct zltr as [zlt | zeq]; [|lra]].
       +++ specialize (rn rlt0) as [t1lb t1ub].
           assert (- 2 * PI < θr < 0) as [trlb trub]. {
             split.
             apply (Rmult_lt_reg_r (Rabs r));
               [rewrite Rabs_left; lra|].
             rewrite Rabs_left at 2; try assumption.
             setl (- (Rabs r * 2 * PI)).
             setr (- (r * θr)).
             apply Ropp_lt_contravar.
             assumption.
             apply (Rmult_lt_reg_r (- r));
               [lra|].
             setl (- (r * θr)).
             setr (- 0).
             apply Ropp_lt_contravar.
             assumption. }
           assert (m = 0%Z) as meq0. {
             destruct m.
             - reflexivity.
             - exfalso.
               rewrite trt1 in trub.
               specialize (IZRposge1 p) as ip.
               generalize trub.
               change (~(θ1 x y r + 2 * IZR (Z.pos p) * PI < 0)).
               apply Rle_not_lt.
               apply (Rle_trans _ (θ1 x y r + 2 * 1 * PI)).
               lra.
               apply (Rplus_le_reg_r (-θ1 x y r)).
               apply (Rmult_le_reg_r (/ PI)).
               zltab.
               setl 2. lra.
               setr (2 * IZR (Z.pos p)). lra.
               lra.
             - exfalso.
               rewrite trt1 in trlb.
               specialize (IZRneglen1 p) as ip.
               generalize trlb.
               change (~(- 2 * PI < θ1 x y r + 2 * IZR (Z.neg p) * PI)).
               apply Rle_not_lt.
               apply (Rle_trans _ (θ1 x y r + 2 * -1  * PI)).
               apply (Rplus_le_reg_r (-θ1 x y r)).
               apply (Rmult_le_reg_r (/ PI)).
               zltab.
               setr (-2). lra.
               setl (2 * IZR (Z.neg p)). lra.
               lra.
               lra. }
           rewrite meq0 in trt1.
           autorewrite with null in trt1.
           assumption.
       +++ specialize (rp zlt) as [t1lb t1ub].
           assert (0 < θr < 2 * PI) as [trlb trub]. {
             split.
             apply (Rmult_lt_reg_r (r));
               [lra|].
             setr ((r * θr)).
             setl ( 0).
             assumption.
             apply (Rmult_lt_reg_r (Rabs r));
               [rewrite Rabs_right; lra|].
             rewrite Rabs_right at 1; try lra. }
           assert (m = 0%Z) as meq0. {
             destruct m.
             - reflexivity.
             - exfalso.
               rewrite trt1 in trub.
               specialize (IZRposge1 p) as ip.
               generalize trub.
               change (~(θ1 x y r + 2 * IZR (Z.pos p) * PI < 2 * PI)).
               apply Rle_not_lt.
               apply (Rle_trans _ (θ1 x y r + 2 * 1 * PI)).
               lra.
               apply (Rplus_le_reg_r (-θ1 x y r)).
               apply (Rmult_le_reg_r (/ PI)).
               zltab.
               setl 2. lra.
               setr (2 * IZR (Z.pos p)). lra.
               lra.
             - exfalso.
               rewrite trt1 in trlb.
               specialize (IZRneglen1 p) as ip.
               generalize trlb.
               change (~(0 < θ1 x y r + 2 * IZR (Z.neg p) * PI)).
               apply Rle_not_lt.
               apply (Rle_trans _ (θ1 x y r + 2 * -1  * PI)).
               apply (Rplus_le_reg_r (-θ1 x y r)).
               apply (Rmult_le_reg_r (/ PI)).
               zltab.
               setr (-2). lra.
               setl (2 * IZR (Z.neg p)). lra.
               lra.
               lra. }
           rewrite meq0 in trt1.
           autorewrite with null in trt1.
           assumption.
    ++ exfalso.
       rewrite trt2 in at2d.
       rewrite <- k2_periodic in at2d.
       clear trt2 no.
       specialize (k2_theta2_odd x y r) as [p k2t2]; try assumption.
       rewrite Rplus_assoc in at2d.
       assert (2 * IZR m * PI + 2 * IZR k * PI =
               IZR (2 * (m + k)) * PI) as id. {
         rewrite mult_IZR, plus_IZR.
         field. }
       rewrite id in at2d.
       rewrite k2t2 in at2d.
       clear id k2t2.
       assert (IZR (2 * p + 1) = IZR (2 * (m + k))) as id. {
         apply (Rmult_eq_reg_r PI).
         apply (Rplus_eq_reg_l (θ2 x y r)).
         assumption.
         lra. }
       clear - id.
       apply eq_IZR in id.
       omega.
Qed.

Lemma npx_turning_s :
  forall x y r θr stp Dr
         (phaser : turning r 0 0 0 x y)
         (P : path_segment Dr (Hx r 0 0 θr stp) (Hy r 0 0 θr stp)
                           (mkpt 0 0) (mkpt x y)),
    ~ (0 < x /\ y = 0).
Proof.
  intros.
  addzner.

  intros [zlex yeq0].
  inversion P.
  clear contx conty abnd pzbydist.
  injection bbnd.
  clear bbnd.
  intros Hyd Hxd.
  unfold Hy in Hyd.
  unfold Hx in Hxd.
  unfold extension_cont in *.
  destruct Rle_dec.
  + unfold Hxarc, Hyarc in Hyd, Hxd.
    unfold turning, Tcx, Tcy in phaser.
    autorewrite with null in *.
    rewrite Rsqr_minus in phaser.
    assert (2 * y * r = x² + y²) as phaset. {
      apply (Rplus_eq_reg_r (- 2 * y * r + r²)).
      lrag phaser. }
    clear phaser.

    rewrite <- Hxd in zlex.
    rewrite <- Hyd in yeq0.
    assert (cos (Dr / r) = 1) as ceq1;
      [apply (Rmult_eq_reg_r r); lra|].
    destruct (total_order_T 0 r);
      [destruct s; [|lra]|].
    
    ++ assert (0 <= Dr / r) as dl. {
         apply (Rmult_le_reg_r r).
         assumption.
         destruct Dr.
         simpl in *.
         lrag cond_nonneg. }
       
       assert (Dr / r <= θr) as ul. {
         apply (Rmult_le_reg_r r).
         assumption.
         lrag r0. }

       assert (0 <= Dr / r < 2 * PI) as drrng. {
         split.
         assumption.
         apply (Rle_lt_trans _ θr).
         assumption.
         apply (Rmult_lt_reg_r (Rabs r)).
         rewrite Rabs_right; [assumption|lra].
         rewrite Rabs_right at 1; [|lra].
         rewrite Rmult_comm.
         rewrite (Rmult_comm _ (Rabs r)).
         rewrite <- Rmult_assoc.
         assumption. }
       apply cosθeq1 in ceq1; try assumption.
       rewrite ceq1, sin_0, Rmult_0_r in zlex.
       lra.

  ++ assert (0 <= Dr / - r) as dl. {
         apply (Rmult_le_reg_r (-r)).
         lra.
         destruct Dr.
         simpl in *.
         lrag cond_nonneg. }
       
       assert (Dr / - r <= - θr) as ul. {
         apply (Rmult_le_reg_r (-r)).
         lra.
         lrag r0. }

       assert (0 <= Dr / - r < 2 * PI) as drrng. {
         split.
         assumption.
         apply (Rle_lt_trans _ (-θr)).
         assumption.
         apply (Rmult_lt_reg_r (Rabs r)).
         rewrite Rabs_left; [lra|assumption].
         rewrite Rabs_left at 1; [|lra].
         rewrite Rmult_comm.
         setl (r * θr).
         rewrite (Rmult_comm _ (Rabs r)).
         rewrite <- Rmult_assoc.
         assumption. }
     rewrite <- cos_neg in ceq1.
     assert (- (Dr / r) = Dr / -r) as id. {
       setl (Dr / - r). lra.
       reflexivity. }
     rewrite id in ceq1. clear id.
     apply cosθeq1 in ceq1; try assumption.
     assert (Dr / r = - (Dr / -r)) as id. {
       setl (- (Dr / - r)). lra.
       reflexivity. }
     rewrite id, sin_neg in zlex.
     rewrite ceq1, sin_0, Ropp_0, Rmult_0_r in zlex.
     lra.
     
  + apply Rnot_le_lt in n.
    specialize (ottb_distance_straight _ _ _ _ _ _ _ _ stp P n)
      as phaset.
    unfold turning, straight in phaser, phaset.
    lra.
Qed.

Lemma ottb_compute_turning_t_s :
  forall (x y r θr : R) (stp : 0 < r * θr < Rabs r * 2 * PI)
         (Dr : nonnegreal)
         (no : ~ (x = 0 /\ y = 0))
         (phaser : turning r 0 0 0 x y)
         (P : path_segment Dr (Hx r 0 0 θr stp) (Hy r 0 0 θr stp)
                           (mkpt 0 0) (mkpt x y)),
    let θ := calcθ₁ 0 0 0 x y in
    Rabs θ <= Rabs θr < 2 * PI.
Proof.
  intros.
  addzner.

  specialize (npx_turning_s _ _ _ _ stp Dr phaser P) as npx.

  destruct (Req_dec θ 0) as [tmeq0 |tmne0].
  + rewrite tmeq0.
    arn.
    unfold Rabs at 1.
    destruct Rcase_abs;[lra|].
    split.
    unfold Rabs.
    destruct (Rcase_abs);
      lra.
    apply (Rmult_lt_reg_r (Rabs r)).
    unfold Rabs.
    destruct Rcase_abs; lra.
    rewrite Rmult_comm at 1.
    rewrite <- Rabs_mult.
    rewrite Rabs_right; lra.

  + inversion P.
    clear abnd contx conty pzbydist.
    inversion bbnd as [[Hxd Hyd]].
    clear bbnd.
    unfold Hx, Hxlin, extension_cont in Hxd, Hyd.
    unfold Hy, Hylin, extension_cont in Hxd, Hyd.
    autorewrite with null in Hxd, Hyd.
    
    destruct Rle_dec.
    ++ unfold θ in *.
       rewrite (calcth1_atan2_s x y) in *.
       unfold Hxarc, Hyarc in *.
       autorewrite with null in *.
       split.
       +++ rewrite Rplus_comm in Hyd.
           rewrite <- (Rmult_1_r r) in Hyd at 1.
           assert (r * 1 + - r * cos (Dr / r) = r * (1 - cos (Dr / r)))
             as id; [ field| rewrite id in *; clear id].
           rewrite <- Hxd, <- Hyd.
           destruct (Rlt_dec 0 r) as [zltr| zger].
           ++++ assert (0 < θr) as zlttr;
                  [apply (Rmult_lt_reg_l r);[assumption|lra]|].
                assert (0 < Dr / r) as zltDrr. {
                  rewrite <- RmultRinv.
                  zltab.
                  destruct Dr.
                  simpl in *.
                  destruct cond_nonneg.
                  assumption.
                  rewrite <- e in *.
                  rewrite <- RmultRinv in *.
                  autorewrite with null in *.
                  exfalso.
                  apply no.
                  split; try auto.
                  rewrite <- Hyd.
                  field.
                }
                assert (Dr / r < 2 * PI) as Drrlt2pi. {
                  apply (Rmult_lt_reg_r (Rabs r));
                    [rewrite Rabs_right; lra|
                     rewrite Rabs_right at 1; try lra].
                  rewrite (Rmult_comm _ (Rabs r)).
                  rewrite <- Rmult_assoc.
                  setl Dr; try lra. }
                rewrite chord_property; try lra.
                repeat rewrite Rabs_right; try lra.
                apply (Rmult_le_reg_r r); try lra.
                setl (Dr). lra.
                lra.
           ++++ apply Rnot_lt_le in zger.
                destruct zger as [rlt0|]; [|lra].
                assert (θr < 0) as zlttr;
                  [apply (Rmult_lt_reg_l (-r)); lra|].
                assert (Dr / r < 0) as zltDrr. {
                  rewrite <- RmultRinv.
                  setl (- (Dr * / (-r))). lra.
                  setr (-0).
                  apply Ropp_lt_contravar.
                  zltab.
                  destruct Dr.
                  simpl in *.
                  destruct cond_nonneg.
                  assumption.
                  rewrite <- e in *.
                  rewrite <- RmultRinv in *.
                  autorewrite with null in *.
                  exfalso.
                  apply no.
                  split; try auto.
                  rewrite <- Hyd.
                  field.
                  lra. }
                
                assert (- 2 * PI < Dr / r) as Drrlt2pi. {
                  apply (Rmult_lt_reg_r (Rabs r));
                    [rewrite Rabs_left; lra|
                     rewrite Rabs_left at 2; try lra].
                  setl (- (Rabs r * 2 * PI)).
                  setr (- Dr); try lra. }
                rewrite chord_property_neg; try lra.
                repeat rewrite Rabs_left; try lra.
                apply (Rmult_le_reg_r (-r)); try lra.
                setl (Dr). lra.
                lra.
       +++ apply (Rmult_lt_reg_r (Rabs r)).
           unfold Rabs.
           destruct Rcase_abs; lra.
           rewrite Rmult_comm at 1.
           rewrite <- Rabs_mult.
           rewrite Rabs_right; lra.

    ++ apply Rnot_le_lt in n.
       specialize (ottb_distance_straight
                     _ _ _ _ _ _ _ _ stp P n)
         as phaset.
       unfold turning in phaser.
       unfold straight in phaset.
       lra.
Qed.
(* end hide *)

Lemma ottb_compute_turning_t :
  forall θ₀ x₀ y₀ x₁ y₁ r θr stp Dr
         (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
         (phaser : turning r θ₀ x₀ y₀ x₁ y₁)
         (P : path_segment Dr (Hx r θ₀ x₀ θr stp) (Hy r θ₀ y₀ θr stp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    let θ := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    Rabs θ <= Rabs θr < 2 * PI.
Proof.
  intros.

  unfold θ in *; clear θ.
  rewrite calc_angle_std in *.
  rewrite path_std in P.

  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.

  specialize (notid_rot θ₀ _ _ _ _ no) as not.
  simpl in not.
  change (~ (x = 0 /\ y = 0)) in not.
    
  set (θ := calcθ₁ 0 0 0 x y) in *.

  apply turning_rot in phaser.
  change (turning r 0 0 0 x y) in phaser.
  eapply ottb_compute_turning_t_s; try eassumption.
Qed.

Lemma ottb_compute_straight_t :
  forall θ₀ x₀ y₀ x₁ y₁ r θr stp Dr
         (phaser : straight r θ₀ x₀ y₀ x₁ y₁)
         (P : path_segment Dr (Hx r θ₀ x₀ θr stp) (Hy r θ₀ y₀ θr stp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    let x := (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ in
    let y := - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ in
    θr = θ1 x y r.
Proof.
  intros.
  addzner.

  apply path_std in P; try assumption.
  change (path_segment Dr (Hx r 0 0 θr stp) (Hy r 0 0 θr stp)
         (mkpt 0 0) (mkpt x y)) in P.
  apply straight_rot in phaser.
  change (straight r 0 0 0 x y) in phaser.
  eapply ottb_compute_straight_t_s;
    try eassumption.
Qed.

Lemma ottb_tinrng :
  forall θ₀ x₀ y₀ x₁ y₁ r θr stp Dr
         (phaser : straight r θ₀ x₀ y₀ x₁ y₁)
         (P : path_segment Dr (Hx r θ₀ x₀ θr stp) (Hy r θ₀ y₀ θr stp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    (0 < θmax /\ (θmax/2 < θr < θmax \/ - 2*PI < θr < θmax/2 - 2*PI)) \/
    (θmax < 0 /\ (θmax < θr < θmax/2 \/ θmax/2 + 2*PI < θr < 2*PI)).
Proof.
  intros.
  specialize (ottb_compute_straight_t
                _ _ _ _ _ _ _ stp _ phaser P) as treqtm.
  simpl in *.
  clear P.
  rewrite treqtm in *.
  
  apply tinrng; try assumption.
Qed.


(**
 This justifies equation (15) of the paper.
 Given path segment P, this expression calculates distance traveled. *)
Theorem ottb_path_distance : forall (D:nonnegreal) (x₀ y₀ x₁ y₁ r θ₀ θc:R)
    rtp (P : path_segment D (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp)
                      (mkpt x₀ y₀) (mkpt x₁ y₁)),
    (turning r θ₀ x₀ y₀ x₁ y₁ /\
     nonneg D = r * calcdθ θ₀ x₀ y₀ x₁ y₁ r) \/
    (straight r θ₀ x₀ y₀ x₁ y₁ /\
     nonneg D = r * θc + sqrt ((x₁ - (x₀ - r*sin θ₀ + r*sin(θ₀+θc)))² +
                               (y₁ - (y₀ + r*cos θ₀ - r*cos(θ₀+θc)))²)).
Proof.
  intros.
  
  addzner.
  set (p₀ := {| ptx := x₀; pty := y₀ |}).
  set (p₁ := {| ptx := x₁; pty := y₁ |}).
  inversion P.
  injection bbnd. intros endpty endptx.
  inversion rtp as [zlerth thle2rPI].
  assert (0 <= D) as zleD. destruct D. simpl. assumption.
  generalize (H_len r θ₀ θc x₀ y₀ D zleD (Rlt_le _ _ zlerth) rtp) as paramD; intro.
  generalize (is_RInt_unique _ _ _ _ paramD) as Dval; intro.

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

  destruct (Rle_dec D (r*θc)).
  destruct (Rlt_dec D (Rabs r *PI)).
  + left.
    split.
    ++ assert (0 <= r * θc < 2 * Rabs r * PI) as rtcorder.
       split; [left; assumption| lra].
       assert (0 <= nonneg D <= r * θc) as Dorder. split; assumption.
       apply (ottb_distance_turning D x₀ y₀ x₁ y₁ r θ₀ θc rtp P Dorder).

    ++ (* main result for turning D *)
      inversion zleD as [zeqD | zltD].
      
      (* make it look like this:
       2 *asin (TI_map (1/(2*r) * sqrt ((x₁ - x₀)² + (y₁ - y₀)²))) *)
      unfold calcdθ.
      assert (0 <= nonneg D <= r * θc) as Dorder;[ split; assumption|].
      assert (0 < nonneg D < Rabs r * PI) as DltrPI;[ split; assumption|].

      rewrite (Rmult_comm _ 2) in thle2rPI.
      generalize (ottb_turning_le180 D x₀ y₀ x₁ y₁ r θ₀ θc
                                     rtp (conj (Rlt_le _ _ zlerth) thle2rPI)
                                     P Dorder DltrPI)
        as ltPI. intro.
      destruct (Rlt_dec 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)).

      +++ assert (0 <= nonneg D <= r * θc) as Drtcrel; [ split; assumption|].
          assert (0 <= nonneg D <= Rabs r * PI) as DrPIrel;
            [split; [assumption|left; assumption]| ].
          generalize (H_len_0_3 r θ₀ θc x₀ y₀ D Drtcrel DrPIrel rtp) as Dcomp; intro.
          generalize (is_RInt_unique _ _ _ _ Dcomp) as Dcompval; intro.
          rewrite Dval in Dcompval.
          rewrite <- endpty. rewrite <- endptx.
          fieldrewrite (sqrt ((Hx r θ₀ x₀ θc rtp (nonneg D) - x₀)² +
                              (Hy r θ₀ y₀ θc rtp (nonneg D) - y₀)²) /
                             (2 * r))
                       (1 / (2 * r) *
                        sqrt
                          ((Hx r θ₀ x₀ θc rtp (nonneg D) - x₀)² +
                           (Hy r θ₀ y₀ θc rtp (nonneg D) - y₀)²)).
          auto.

          rewrite <- Rmult_assoc.
          assumption.

    +++ exfalso. apply n. assumption.
    (**********)
        
    +++ unfold calcdθ.
    injection abnd. intros bpty bptx.
    rewrite <- bpty, <- bptx, <- endpty, <- endptx.
    unfold Hx, Hy, extension_cont, Hxarc, Hyarc.
    destruct (Rle_dec 0 (r*θc)).
    destruct (Rle_dec D (r*θc)).
    rewrite <- zltD.
    assert (0 = 
            ((r * sin (0 / r + θ₀) - r * sin θ₀ + x₀ -
             (r * sin (0 / r + θ₀) - r * sin θ₀ + x₀)) * cos θ₀ +
             (- r * cos (0 / r + θ₀) + r * cos θ₀ + y₀ -
             (- r * cos (0 / r + θ₀) + r * cos θ₀ + y₀)) * sin θ₀))
      as zeroid.
    field.
    rewrite <- zeroid. clear.
    destruct (Rlt_dec 0 0).
    exfalso. lra.
    destruct (Rgt_dec 0 0).
    exfalso. lra.
    destruct (Req_EM_T (- r * cos (0 / r + θ₀) + r * cos θ₀ + y₀)
                       (- r * cos (0 / r + θ₀) + r * cos θ₀ + y₀)).
    destruct (Req_EM_T (r * sin (0 / r + θ₀) - r * sin θ₀ + x₀)
                       (r * sin (0 / r + θ₀) - r * sin θ₀ + x₀)).
    field.
    exfalso. apply n1. reflexivity.
    exfalso. apply n1. reflexivity.
    exfalso. apply n; assumption.
    exfalso. apply n. left; assumption.

  
  + apply Rnot_lt_ge in n.
    left.
    split.
    assert (0 <= r * θc < 2 * Rabs r * PI) as rtcorder.
    split; [left; assumption| lra].
    assert (0 <= nonneg D <= r * θc) as Dorder. split; assumption.
    apply (ottb_distance_turning D x₀ y₀ x₁ y₁ r θ₀ θc rtp P Dorder).
    
    apply Rge_le in n. inversion_clear n.
    assert (Rabs r * PI < D < 2 * Rabs r * PI) as Drange.
    split; try assumption.
    lra.

    (* make it look like this: 
       Rabs r * PI +
       r*2*asin (TI_map (1/(2*r) * sqrt ((x₁ - (x₀ - 2*r*sin θ₀))² +
                                         (y₁ - (y₀ + 2*r*cos θ₀))²))) *)
  
    unfold calcdθ.
    assert (0 <= D <= r * θc) as Dorder. split; assumption.
    rewrite (Rmult_comm _ 2) in thle2rPI.
    generalize (ottb_turning_gt180 D x₀ y₀ x₁ y₁ r θ₀ θc
                                   rtp (conj (Rlt_le _ _ zlerth) thle2rPI)
                                   P Dorder Drange) as 
        gtPI. intro.
    destruct (Rlt_dec 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)).
    exfalso. generalize r1. lra.
    clear n.
    destruct (Rgt_dec 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)).
    clear r1.
  
    assert (0 <= nonneg D <= r * θc) as Drtcrel. split; assumption.
    assert (Rabs r * PI <= nonneg D <= 2* Rabs r * PI) as DrPIrel. split.
    apply Rge_le. left. assumption.
    lra. 
    generalize (H_len_0_5 r θ₀ θc x₀ y₀ D Drtcrel  DrPIrel rtp) as Dcomp; intro.
    generalize (is_RInt_unique _ _ _ _ Dcomp) as Dcompval; intro.
    rewrite Dval in Dcompval.
    rewrite <- endpty. rewrite <- endptx.

    assert ((x₀ - 2 * r * sin θ₀) = Hx r θ₀ x₀ θc rtp (Rabs r * PI)).
    unfold Hx, extension_cont.
    destruct (Rle_dec (Rabs r * PI) (r * θc)).
    unfold Hxarc.

    destruct (Rle_dec 0 r).
    rewrite Rabs_pos_eq; try assumption.
    fieldrewrite (r * PI / r + θ₀) (θ₀ + PI).
    intro; subst; apply zner; reflexivity.
    rewrite neg_sin. field.

    apply Rnot_le_lt in n.
    rewrite Rabs_left; try assumption.
    fieldrewrite (- r * PI / r + θ₀) (- (- θ₀ + PI)).
    intro; subst; apply zner; reflexivity.
    rewrite sin_neg.
    rewrite neg_sin.
    rewrite sin_neg.
    field.

    exfalso.
    apply n.
    apply (Rle_trans _ D); try assumption.
    apply Rge_le. left. assumption.
    rewrite H0. clear H0.
    
    assert ((y₀ + 2 * r * cos θ₀) = Hy r θ₀ y₀ θc rtp (Rabs r * PI)).
    unfold Hy, extension_cont.
    destruct (Rle_dec (Rabs r * PI) (r * θc)).
    unfold Hyarc.

    destruct (Rle_dec 0 r).
    rewrite Rabs_pos_eq; try assumption.
    fieldrewrite (r * PI / r + θ₀) (θ₀ + PI).
    intro; subst; apply zner; reflexivity.
    rewrite neg_cos. field.

    apply Rnot_le_lt in n.
    rewrite Rabs_left; try assumption.
    fieldrewrite (- r * PI / r + θ₀) (- (- θ₀ + PI)).
    intro; subst; apply zner; reflexivity.
    rewrite cos_neg.
    rewrite neg_cos.
    rewrite cos_neg.
    field.

    exfalso.
    apply n.
    apply (Rle_trans _ D); try assumption.
    apply Rge_le. left. assumption.
    rewrite H0. clear H0.
    
    fieldrewrite (sqrt
                    ((Hx r θ₀ x₀ θc rtp (nonneg D) - Hx r θ₀ x₀ θc rtp (Rabs r * PI))² +
                     (Hy r θ₀ y₀ θc rtp (nonneg D) - Hy r θ₀ y₀ θc rtp (Rabs r * PI))²) / 
                    (2 * r))
                 (1 / (2 * r) *
                  sqrt
                    ((Hx r θ₀ x₀ θc rtp (nonneg D) - Hx r θ₀ x₀ θc rtp (Rabs r * PI))² +
                     (Hy r θ₀ y₀ θc rtp (nonneg D) - Hy r θ₀ y₀ θc rtp (Rabs r * PI))²)).
    auto.
    rewrite Rmult_plus_distr_l.
    fieldrewrite (r * (Rabs r / r * PI)) (Rabs r * PI). auto.
    rewrite <- Rmult_assoc.
    assumption.
    exfalso. apply n. assumption.

    unfold calcdθ.
    injection abnd. intros bpty bptx.
  
    assert (((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) = 0) as midline.
    rewrite <- bpty, <- bptx, <- endpty, <- endptx.
    rewrite <- H.
    unfold Hx, Hy, extension_cont, Hyarc, Hxarc.
    destruct (Rle_dec (Rabs r *PI) (r * θc)).
    destruct (Rle_dec 0 (r * θc)).
    fieldrewrite (0 / r + θ₀) (θ₀). auto.
    fieldrewrite ((r * sin (Rabs r * PI / r + θ₀) - r * sin θ₀ + x₀ -
                  (r * sin θ₀ - r * sin θ₀ + x₀)) * cos θ₀ +
                  (- r * cos (Rabs r * PI / r + θ₀) + r * cos θ₀ + y₀ -
                  (- r * cos θ₀ + r * cos θ₀ + y₀)) * sin θ₀)
                 (r * (sin (Rabs r * PI / r + θ₀) * cos θ₀ 
                       -  cos (Rabs r * PI / r + θ₀)  * sin θ₀)).
    rewrite <- sin_minus.
    fieldrewrite (Rabs r * PI / r + θ₀ - θ₀) (Rabs r * PI / r). auto.
    assert ((r * sin (Rabs r * PI / r)) = 0).
    destruct (Rle_dec 0 r). inversion r3.
    rewrite Rabs_pos_eq.
    fieldrewrite (r * PI / r) PI. auto.
    rewrite sin_PI. field. assumption.
    exfalso. auto.
    apply Rnot_le_lt in n.
    rewrite Rabs_left.
    fieldrewrite (- r * PI / r) (- PI). auto.
    rewrite sin_neg. rewrite sin_PI. field. assumption.
    rewrite H0. reflexivity.
    exfalso. apply n. left; assumption.
    exfalso. apply n. lra.


    rewrite midline.
    destruct (Rlt_dec 0 0).
    exfalso. lra.
    destruct (Rgt_dec 0 0).
    exfalso. lra.
    clear n n0.

    destruct (Req_EM_T y₀ y₁) as [yeq | yneq].
    destruct (Req_EM_T x₀ x₁) as [xeq | xneq].

    exfalso.
    apply (Rplus_eq_compat_l (-x₀)) in xeq.
    apply (Rplus_eq_compat_l (-y₀)) in yeq.
    generalize yeq xeq. clear yeq xeq.
    fieldrewrite (- y₀ + y₀) 0.
    fieldrewrite (- x₀ + x₀) 0.
    rewrite <- bpty, <- bptx, <- endpty, <- endptx, <- H.
    unfold Hx, Hy, extension_cont.
    destruct (Rle_dec 0 (r * θc)); try (exfalso; apply n; assumption).
    destruct (Rle_dec (Rabs r * PI) (r * θc)); try (exfalso; apply n; rewrite H; assumption).
    unfold Hxarc, Hyarc.

    fieldrewrite (- (- r * cos (0 / r + θ₀) + r * cos θ₀ + y₀) +
                  (- r * cos (Rabs r * PI / r + θ₀) + r * cos θ₀ + y₀))
                 (r * (cos (0 / r + θ₀) + - cos (Rabs r * PI / r + θ₀))).
    fieldrewrite (- (r * sin (0 / r + θ₀) - r * sin θ₀ + x₀) +
                  (r * sin (Rabs r * PI / r + θ₀) - r * sin θ₀ + x₀))
                 (r * (- sin (0 / r + θ₀) + sin (Rabs r * PI / r + θ₀))).
    fieldrewrite (0 / r + θ₀) (θ₀). auto.
    intros.
    apply path_cos_id in yeq; auto.
    apply path_sin_id in xeq; auto.
    symmetry in xeq,yeq.
    generalize (sin_eq_0_0 _ xeq) as cyclesin. intro.
    generalize (cos_eq_0_0 _ yeq) as cyclecos. intro.
    inversion_clear cyclesin as [v tdefv]. inversion_clear cyclecos as [w tdefw].
    rewrite tdefv in tdefw. clear tdefv.
    assert (IZR w * PI + PI / 2 =  (IZR w  + / 2) * PI) as Zid. field.
    rewrite Zid in tdefw. clear Zid.
    generalize PI_RGT_0 as PI_RGT_0. intro.
    apply (Rmult_eq_reg_r PI) in tdefw; [|intro PIeq0; rewrite PIeq0 in PI_RGT_0; lra].
    assert (IZR v - IZR w = /2) as izrfrac. rewrite tdefw. field. clear tdefw.
    rewrite Z_R_minus in izrfrac.
    set (q := Zminus v w).
    change (IZR q = / 2) in izrfrac.

    assert (IZR q * 2 = 1).
    fieldrewrite 1 (/ 2 * 2).
    apply (Rmult_eq_compat_r 2). assumption.
    generalize H0. clear H0.
    change (IZR q * 2 <> 1).
    discrR.
    omega.
    lra.
    rewrite <- H. field. auto.
    rewrite <- H. field. auto.

  + right.
    apply Rnot_le_lt in n.
    split.
    assert (0 <= r * θc < 2 * Rabs r * PI) as rtcorder.
    split; [left; assumption|lra].
    assert (r * θc < nonneg D) as Dorder. assumption.
    apply (ottb_distance_straight D x₀ y₀ x₁ y₁ r θ₀ θc rtp P Dorder).
    
    assert (0 <= r * θc < nonneg D) as Drtcrel.
    split; [left|];assumption.
    generalize (H_len_d_1 r θ₀ θc x₀ y₀ D Drtcrel rtp) as Dcomp; intro.
    generalize (is_RInt_unique _ _ _ _ Dcomp) as Dcompval; intro.
    rewrite Dval in Dcompval.
    rewrite <- endpty. rewrite <- endptx.

    assert ((x₀ - r * sin θ₀ + r * sin (θ₀ + θc)) = Hx r θ₀ x₀ θc rtp (r * θc)).
    unfold Hx, extension_cont.
    destruct (Rle_dec (r * θc) (r * θc));
      [| exfalso; apply Rnot_le_lt in n0; lra].
    unfold Hxarc.

    fieldrewrite (r * θc / r + θ₀) (θ₀ + θc).
    intro; subst; apply zner; reflexivity.
    field. rewrite H. clear H.

    assert ((y₀ + r * cos θ₀ - r * cos (θ₀ + θc)) = Hy r θ₀ y₀ θc rtp (r * θc)).
    unfold Hy, extension_cont.
    destruct (Rle_dec (r * θc) (r * θc));
      [|exfalso; apply Rnot_le_lt in n0; lra].
    unfold Hyarc.

    fieldrewrite (r * θc / r + θ₀) (θ₀ + θc).
    intro; subst; apply zner; reflexivity.
    field. rewrite H. clear H.
    assumption.
Qed.

Lemma ottb_unique_D :
  forall θ₀ x₀ y₀ x₁ y₁ r θr Dr Ds stp 
         (P : path_segment Dr (Hx r θ₀ x₀ θr stp) (Hy r θ₀ y₀ θr stp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁))
         (S : path_segment Ds (Hx r θ₀ x₀ θr stp) (Hy r θ₀ y₀ θr stp)
                           (mkpt x₀ y₀) (mkpt x₁ y₁)),
    nonneg Dr = nonneg Ds.
Proof.
  intros.
  
  apply ottb_path_distance in P;
  apply ottb_path_distance in S.

  destruct S as [[sst dsd] |[str dsd]];
    destruct P as [[pst dpd] |[ptr dpd]].

  + rewrite dpd, dsd.
    reflexivity.
  + unfold straight, turning, Tcx, Tcy in *.
    rewrite sst in ptr.
    lra.
  + unfold straight, turning, Tcx, Tcy in *.
    rewrite pst in str.
    lra.
  + rewrite dpd, dsd.
    reflexivity.
Qed.

