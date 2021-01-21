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
Require Import tlens.
Require Import incr_function_le_ep.


Import Lra.
Open Scope R_scope.
Set Bullet Behavior "Strict Subproofs".
Lemma ottb_bigger_theta_bigger_r_ep_std :
  forall x₁ y₁ θr θs,
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (nx : ~ (y₁ = 0))
           (trrng : θmax / 2 <= θr <= θmax)
           (tsrng : θmax / 2 <= θs <= θmax),
      let r := (x₁ * sin θr - y₁ * cos θr)
                 / (1 - cos θr) in
      let s := (x₁ * sin θs - y₁ * cos θs)
                 / (1 - cos θs) in
      forall (tp : 0 < θr)
             (to : θr < θs)
             (tu : θs < 2 * PI),
        r < s.
Proof.
  intros.
  unfold r, s.

  assert (~ (x₁ = 0 /\ y₁ = 0)) as nO; try lra.
           
  assert (θmax <> 2*PI) as tmne2pi. {
    unfold θmax.
    rewrite calcth1_atan2_s.
    intro at22pi.
    assert (atan2 y₁ x₁ = PI) as at2pi. {
      apply (Rmult_eq_reg_l 2); try discrR.
      assumption. }
    apply (atan2_PI_impl _ _ nO) in at2pi as [xlt0  yeq0].
    apply nx.
    assumption. }
  
  assert (θs <> 0) as tsne0. lra.
  assert (cos θs <> 1) as ctne1. {
    intro.
    apply cosθeq1 in H.
    lra.
    split; lra. }

  assert (0 < 1 - cos θs) as omcsgt0. {
    apply (Rplus_lt_reg_r (cos θs)).
    setr 1.
    arn.
    specialize (COS_bound θs) as [cbl cbu].
    destruct cbu as [cblt | cbe].
    assumption.
    exfalso.
    apply ctne1.
    assumption. }

  
  assert (θr <> 0) as trne0. lra.
  assert (cos θr <> 1) as ctrne1. {
    intro.
    apply cosθeq1 in H.
    lra.
    split; lra. }

  assert (0 < 1 - cos θr) as omcrgt0. {
    apply (Rplus_lt_reg_r (cos θr)).
    setr 1.
    arn.
    specialize (COS_bound θr) as [cbl cbu].
    destruct cbu as [cblt | cbe].
    assumption.
    exfalso.
    apply ctrne1.
    assumption. }

  specialize (r_std_deriv_pos x₁ y₁ nO) as dp.
  change (forall θ : R,
             θmax / 2 < θ < θmax ->
             0 < Derive (fun θ0 : R => (x₁ * sin θ0 - y₁ * cos θ0)
                                         / (1 - cos θ0)) θ)
    in dp.
  set (f := (fun θ : R => (x₁ * sin θ - y₁ * cos θ)
                            / (1 - cos θ))) in *.
  change (f θr < f θs).
  specialize (atan2_bound _ _ nO) as [apl apu].
  assert (θmax < 2*PI) as tm. {
    unfold θmax.
    rewrite calcth1_atan2_s.
    destruct apu as [at2lt |at2eq].
    lra.
    exfalso.
    apply tmne2pi.
    unfold θmax.
    rewrite calcth1_atan2_s.
    rewrite at2eq.
    reflexivity. }
  
  destruct (Rge_dec 0 θmax) as [zgetm | zlttm];
    [exfalso; lra|apply Rnot_ge_lt in zlttm].

  eapply (incr_function_le_ep) with (a:=θmax / 2) (b:=θmax); try assumption.
  + intros.
    apply r_std_deriv.
    simpl in H, H0.
    intro.
    apply cosθeq1 in H1;
    lra.
    
  + intros.
    simpl in H, H0.
    set (f' := (fun x0 : R =>
                  (x₁ * cos x0 + y₁ * sin x0)
                    / (1 + - cos x0)
                  - (x₁ * sin x0 - y₁ * cos x0) *
                    sin x0 / (1 - cos x0)²)) in *.
    assert (cos x <> 1) as cxne1. {
      intro cxeq1.
      apply cosθeq1 in cxeq1;
      lra. }
    specialize (r_std_deriv x₁ y₁ x cxne1) as rsd.
    change (is_derive f x (f' x)) in rsd.
    apply is_derive_unique in rsd.
    rewrite <- rsd.
    apply Rlt_gt.

    apply r_std_deriv_pos; try assumption.
    change (θmax / 2 < x < θmax).
    split; lra.
    
  + destruct trrng.
    assumption.

  + destruct tsrng.
    assumption.
Qed.

Lemma ottb_bigger_theta_bigger_r_std :
  forall x₁ y₁ θr θs,
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (nO : ~ (x₁ = 0 /\ y₁ = 0))
           (trrng : θmax / 2 < θr < θmax)
           (tsrng : θmax / 2 < θs < θmax),
      let r := (x₁ * sin θr - y₁ * cos θr)
                 / (1 - cos θr) in
      let s := (x₁ * sin θs - y₁ * cos θs)
                 / (1 - cos θs) in
      forall (tp : 0 < θr)
             (to : θr < θs)
             (tu : θs < 2 * PI),
        r < s.
Proof.
  intros.
  unfold r, s.
  assert (θs <> 0) as tsne0. lra.
  assert (cos θs <> 1) as ctne1. {
    intro.
    apply cosθeq1 in H.
    lra.
    split; lra. }

  assert (0 < 1 - cos θs) as omcsgt0. {
    apply (Rplus_lt_reg_r (cos θs)).
    setr 1.
    arn.
    specialize (COS_bound θs) as [cbl cbu].
    destruct cbu as [cblt | cbe].
    assumption.
    exfalso.
    apply ctne1.
    assumption. }

  
  assert (θr <> 0) as trne0. lra.
  assert (cos θr <> 1) as ctrne1. {
    intro.
    apply cosθeq1 in H.
    lra.
    split; lra. }

  assert (0 < 1 - cos θr) as omcrgt0. {
    apply (Rplus_lt_reg_r (cos θr)).
    setr 1.
    arn.
    specialize (COS_bound θr) as [cbl cbu].
    destruct cbu as [cblt | cbe].
    assumption.
    exfalso.
    apply ctrne1.
    assumption. }

  specialize (r_std_deriv_pos x₁ y₁ nO) as dp.
  change (forall θ : R,
             θmax / 2 < θ < θmax ->
             0 < Derive (fun θ0 : R => (x₁ * sin θ0 - y₁ * cos θ0)
                                         / (1 - cos θ0)) θ)
    in dp.
  set (f := (fun θ : R => (x₁ * sin θ - y₁ * cos θ)
                            / (1 - cos θ))) in *.
  change (f θr < f θs).

  eapply (incr_function_le f θr θs); try (simpl; lra).
  intros.

  apply r_std_deriv.
  simpl in H, H0.
  intro.
  apply cosθeq1 in H1.
  lra.
  split; lra.
  intros.
  simpl in H, H0.
  set (f' := (fun x0 : R =>
                (x₁ * cos x0 + y₁ * sin x0)
                  / (1 + - cos x0)
                - (x₁ * sin x0 - y₁ * cos x0) *
                  sin x0 / (1 - cos x0)²)) in *.
  assert (cos x <> 1) as cxne1. {
    intro cxeq1.
    apply cosθeq1 in cxeq1.
    lra. lra. }
  specialize (r_std_deriv x₁ y₁ x cxne1) as rsd.
  change (is_derive f x (f' x)) in rsd.
  apply is_derive_unique in rsd.
  rewrite <- rsd.
  apply Rlt_gt.

  apply r_std_deriv_pos; try assumption.
  change (θmax / 2 < x < θmax).
  split; lra.
Qed.

Lemma ottb_bigger_theta_bigger_r2_std :
  forall x₁ y₁ θr θs,
    let θmax := calcθ₁ 0 0 0 x₁ y₁ in
    forall (nO : ~ (x₁ = 0 /\ y₁ = 0))
           (trrng : θmax / 2 + 2 * PI < θr < 2 * PI)
           (tsrng : θmax / 2 + 2 * PI < θs < 2 * PI),
      let r := (x₁ * sin θr - y₁ * cos θr)
                 / (1 - cos θr) in
      let s := (x₁ * sin θs - y₁ * cos θs)
                 / (1 - cos θs) in
      forall (tp : 0 < θr)
             (to : θr < θs)
             (tu : θs < 2 * PI),
        r < s.
Proof.
  intros.
  unfold r, s.
  assert (θs <> 0) as tsne0. lra.
  assert (cos θs <> 1) as ctne1. {
    intro.
    apply cosθeq1 in H.
    lra.
    split; lra. }

  assert (0 < 1 - cos θs) as omcsgt0. {
    apply (Rplus_lt_reg_r (cos θs)).
    setr 1.
    arn.
    specialize (COS_bound θs) as [cbl cbu].
    destruct cbu as [cblt | cbe].
    assumption.
    exfalso.
    apply ctne1.
    assumption. }

  
  assert (θr <> 0) as trne0 by lra.
  assert (cos θr <> 1) as ctrne1. {
    intro.
    apply cosθeq1 in H.
    lra.
    split; lra. }

  assert (0 < 1 - cos θr) as omcrgt0. {
    apply (Rplus_lt_reg_r (cos θr)).
    setr 1.
    arn.
    specialize (COS_bound θr) as [cbl cbu].
    destruct cbu as [cblt | cbe].
    assumption.
    exfalso.
    apply ctrne1.
    assumption. }


  specialize (r_std_deriv_pos x₁ y₁ nO) as dp.
  change (forall θ : R,
             θmax / 2 < θ < θmax ->
             0 < Derive (fun θ0 : R => (x₁ * sin θ0 - y₁ * cos θ0)
                                         / (1 - cos θ0)) θ)
    in dp.
  set (f := (fun θ : R => (x₁ * sin θ - y₁ * cos θ)
                            / (1 - cos θ))) in *.
  change (f θr < f θs).
  
  eapply (incr_function_le f θr θs); try (simpl; lra).
  intros.
  apply r_std_deriv.
  simpl in H, H0.
  intro.
  apply cosθeq1 in H1.
  lra.
  split; lra.
  intros.
  simpl in H, H0.
  set (f' := (fun x0 : R =>
                (x₁ * cos x0 + y₁ * sin x0)
                  / (1 + - cos x0)
                - (x₁ * sin x0 - y₁ * cos x0) *
                  sin x0 / (1 - cos x0)²)) in *.
  assert (cos x <> 1) as cxne1. {
    intro cxeq1.
    apply cosθeq1 in cxeq1.
    lra. lra. }
  specialize (r_std_deriv x₁ y₁ x cxne1) as rsd.
  change (is_derive f x (f' x)) in rsd.
  apply is_derive_unique in rsd.
  rewrite <- rsd.
  apply Rlt_gt.
  apply r_std_deriv_pos2; try assumption.
  change (θmax / 2 + 2 * PI < x < 2 * PI).
  split; lra.
Qed.

Lemma full_path_dist_increasing_s :
  forall (x y r s : R)
         (not_forward : (~ (0 <= x /\ y = 0)))
         (phase : straight s 0 0 0 x y)
         (rgt0 : 0 < r)
         (sgtr : r < s),
    let d := (fun t => t * (θ1 x y) t +
                       (sqrt ((x - t * sin (θ1 x y t))² +
                              (y - t * (1 - cos (θ1 x y t)))²))) in
    d r < d s.
Proof.
  intros.

  apply straightcond in phase.
  assert (forall (t : R), Rbar_lt 0 t ->
                          Rbar_lt t (if (Rlt_le_dec 0 y)
                                     then /(2 * y)*(x² + y²)
                                     else p_infty)
                          ->
                          ex_derive (θ1 x y) t) as t1pe.
  { intros.
    apply theta1_ex_derive_posr; auto.
    apply condstraight.
    destruct (Rlt_le_dec 0 y) as [P1 | P2].
    - simpl in H0.
      apply (Rmult_lt_reg_r (/(2 * y)));[apply Rinv_0_lt_compat; lra|].
      setl t; lra.
    - simpl in H.
      destruct P2.
      + apply Rlt_trans with (r2 := 0).
        -- apply Ropp_lt_cancel; rewrite Ropp_0; setr (2 * t * (- y)).
           repeat apply Rmult_lt_0_compat; lra.
        -- apply Rplus_le_lt_0_compat; [apply Rle_0_sqr|apply Rsqr_pos_lt; lra].
      + rewrite H1, Rmult_0_r, Rsqr_0, Rplus_0_r; apply Rsqr_pos_lt.
        intro.
        rewrite H1, H2 in not_forward; apply not_forward; split; lra.
  }
      
  set (d' := (fun t => (((θ1 x y t) - sin (θ1 x y t))))).
  set (ub := if (Rlt_le_dec 0 y) then (Finite (/(2 * y)*(x² + y²))) else p_infty) in *.
  assert (forall x : R,
             Rbar_lt 0 x -> Rbar_lt x ub -> is_derive d x (d' x)).
  { intros.
    assert (straight x0 0 0 0 x y) as P1.
    { apply condstraight.
      simpl in H0, H.
      destruct (Rlt_le_dec 0 y).
      - unfold ub in H0.
        setl ((2 * y) * x0).
        eapply Rmult_lt_compat_l with (r := 2 * y) in H0; [|lra].
        + rewrite <- Rmult_assoc, <- Rinv_r_sym in H0; lra.
      - destruct (Rle_lt_or_eq_dec _ _ r0) as [ylt | yeq].
        + specialize (Rplus_le_le_0_compat x² y² (Rle_0_sqr _)
                                           (Rle_0_sqr _)) as P1.
          eapply Rlt_le_trans with (r2 := 0); auto.
          specialize (Rmult_lt_compat_l _ _ _ H ylt) as P2.
          rewrite Rmult_0_r in P2.
          lra.
        + rewrite yeq, Rmult_0_r in *; assumption.
    }
    destruct Rlt_le_dec; unfold ub in *.
    + simpl in H; eapply full_path_dist_is_derive_s; auto.
    + eapply full_path_dist_is_derive_s; auto.      
  }
  eapply incr_function; eauto.
  + intros.
    apply Rlt_gt, x_minus_sin_x_pos.
    assert (x0 <> 0) as Q1.
    { simpl in H0; lra. }
    assert (straight x0 0 0 0 x y) as Q2.
    { apply condstraight.
      simpl in H0, H.
      destruct (Rlt_le_dec 0 y).
      - unfold ub in H1.
        setl ((2 * y) * x0).
        eapply Rmult_lt_compat_l with (r := 2 * y) in H1; [|lra].
        + rewrite <- Rmult_assoc, <- Rinv_r_sym in H1; lra.
      - destruct (Rle_lt_or_eq_dec _ _ r0) as [ylt | yeq].
        + specialize (Rplus_le_le_0_compat x² y² (Rle_0_sqr _)
                                           (Rle_0_sqr _)) as P1.
          eapply Rlt_le_trans with (r2 := 0); auto.
          specialize (Rmult_lt_compat_l _ _ _ H0 ylt) as P2.
          rewrite Rmult_0_r in P2.
          lra.
        + rewrite yeq, Rmult_0_r in *; assumption.
    }
    apply straightcond in Q2.
    specialize (ottb_r_thetac_lb2_s x y x0 not_forward Q1 Q2) as Q3.
    simpl in *.
    apply (Rmult_lt_reg_l _ _ _ H0); lra.
  + destruct Rlt_le_dec; unfold ub.
    ++ simpl.
       rewrite Rmult_assoc in phase.
       apply (Rmult_lt_reg_l (2 * y)); [lra |].
       rewrite <- Rmult_assoc, <- Rinv_r_sym; lra.
    ++ simpl; auto.
Qed.

Lemma theta1_pos_cond :
  forall x y r
         (zlty : 0 < y)
         (zltr : 0 < r)
         (rltlz : r < (x² + y²) / (2 * y)),
    0 < θ1 x y r.
Proof.
  intros.
  assert (straight r 0 0 0 x y) as phas. {
    apply condstraight.
    apply (Rmult_lt_reg_r (/ (2 * y))).
    zltab.
    lrag rltlz. }
  assert (r <> 0) as rne0; try lra.
  specialize (theta1_rsgn_lim _ _ _ rne0 phas) as [rgt rlt].
  specialize (rgt zltr).
  destruct rgt as [lt |eq]; try assumption.
  exfalso.
  symmetry in eq.
  clear - zltr zlty eq rltlz.
  unfold θ1 in eq.
  destruct (total_order_T 0 r); [destruct s|]; try lra.
  destruct (total_order_T 0 y); [destruct s|]; try lra.
  destruct (total_order_T); [destruct s|].
  destruct (total_order_T); [destruct s|].
  (* Q1o *)
  { rewrite <- (Rmult_0_r 2) in eq.
    apply (Rmult_eq_reg_l 2) in eq; try lra.
    apply (f_equal tan) in eq.
    rewrite atan_right_inv, tan_0 in eq.
    assert ((x - sqrt (x² - (2 * r - y) * y)) = 0) as s1. {
      apply (Rmult_eq_reg_r (/ (2 * r - y))); try lra.
      zltab. }
    apply Rminus_diag_uniq in s1.
    apply (f_equal Rsqr) in s1.
    assert (0 < (x² - (2 * r - y) * y)) as sqp. {
      apply (Rplus_lt_reg_r (2 * y * r)).
      apply (Rmult_lt_reg_r (/ (2 * y))).
      zltab.
      lrag rltlz. }
    rewrite Rsqr_sqrt in s1.
    assert ((0 = (2 * r - y) * y)) as s2. {
      apply (Rmult_eq_reg_r (-1)).
      apply (Rplus_eq_reg_r (x²)).
      lrag s1.
      discrR. }
    symmetry in s2.
    apply Rmult_integral in s2.
    lra.
    left; assumption. }
  (* Q1a *)
  { rewrite <- (Rmult_0_r 2) in eq.
    apply (Rmult_eq_reg_l 2) in eq; try lra.
    apply (f_equal tan) in eq.
    rewrite atan_right_inv, tan_0 in eq.
    rewrite <- RmultRinv in eq.
    apply Rmult_integral in eq.
    destruct eq; try lra.

    generalize r2; intro r3.
    apply Rinv_0_lt_compat in r3.
    rewrite Rinv_mult_distr in H; try lra. }
  (* Q1t *)
  { rewrite <- (Rmult_0_r 2) in eq.
    apply (Rmult_eq_reg_l 2) in eq; try lra.
    apply (f_equal tan) in eq.
    rewrite atan_right_inv, tan_0 in eq.
    assert ((x - sqrt (x² - (2 * r - y) * y)) = 0) as s1. {
      apply (Rmult_eq_reg_r (/ (2 * r - y))); try lra.
      zltab. }
    apply Rminus_diag_uniq in s1.
    apply (f_equal Rsqr) in s1.
    assert (0 < (x² - (2 * r - y) * y)) as sqp. {
      apply (Rplus_lt_reg_r (2 * y * r)).
      apply (Rmult_lt_reg_r (/ (2 * y))).
      zltab.
      lrag rltlz. }
    rewrite Rsqr_sqrt in s1.
    assert ((0 = (2 * r - y) * y)) as s2. {
      apply (Rmult_eq_reg_r (-1)).
      apply (Rplus_eq_reg_r (x²)).
      lrag s1.
      discrR. }
    symmetry in s2.
    apply Rmult_integral in s2.
    lra.
    left; assumption. }
  destruct (total_order_T); [destruct s|].
  (* pos yaxis o *)
  { rewrite <- (Rmult_0_r 2) in eq.
    apply (Rmult_eq_reg_l 2) in eq; try lra.
    apply (f_equal tan) in eq.
    rewrite atan_right_inv, tan_0 in eq.
    assert ((x - sqrt (x² - (2 * r - y) * y)) = 0) as s1. {
      apply (Rmult_eq_reg_r (/ (2 * r - y))); try lra.
      zltab. }
    apply Rminus_diag_uniq in s1.
    apply (f_equal Rsqr) in s1.
    assert (0 < (x² - (2 * r - y) * y)) as sqp. {
      apply (Rplus_lt_reg_r (2 * y * r)).
      apply (Rmult_lt_reg_r (/ (2 * y))).
      zltab.
      lrag rltlz. }
    rewrite Rsqr_sqrt in s1.
    assert ((0 = (2 * r - y) * y)) as s2. {
      apply (Rmult_eq_reg_r (-1)).
      apply (Rplus_eq_reg_r (x²)).
      lrag s1.
      discrR. }
    symmetry in s2.
    apply Rmult_integral in s2.
    lra.
    left; assumption. }
  specialize PI_RGT_0 as pigt0.
  lra.
  (* pos yaxis t *)
  { rewrite <- (Rmult_0_r 2) in eq.
    apply (Rmult_eq_reg_l 2) in eq; try lra.
    apply (f_equal tan) in eq.
    rewrite atan_right_inv, tan_0 in eq.
    assert ((x - sqrt (x² - (2 * r - y) * y)) = 0) as s1. {
      apply (Rmult_eq_reg_r (/ (2 * r - y))); try lra.
      zltab. }
    apply Rminus_diag_uniq in s1.
    apply (f_equal Rsqr) in s1.
    assert (0 < (x² - (2 * r - y) * y)) as sqp. {
      apply (Rplus_lt_reg_r (2 * y * r)).
      apply (Rmult_lt_reg_r (/ (2 * y))).
      zltab.
      lrag rltlz. }
    rewrite Rsqr_sqrt in s1.
    assert ((0 = (2 * r - y) * y)) as s2. {
      apply (Rmult_eq_reg_r (-1)).
      apply (Rplus_eq_reg_r (x²)).
      lrag s1.
      discrR. }
    symmetry in s2.
    apply Rmult_integral in s2.
    lra.
    left; assumption. }
  destruct (total_order_T); [destruct s|].
  (* Q2o *)
  apply Rplus_opp_r_uniq in eq.
  symmetry in eq.
  assert (atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y)) = - PI)
    as at2. {
    apply (Rmult_eq_reg_r (-2)); try lra. }
  match goal with
  | eq : atan ?arg = _ |- _ =>
    specialize (atan_bound arg) as [atl atu]
  end.
  lra.
  specialize PI_RGT_0 as pigt0.
  lra.
  (* Q2t *)
  { rewrite <- (Rmult_0_r 2) in eq.
    apply (Rmult_eq_reg_l 2) in eq; try lra.
    apply (f_equal tan) in eq.
    rewrite atan_right_inv, tan_0 in eq.
    assert ((x - sqrt (x² - (2 * r - y) * y)) = 0) as s1. {
      apply (Rmult_eq_reg_r (/ (2 * r - y))); try lra.
      zltab. }
    apply Rminus_diag_uniq in s1.
    apply (f_equal Rsqr) in s1.
    assert (0 < (x² - (2 * r - y) * y)) as sqp. {
      apply (Rplus_lt_reg_r (2 * y * r)).
      apply (Rmult_lt_reg_r (/ (2 * y))).
      zltab.
      lrag rltlz. }
    rewrite Rsqr_sqrt in s1.
    assert ((0 = (2 * r - y) * y)) as s2. {
      apply (Rmult_eq_reg_r (-1)).
      apply (Rplus_eq_reg_r (x²)).
      lrag s1.
      discrR. }
    symmetry in s2.
    apply Rmult_integral in s2.
    lra.
    left; assumption. }
Qed.

(* end hide *)

Lemma full_path_dist_increasing_turn_s :
    forall (x y r s : R)
           (nO : ~ (x = 0 /\ y = 0))
         (phase : turning s 0 0 0 x y)
         (rgt0 : 0 < r)
         (sgtr : r < s),
    let d := (fun t => t * (θ1 x y) t +
                       (sqrt ((x - t * sin (θ1 x y t))² +
                              (y - t * (1 - cos (θ1 x y t)))²))) in
    d r < d s.
Proof.
  intros.
  rename s into rz.

  assert (0 < y) as zlty. {
    apply turningcond in phase.
    specialize (posss _ _ nO) as px2.
    rewrite <- phase in px2.
    apply zlt_mult in px2; try assumption.
    zltab. }

  assert (rz = (x² + y²) / (2 * y)) as rzd. {
    apply turningcond in phase.
    apply (Rmult_eq_reg_r (2 * y)); try lra.
    lrag phase. }

  assert (straight r 0 0 0 x y) as phaser. {
    apply condstraight.
    apply (Rmult_lt_reg_r (/ (2 * y))); try zltab.
    setl r; try lra. }
  
  set (θmax := calcθ₁ 0 0 0 x y).

  assert (~ (x - 0 = 0 /\ y - 0 = 0)) as notO; try lra.
  assert (θmax <> 0) as notpx. {
    intros tmeq0.
    unfold θmax, calcθ₁ in tmeq0.
    autorewrite with null in tmeq0.
    assert (atan2 y x = 0) as meq0; try lra.
    apply atan2_0_impl in meq0;
      lra.  }
  assert (θmax <> 2 * PI) as notnx.  {
    intros tmeq0.
    unfold θmax, calcθ₁ in tmeq0.
    autorewrite with null in tmeq0.
    assert (atan2 y x = PI) as meq0; try lra.
    apply atan2_PI_impl in meq0;
      lra.  }

  specialize (tmax_radius_gen _ _ _ _ _ notO notpx notnx) as rzd2.
  autorewrite with null in rzd2.
  rewrite <- rzd in rzd2.
  change (rz = (x * sin θmax - y * cos θmax)
                 / (1 - cos θmax)) in rzd2.
  specialize (t1eqtm_gen _ _ _ _ _ notO notpx notnx) as tmd.
  autorewrite with null in tmd.
  rewrite Rplus_comm in tmd.
  rewrite <- rzd in tmd.
  change (θ1 x y rz = θmax) in tmd.
  rewrite <- tmd in rzd2.
  
  rename d into d1.
  set (d2 := (fun r:R_AbsRing => r * θ1 x y r + sqrt (x² - (2 * r - y) * y))) in *.
  set (d' := (fun ru:R_AbsRing => (θ1 x y ru - sin (θ1 x y ru)))) in *.
  assert (forall (r:R), Rbar_lt 0 r -> Rbar_lt r rz ->
                        is_derive d1 r (d' r)) as dderv. {
    rename r into s.
    intros r zltr rltrz.
    unfold d1, d'.
    apply full_path_dist_is_derive_s; try assumption.
    apply condstraight.
    rewrite rzd in rltrz.
    clear - rltrz zltr zlty.
    simpl in *.
    apply (Rmult_lt_reg_r (/ (2 * y))).
    zltab.
    setl r.
    zltab.
    lra. }
  
  assert (forall r : R, Rbar_lt 0 r -> Rbar_lt r rz -> is_derive d2 r (d' r))
    as dder2. {
    rename r into s.
    intros r zltr rltrz.
    apply (is_derive_ext_loc d1 d2).
    unfold locally, d1, d2.
    
    assert (0 < Rmin (rz - r) (r)) as egt0. {
      unfold Rmin.
      simpl in zltr, rltrz.
      destruct Rle_dec; try assumption.
      apply (Rplus_lt_reg_r r).
      setr rz; try assumption.
      arn.
      assumption. }
    
    set (eps := (mkposreal (_:R) egt0)).
    exists eps.
    intros r0 bar.
    simpl in *.
    assert (straight r0 0 0 0 x y) as rstr. {
      apply condstraight.
      apply (Rmult_lt_reg_r (/ (2 * y))); try zltab.
      setl r0; try lra.
      rewrite RmultRinv.
      rewrite <- rzd.
      unfold ball in bar.
      simpl in bar.
      unfold AbsRing_ball, abs, minus, plus, opp in bar.
      simpl in bar.
      unfold Rmin, Rabs in bar;
        destruct Rle_dec;
        destruct Rcase_abs; lra.  }
    assert (0 < r0) as zltr0. {
      unfold ball, AbsRing_ball in bar.
      simpl in bar, r0.
      unfold AbsRing_ball, minus, plus, opp, abs in bar.
      simpl in bar.
      unfold Rmin, Rabs in bar;
        destruct Rle_dec;
        destruct Rcase_abs; lra. }
    assert (r0 <> 0) as r0ne0; try lra.
    rewrite (Darm_Q_straight_std _ _ _ rstr r0ne0).
    reflexivity.
    apply dderv; try assumption. }
  
  
  assert (forall r : R, Rbar_lt 0 r -> Rbar_lt r rz -> d' r > 0)
    as pder. {
    rename r into s.
    intros r zltr rltlz.
    unfold d'.
    apply Rlt_gt.
    simpl in zltr, rltlz.
    rewrite rzd in rltlz.

    assert (r <> 0) as rne0; try lra.
    assert (~ (r < 0 /\ θmax = 2 * PI)) as nna; try lra.

    specialize (theta1_pos_cond _ _ _ zlty zltr rltlz) as zgtt1.
    apply x_minus_sin_x_pos; assumption. }

  unfold d1.
  rewrite tmd.
  assert (0 = sqrt ((x - rz * sin θmax)² + (y - rz * (1 - cos θmax))²)) as zarm. {
    rewrite <- sqrt_0.
    apply f_equal.
    repeat rewrite Rsqr_minus.
    repeat rewrite Rsqr_mult.
    repeat rewrite Rsqr_minus.
    setr (x² + y²
          + rz² * ((sin θmax)² + (cos θmax)²)
            - 2 * x * rz * sin θmax
          + 2 * y * rz *cos θmax
          + rz²
            - rz² * 2 * 1 * cos θmax
            - 2 * y * rz
         ).
    rewrite sin2_cos2.
    setr (x² + y² - 2 * y * rz
          + 2 * rz² * ( 1 - cos  θmax)
            - 2 * rz * (x * sin θmax - y * cos θmax)).
    rewrite rzd at 1.
    unfold Rsqr at 5.
    rewrite rzd2 at 1.
    repeat rewrite <- RmultRinv.
    rewrite tmd.
    setr 0; try lra.
    split; try lra.
    intro omceq0.
    apply Rminus_diag_uniq_sym in omceq0.
    apply cos_eq_1_2PI_0 in omceq0.
    lra.
    unfold θmax,calcθ₁.
    arn.
    setl (2 * 0).
    apply Rmult_le_compat_l ; try lra.
    destruct (total_order_T x 0); [destruct s|].
    specialize (atan2Q2 _ _ r0 zlty) as [at2l at2u].
    lra.
    specialize (atan2_PI2 _ zlty) as at2b.
    rewrite e, at2b.
    specialize PI_RGT_0; try lra.
    specialize (atan2Q1 _ _ r0 zlty) as [at2l at2u].
    lra.
    unfold θmax,calcθ₁.
    arn.
    specialize (atan2_bound _ _ nO) as [at2lb at2ub].
    lra. }

  rewrite <- zarm.
  rewrite <- tmd.
  arn.
  rewrite Darm_Q_straight_std; try (lra||assumption).
  assert (0 = sqrt (x² - (2 * rz - y) * y)) as zdef. {
    rewrite rzd.
    rewrite <- sqrt_0.
    apply f_equal.
    unfold Rsqr.
    field; lra. }
  match goal with
  | |- _ < ?R => rewrite <- (Rplus_0_r R)
  end.
  rewrite zdef.
  change (d2 r < d2 rz).
  
  set (arcl := fun x y r => r * θ1 x y r) in *.
  set (arclx := fun x y => extension_C0 (arcl x y) 0 rz) in *.
  set (arml := fun x y r => sqrt (x² - (2 * r - y) * y)) in *.
  set (armlx := fun x y => extension_C0 (arml x y) 0 rz) in *.
  simpl in armlx.
  set (d3 := fun r => plus (arclx x y r) (armlx x y r)) in *.
  simpl in d3.
  assert (forall r, 0 <= r <= rz -> d2 r = d3 r) as ird. {
    intros *.
    intros [rlb rub].
    unfold d2, d3, plus, arcl, arclx, armlx, arml, extension_C0.
    simpl.
    destruct Rbar_le_dec; [ destruct Rbar_le_dec |].
    reflexivity.
    simpl in r0, n.
    lra.
    simpl in n.
    lra. }
  rewrite (ird r), (ird rz); try (split; lra).

  assert (forall r : R, Rbar_lt 0 r -> Rbar_lt r rz -> is_derive d3 r (d' r))
    as dder3. {
    rename r into s.
    intros *.
    simpl.
    intros zlr rltrz.
    apply (is_derive_ext_loc d2); try (apply dder2; simpl; assumption).
    unfold locally.
    simpl.
    assert (0 < Rmin r (rz - r)) as zlte. {
      unfold Rmin.
      destruct Rle_dec; lra. }
    exists (mkposreal (Rmin r (rz - r)) zlte).
    intros r0 br0.
    unfold ball in br0.
    simpl in br0.
    unfold AbsRing_ball, minus, opp, plus, abs in br0.
    simpl in br0.
    unfold d2.
    unfold d3, plus, arcl, arclx, armlx, arml, extension_C0.
    destruct Rbar_le_dec;
      [destruct Rbar_le_dec|].
    reflexivity.
    simpl in *.
    apply Rnot_le_lt in n.
    exfalso.
    apply Rabs_def2 in br0.
    destruct br0 as [lb ub].
    unfold Rmin in *.
    destruct Rle_dec;
      lra.
    simpl in n.
    apply Rnot_le_lt in n.
    exfalso.
    apply Rabs_def2 in br0.
    destruct br0 as [lb ub].
    unfold Rmin in *.
    destruct Rle_dec;
      lra. }
  
  assert (forall r : R, Rbar_le 0 r -> Rbar_le r rz -> continuous d3 r)
    as d3c. {
    rename r into s.
    simpl; intros.
    unfold d3.
    unfold arclx, armlx.
    rewrite rzd.
    apply cont_dist_posy; lra.
  }

  apply (incr_function_le_cont_ep d3c dder3 pder); try (simpl; lra).
Qed.

Lemma full_path_dist_increasing :
  forall θ₀ x₀ y₀ x₁ y₁ r s (phase : straight s θ₀ x₀ y₀ x₁ y₁)
         (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0)),
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (tmaxne0 : θmax <> 0)
           (rgt0 : 0 < r)
           (sgtr : r < s),
      let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
      let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
      let d := (fun t => t * (θ1 x y) t +
                         (sqrt ((x - t * sin (θ1 x y t))² +
                                (y - t * (1 - cos (θ1 x y t)))²))) in
      d r < d s.
Proof.
  intros.
  apply straight_rot in phase.
  change (straight s 0 0 0 x y) in phase.

  unfold θmax in *; clear θmax.
  rewrite calc_angle_std in *.
  
  specialize (notid_rot θ₀ _ _ _ _ no) as not.
  simpl in not.
  change (~ (x = 0 /\ y = 0)) in not.

  change (calcθ₁ 0 0 0 x y <> 0) in tmaxne0.
  set (θmax := calcθ₁ 0 0 0 x y) in *.
  apply thmaxne0impl in tmaxne0.

  assert (~ (0 <= x /\ y = 0)) as not_forward;
    try lra.
  apply full_path_dist_increasing_s; assumption.
Qed.

(** Theorem 7 (Approach angle orders turn-to-bearing path radii) *)

Lemma ottb_bigger_theta_bigger_r_ep :
  forall θ₀ x₀ y₀ x₁ y₁ θr θs,
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (tmaxne0 : θmax <> 0)
           (tmaxne2PI : θmax <> 2 * PI)
           (trrng : θmax / 2 <= θr <= θmax)
           (tsrng : θmax / 2 <= θs <= θmax),
      let r := (x * sin θr - y * cos θr)
                 / (1 - cos θr) in
      let s := (x * sin θs - y * cos θs)
                 / (1 - cos θs) in
      forall (tp : 0 < θr)
             (to : θr < θs)
             (tu : θs < 2 * PI),
        r < s.
Proof.
  intros.
  unfold θmax in *; clear θmax.
  rewrite calc_angle_std in *.

  specialize (notid_rot θ₀ _ _ _ _ no) as not.
  simpl in not.
  change (~ (x = 0 /\ y = 0)) in not.

  unfold x, y in *.
  clear x y.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  set (θmax := calcθ₁ 0 0 0 x y) in *.

  assert (y <> 0) as yne0. {
    intros yeq0.
    apply thmaxne0impl in tmaxne0.
    apply thmaxnePIimpl in tmaxne2PI.
    lra. }

  apply ottb_bigger_theta_bigger_r_ep_std; try assumption.
Qed.

Lemma ottb_bigger_theta_bigger_r :
  forall θ₀ x₀ y₀ x₁ y₁ θr θs,
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (trrng : θmax / 2 < θr < θmax)
           (tsrng : θmax / 2 < θs < θmax),
      let r := (x * sin θr - y * cos θr)
                 / (1 - cos θr) in
      let s := (x * sin θs - y * cos θs)
                 / (1 - cos θs) in
      forall (tp : 0 < θr)
             (to : θr < θs),
        r < s.
Proof.
  intros.
  unfold θmax in *; clear θmax.
  rewrite calc_angle_std in *.

  specialize (notid_rot θ₀ _ _ _ _ no) as not.
  simpl in not.
  change (~ (x = 0 /\ y = 0)) in not.

  unfold x, y in *.
  clear x y.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  set (θmax := calcθ₁ 0 0 0 x y) in *.

  apply ottb_bigger_theta_bigger_r_std; try assumption.
  destruct tsrng.
  unfold θmax in H0.
  rewrite calcth1_atan2_s in H0.
  specialize (atan2_bound _ _ not) as [t2l t2u].
  lra.
Qed.

Lemma ottb_bigger_theta_bigger_r2 :
  forall θ₀ x₀ y₀ x₁ y₁ θr θs,
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (trrng : θmax / 2 + 2 * PI < θr < 2 * PI)
           (tsrng : θmax / 2 + 2 * PI < θs < 2 * PI),
      let r := (x * sin θr - y * cos θr)
                 / (1 - cos θr) in
      let s := (x * sin θs - y * cos θs)
                 / (1 - cos θs) in
      forall (tp : 0 < θr)
             (to : θr < θs)
             (tu : θs < 2 * PI),
        r < s.
Proof.
  intros.
  unfold θmax in *; clear θmax.
  rewrite calc_angle_std in *.

  specialize (notid_rot θ₀ _ _ _ _ no) as not.
  simpl in not.
  change (~ (x = 0 /\ y = 0)) in not.

  unfold x, y in *.
  clear x y.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  set (θmax := calcθ₁ 0 0 0 x y) in *.

  apply ottb_bigger_theta_bigger_r2_std; try assumption.
Qed.

(* begin hide *)

Theorem ottb_bigger_r_longer_path_std :
  forall x y r s Dr Ds θr θs
         (tmns : calcθ₁ 0 0 0 x y <> 0) (* cannot omit turn *)
         (phases : straight s 0 0 0 x y)
         (rp : 0 < r) rtp
         (ro : r < s) stp
         (Pr : path_segment Dr (Hx r 0 0 θr rtp) (Hy r 0 0 θr rtp)
                            (mkpt 0 0) (mkpt x y))
         (Ps : path_segment Ds (Hx s 0 0 θs stp) (Hy s 0 0 θs stp)
                            (mkpt 0 0) (mkpt x y)),
    Dr < Ds.
Proof.
  intros.

  assert (~ (x = 0 /\ y = 0)) as nO. {
    apply straightcond in phases.
    intros [xd yd].
    rewrite xd, yd in phases.
    autorewrite with null in phases.
    lra. }

  assert (straight r 0 0 0 x y) as phaser. {
    apply straightcond in phases.
    apply condstraight.
    destruct (total_order_T 0 y); [destruct s0|].
    - apply (Rlt_trans _ (2 * s * y)).
      repeat rewrite Rmult_assoc.
      repeat rewrite (Rmult_comm _ y).
      repeat rewrite <- Rmult_assoc.
      apply Rmult_lt_compat_l; try lra.
      assumption.
    - apply (Rle_lt_trans _ (2 * s * y)).
      rewrite <- e.
      arn.
      right; reflexivity.
      assumption.
    - apply (Rlt_trans _ (-0)).
      setl (- (2 * r * -y)).
      apply Ropp_lt_contravar.
      zltab.
      arn.
      apply posss.
      assumption. }

  specialize (ottb_compute_straight_t_s _ _ _ _ rtp Dr phaser Pr) as trdef.
  specialize (ottb_compute_straight_t_s _ _ _ _ stp Ds phases Ps) as tsdef.

  set (o := {| ptx := 0; pty := 0 |}) in *.

  rewrite <- (Rminus_0_r x) in nO.
  rewrite <- (Rminus_0_r y) in nO.
  specialize (rotated_straight_path_equiv
                _ _ _ _ _ nO tmns) as npx.
  autorewrite with null in npx.

  assert (0 <= θr < 2 * PI) as t1r. {
    assert (r<>0) as rne0. lra.
    specialize (theta1_rsgn_bnd _ _ _ rne0 phaser) as [t1p t1n].
    lra.
  }

  assert (0 <= θs < 2 * PI) as t1s. {
    assert (s<>0) as sne0. lra.
    specialize (theta1_rsgn_bnd _ _ _ sne0 phases) as [t1p t1n].
    lra.
  }
  rename Pr into Drdef.
  rename Ps into Dsdef.

  apply (ottb_path_distance) in Drdef.
  destruct t1r as [t1rl t1ru].
  
  apply ottb_path_distance in Dsdef.
  destruct t1s as [t1sl t1su].
  
  destruct Drdef as [[trn Drdef] |[str Drdef]].
  unfold turning, Tcx, Tcy in trn.
  unfold straight, Tcx, Tcy in phaser.
  lra. clear str.

  destruct Dsdef as [[trn Dsdef] |[str Dsdef]].
  unfold turning, Tcx, Tcy in trn.
  unfold straight, Tcx, Tcy in phases.
  lra. clear str.

  rewrite Drdef, Dsdef. clear Drdef Dsdef.
  rewrite sin_0, cos_0 in *.
  repeat rewrite Rplus_0_l.
  fieldrewrite (x - (0 - r * 0 + r * sin (θr))) (x - r * sin θr).
  fieldrewrite (y - (r * 1 - r * cos θr)) (y - r * (1 - cos θr)).
  fieldrewrite (x - (0 - s * 0 + s * sin (θs))) (x - s * sin θs).
  fieldrewrite (y - (s * 1 - s * cos θs)) (y - s * (1 - cos θs)).

  rewrite trdef, tsdef.
  apply full_path_dist_increasing_s; try assumption.
Qed.

Theorem ottb_bigger_r_longer_path_turn_std :
  forall x y r s Dr Ds θr θs 
         (nO : ~ (x = 0 /\ y = 0))
         (phases : turning s 0 0 0 x y)
         (rp : 0 < r) rtp
         (ro : r < s) stp
         (Pr : path_segment Dr (Hx r 0 0 θr rtp) (Hy r 0 0 θr rtp)
                            (mkpt 0 0) (mkpt x y))
         (Ps : path_segment Ds (Hx s 0 0 θs stp) (Hy s 0 0 θs stp)
                            (mkpt 0 0) (mkpt x y)),
    Dr < Ds.
Proof.
  intros.

  assert (0 < y) as zlty. {
    apply turningcond in phases.
    autorewrite with null in nO.
    specialize (posss _ _ nO) as px2.
    rewrite <- phases in px2.
    apply zlt_mult in px2; try assumption.
    zltab. }

  assert (straight r 0 0 0 x y) as phaser. {
    apply turningcond in phases.
    apply condstraight.
    rewrite <- phases.
    repeat rewrite Rmult_assoc.
    repeat rewrite (Rmult_comm _ y).
    repeat rewrite <- Rmult_assoc.
    apply Rmult_lt_compat_l; try lra. }

  specialize (ottb_compute_straight_t_s _ _ _ _ rtp Dr phaser Pr) as trdef.
  set (o := {| ptx := 0; pty := 0 |}) in *.

  assert (~ (0 <= x /\ y = 0)) as npx; try lra.

  assert (0 <= θr < 2 * PI) as t1r. {
    assert (r<>0) as rne0. lra.
    specialize (theta1_rsgn_bnd _ _ _ rne0 phaser) as [t1p t1n].
    rewrite <- trdef in t1p.
    change (0 < r -> 0 <= θr < 2 * PI) in t1p.
    lra.
  }

  assert (0 <= θs < 2 * PI) as t1s. {
    assert (0 < s) as sne0. lra.
    split.
    left; apply (Rmult_lt_reg_l s); try lra.
    apply (Rmult_lt_reg_l s); try lra.
    rewrite <- (Rabs_pos_eq s) at 2; try lra. }
  rename Pr into Drdef.
  rename Ps into Dsdef.

  autorewrite with null in nO.
  specialize (ottb_compute_turning_r_s _ _ _ _ _ _ phases nO Dsdef) as rzd.
  
  apply (ottb_path_distance) in Drdef.
  destruct t1r as [t1rl t1ru].
  
  apply ottb_path_distance in Dsdef.
  destruct t1s as [t1sl t1su].
  
  destruct Drdef as [[trn Drdef] |[str Drdef]].
  unfold turning, Tcx, Tcy in trn.
  unfold straight, Tcx, Tcy in phaser.
  lra. clear str.

  destruct Dsdef as [[trn Dsdef] |[str Dsdef]].
  2 : {
    unfold straight, Tcx, Tcy in str.
    unfold turning, Tcx, Tcy in phases.
    lra. }

  rewrite Drdef, Dsdef. clear Drdef Dsdef.
  rewrite sin_0, cos_0 in *.
  repeat rewrite Rplus_0_l.

  fieldrewrite (x - (0 - r * 0 + r * sin (θr))) (x - r * sin θr).
  fieldrewrite (y - (r * 1 - r * cos θr)) (y - r * (1 - cos θr)).

  rewrite <- eqv_calcs; [| arn; assumption | assumption].
  set (θmax := calcθ₁ 0 0 0 x y) in *.
  rewrite <- (Rplus_0_r (s * θmax)).

  assert (~ (x - 0 = 0 /\ y - 0 = 0)) as notO; try lra.
  assert (θmax <> 0) as notpx. {
    intros tmeq0.
    unfold θmax, calcθ₁ in tmeq0.
    autorewrite with null in tmeq0.
    assert (atan2 y x = 0) as meq0; try lra.
    apply atan2_0_impl in meq0;
      lra.  }
  assert (θmax <> 2 * PI) as notnx.  {
    intros tmeq0.
    unfold θmax, calcθ₁ in tmeq0.
    autorewrite with null in tmeq0.
    assert (atan2 y x = PI) as meq0; try lra.
    apply atan2_PI_impl in meq0 as [xlt0 yeq0]; try lra. }

  specialize (tmax_radius_gen _ _ _ _ _ notO notpx notnx) as rzd2.
  autorewrite with null in rzd2.
  rewrite Rplus_comm in rzd.
  rewrite <- rzd in rzd2.
  rename s into rz.
  change (rz = (x * sin θmax - y * cos θmax)
                 / (1 - cos θmax)) in rzd2.
  specialize (t1eqtm_gen _ _ _ _ _ notO notpx notnx) as tmd.
  autorewrite with null in tmd.
  rewrite Rplus_comm in tmd.
  rewrite <- rzd in tmd.
  change (θ1 x y rz = θmax) in tmd.
  rewrite <- tmd in rzd2.

  assert (0 = sqrt ((x - rz * sin θmax)² + (y - rz * (1 - cos θmax))²)) as zarm. {
    rewrite <- sqrt_0.
    apply f_equal.
    repeat rewrite Rsqr_minus.
    repeat rewrite Rsqr_mult.
    repeat rewrite Rsqr_minus.
    setr (x² + y²
          + rz² * ((sin θmax)² + (cos θmax)²)
            - 2 * x * rz * sin θmax
          + 2 * y * rz *cos θmax
          + rz²
            - rz² * 2 * 1 * cos θmax
            - 2 * y * rz
         ).
    rewrite sin2_cos2.
    setr (x² + y² - 2 * y * rz
          + 2 * rz² * ( 1 - cos  θmax)
            - 2 * rz * (x * sin θmax - y * cos θmax)).
    rewrite rzd at 1.
    unfold Rsqr at 5.
    rewrite rzd2 at 1.
    repeat rewrite <- RmultRinv.
    rewrite tmd.
    setr 0; try lra.
    split; try lra.
    intro omceq0.
    apply Rminus_diag_uniq_sym in omceq0.

    specialize (atan2_bound _ _ nO) as [a2lb a2ub].
    apply cos_eq_1_2PI_0 in omceq0.
    lra.

    unfold θmax,calcθ₁ in *.
    arn.
    destruct (total_order_T 0 x); [destruct s|].
    specialize (atan2Q1 _ _ r0 zlty) as [at2l at2u].
    lra.
    specialize (atan2_PI2 _ zlty) as at2b.
    rewrite <- e, at2b.
    specialize PI_RGT_0; try lra.
    specialize (atan2Q2 _ _ r0 zlty) as [at2l at2u].
    lra.
    unfold θmax,calcθ₁ in *; arn; lra. }

  rewrite zarm.
  rewrite trdef.
  rewrite <- tmd.
  apply full_path_dist_increasing_turn_s; try assumption.
Qed.

Theorem ottb_bigger_r_longer_path_turn :
  forall θ₀ x₀ y₀ x₁ y₁ r s Dr Ds θr θs 
         (tmns : calcθ₁ θ₀ x₀ y₀ x₁ y₁ <> 0) (* cannot omit turn *)
         (phases : turning s θ₀ x₀ y₀ x₁ y₁)
         (nog : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0)),
    forall
      (rp : 0 < r) rtp
      (ro : r < s) stp
      (Pr : path_segment Dr (Hx r θ₀ x₀ θr rtp) (Hy r θ₀ y₀ θr rtp)
                         (mkpt x₀ y₀) (mkpt x₁ y₁))
      (Ps : path_segment Ds (Hx s θ₀ x₀ θs stp)
                         (Hy s θ₀ y₀ θs stp)
                         (mkpt x₀ y₀) (mkpt x₁ y₁)),
    Dr < Ds.
Proof.
  intros.
  
  apply turning_rot in phases.
  set (x := (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in *.
  set (y := - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in *.

  generalize nog; intro no.
  apply (notid_rot θ₀) in no.
  change (~ (x = 0 /\ y = 0)) in no.

  assert (0 < y) as zlty. {
    apply turningcond in phases.
    specialize (posss _ _ no) as zlt2.
    rewrite <- phases in zlt2.
    apply zlt_mult in zlt2; lra. }

  assert (straight r 0 0 0 x y) as phaser. {
    apply condstraight.
    apply turningcond in phases.
    rewrite <- phases.
    repeat rewrite Rmult_assoc.
    repeat rewrite (Rmult_comm _ y).
    repeat rewrite <- Rmult_assoc.
    apply Rmult_lt_compat_l; try zltab.
    assumption. }

  set (o := {| ptx := 0; pty := 0 |}) in *.

  specialize (rotated_straight_path_equiv
                _ _ _ _ _ nog tmns) as npx.
  change (~(0 <= x /\ y = 0)) in npx.


  apply path_std in Pr; try lra.
  apply path_std in Ps; try lra.
  change (path_segment Dr (Hx r 0 0 θr rtp) (Hy r 0 0 θr rtp)
                       o {| ptx := x; pty := y |}) in Pr.
  change (path_segment Ds (Hx s 0 0 θs stp)
                       (Hy s 0 0 θs stp)
                       o {| ptx := x; pty := y |}) in Ps.
  rename Pr into Drdef.
  rename Ps into Dsdef.

  eapply ottb_bigger_r_longer_path_turn_std.
  apply no.
  apply phases.
  apply rp.
  assumption.
  apply Drdef.
  apply Dsdef.
Qed.

Theorem ottb_bigger_r_longer_path_straight :
  forall θ₀ x₀ y₀ x₁ y₁ r s Dr Ds θr θs
         (tmns : calcθ₁ θ₀ x₀ y₀ x₁ y₁ <> 0) (* cannot omit turn *)
         (phases : straight s θ₀ x₀ y₀ x₁ y₁)
         (rp : 0 < r) rtp
         (ro : r < s) stp
         (Pr : path_segment Dr (Hx r θ₀ x₀ θr rtp) (Hy r θ₀ y₀ θr rtp)
                            (mkpt x₀ y₀) (mkpt x₁ y₁))
         (Ps : path_segment Ds (Hx s θ₀ x₀ θs stp)
                            (Hy s θ₀ y₀ θs stp)
                            (mkpt x₀ y₀) (mkpt x₁ y₁)),
    Dr < Ds.
Proof.
  intros.
  generalize phases; intro nO.

  apply path_std in Pr; try lra.
  apply path_std in Ps; try lra.
  set (x := (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in *.
  set (y := - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in *.
  set (o := {| ptx := 0; pty := 0 |}) in *.

  apply (straight_not_stationary2) in nO.
  
  apply straight_rot in phases.
  change (straight s 0 0 0 x y) in phases.

  assert (straight r 0 0 0 x y) as phaser. {
    apply straightcond in phases.
    apply condstraight.
    destruct (total_order_T 0 y); [destruct s0|].
    - apply (Rlt_trans _ (2 * s * y)).
      repeat rewrite Rmult_assoc.
      repeat rewrite (Rmult_comm _ y).
      repeat rewrite <- Rmult_assoc.
      apply Rmult_lt_compat_l; try lra.
      assumption.
    - apply (Rle_lt_trans _ (2 * s * y)).
      rewrite <- e.
      arn.
      right; reflexivity.
      assumption.
    - apply (Rlt_trans _ (-0)).
      setl (- (2 * r * -y)).
      apply Ropp_lt_contravar.
      zltab.
      arn.
      apply posss.
      apply notid_rot; assumption. }
  
  generalize Pr; intro trd.
  apply ottb_compute_straight_t in trd; try assumption.
  generalize Ps; intro tsd.
  apply ottb_compute_straight_t in tsd; try assumption.
  autorewrite with null in *.

  specialize (rotated_straight_path_equiv
                _ _ _ _ _ nO tmns) as npx.
  change (~(0 <= x /\ y = 0)) in npx.

  assert (0 <= θr < 2 * PI) as t1r. {
    assert (r<>0) as rne0. lra.
    specialize (theta1_rsgn_bnd _ _ _ rne0 phaser) as [t1p t1n].
    rewrite <- trd in t1p.
    lra.
  }

  assert (0 <= θs < 2 * PI) as t1s. {
    assert (s<>0) as sne0. lra.
    specialize (theta1_rsgn_bnd _ _ _ sne0 phases) as [t1p t1n].
    rewrite <- tsd in t1p.
    lra.
  }
  rename Pr into Drdef.
  rename Ps into Dsdef.

  apply (ottb_path_distance) in Drdef.
  destruct t1r as [t1rl t1ru].
  
  apply ottb_path_distance in Dsdef.
  destruct t1s as [t1sl t1su].
  
  destruct Drdef as [[trn Drdef] |[str Drdef]].
  unfold turning, Tcx, Tcy in trn.
  unfold straight, Tcx, Tcy in phaser.
  lra. clear str.

  destruct Dsdef as [[trn Dsdef] |[str Dsdef]].
  unfold turning, Tcx, Tcy in trn.
  unfold straight, Tcx, Tcy in phases.
  lra. clear str.

  rewrite Drdef, Dsdef. clear Drdef Dsdef.
  rewrite sin_0, cos_0 in *.
  repeat rewrite Rplus_0_l.
  fieldrewrite (x - (0 - r * 0 + r * sin (θr))) (x - r * sin θr).
  fieldrewrite (y - (r * 1 - r * cos θr)) (y - r * (1 - cos θr)).
  fieldrewrite (x - (0 - s * 0 + s * sin (θs))) (x - s * sin θs).
  fieldrewrite (y - (s * 1 - s * cos θs)) (y - s * (1 - cos θs)).

  rewrite trd, tsd.
  apply full_path_dist_increasing_s; try assumption.
Qed.
(* end hide *)

(** Theorem 8 (Radius orders one-turn-to-bearing path lengths) *)
Theorem ottb_bigger_r_longer_path :
  forall θ₀ x₀ y₀ x₁ y₁ r s Dr Ds θr θs
         (nog : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
         (tmns : calcθ₁ θ₀ x₀ y₀ x₁ y₁ <> 0) (* cannot omit turn *)
         (rp : 0 < r) rtp
         (ro : r < s) stp
         (Pr : path_segment Dr (Hx r θ₀ x₀ θr rtp) (Hy r θ₀ y₀ θr rtp)
                            (mkpt x₀ y₀) (mkpt x₁ y₁))
         (Ps : path_segment Ds (Hx s θ₀ x₀ θs stp)
                            (Hy s θ₀ y₀ θs stp)
                            (mkpt x₀ y₀) (mkpt x₁ y₁)),
    Dr < Ds.
Proof.
  intros.
  specialize (ottb_r_constraints _ _ _ _ _ _ _ _ _ Ps) as [trn |str].
  eapply ottb_bigger_r_longer_path_turn; try eassumption.
  eapply ottb_bigger_r_longer_path_straight; try eassumption.
Qed.

(* begin hide *)
(* Standard form of Maximum bearing-constrained path length *)
Lemma maxlength_path_straight_std :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (straight rb 0 0 0 x y /\ θ1 x y rb <= θd /\
       exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx rb 0 0 θv tvp) (Hy rb 0 0 θv tvp) o p
           /\ Du <= Dv)) \/
      (((θd < θmax /\ ra <= (x² + y²)/(2*y) <= rb)\/
        (straight rb 0 0 0 x y /\ θd < θ1 x y rb)) /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θd twp) (Hy rw 0 0 θd twp) o p /\
           Du <= Dw)) \/
      (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= θd /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θmax twp) (Hy rw 0 0 θmax twp) o p /\
           Du <= Dw)).
Proof.
  intros until 5.
  intro u.

  specialize PI_RGT_0 as pigt0.

  assert (~(x = 0 /\ y = 0)) as no. {
    apply straightcond in phaseu.
    intros [xeq0 yeq0].
    rewrite xeq0, yeq0 in phaseu.
    clear - phaseu.
    unfold Rsqr in phaseu.
    lra. }

  assert (-2 * PI < θmax <= 2 * PI) as [tml tmu]. {
    unfold θmax, calcθ₁.
    arn.
    split.
    apply (Rmult_lt_reg_r (/2)); try lra.
    setl (-PI).
    setr (atan2 y x).
    apply atan2_bound; try assumption.
    apply (Rmult_le_reg_r (/2)); try lra.
    setr (PI).
    setl (atan2 y x).
    apply atan2_bound; try assumption. }

  assert (θmax / 2 <= PI) as tmub; try lra.
  assert (- PI < θmax / 2) as tmlb; try lra.

  assert (0 < θmax / 2 + 2 * PI) as tm2lb; try lra.
  assert (θmax / 2 - 2 * PI < 0) as tm2ub; try lra.

  assert (0 < ru) as zltru. lra.
  assert (0 < θu) as zlttu. {
    eapply zlt_mult.
    instantiate (1:=ru).
    destruct tup.
    assumption.
    left; assumption. }

  assert (rb <> 0) as rbne0. lra.
  assert (0 < rb) as zltrb. lra.
  assert (~ (rb < 0 /\ θmax = 2 * PI)) as trm. {
    unfold θmax.
    intros [rblt0 els].
    lra. }

  generalize nc; intro nc2.
  apply thmaxne0 in nc2.
  change (θmax <> 0) in nc2.

  specialize (ottb_compute_straight_t _ _ _ _ _ _ _ tup Du phaseu u) as dudef.
  autorewrite with null in dudef.
  change (θu = θ1 x y ru) in dudef.
  assert (0 < ru * (θ1 x y ru) < Rabs ru * 2 * PI) as tup'. {
    rewrite <- dudef.
    assumption. }
  
  set (f := (fun t => 0 < ru * t < Rabs ru * 2 * PI)).
  assert (existT f θu tup =
          existT f (θ1 x y ru) tup') as tc1. {
    clear - tup' tup dudef.
    apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
      try assumption. }
  
  dependent rewrite tc1 in u.
  clear tc1.
  rewrite dudef in *.
  clear dudef θu f.

  specialize (ottb_compute_straight_r
                _ _ _ _ _ _ _ tup' _ phaseu u) as rudef.
  autorewrite with null in *.

  specialize (ottb_tinrng _ _ _ _ _ _ _ tup Du phaseu u) as t1urng.
  simpl in t1urng.
  change ((0 < θmax /\ (θmax / 2 < θ1 x y ru < θmax \/ -2 * PI < θ1 x y ru < θmax / 2 - 2 * PI)) \/
          (θmax < 0 /\ (θmax < θ1 x y ru < θmax / 2 \/ θmax / 2 + 2 * PI < θ1 x y ru < 2 * PI))) in t1urng.

  assert (straight rb 0 0 0 x y \/
          ~ straight rb 0 0 0 x y) as [stt | nstt].
  {
    unfold straight.
    destruct (Rlt_dec (rb²) ((x - Tcx rb 0 0)² +
                             (y - Tcy rb 0 0)²)).
    left; assumption.
    right; assumption. }
  
  + (* introduce rb path *)
    specialize (intro_r_path_std _ _ _ stt nc2 rbne0 trm) as [rtp [dnnpf v]].
    set (θb := θ1 x y rb) in *.
    set (Lb := rb * θb + calcL rb 0 0 0 x y θb) in *.
    set (Db := {| nonneg := Lb; cond_nonneg := dnnpf |}) in *.
    change (path_segment Db (Hx rb 0 0 θb rtp) (Hy rb 0 0 θb rtp) o p) in v.

    specialize (ottb_compute_straight_r
                  _ _ _ _ _ _ _ rtp _ stt v) as rvdef.
    autorewrite with null in *.
    specialize (ottb_tinrng _ _ _ _ _ _ _ rtp Db stt v) as t1vrng.
    simpl in t1vrng.
    change ((0 < θmax /\ (θmax / 2 < θ1 x y rb < θmax \/ -2 * PI < θ1 x y rb < θmax / 2 - 2 * PI)) \/
            (θmax < 0 /\ (θmax < θ1 x y rb < θmax / 2 \/ θmax / 2 + 2 * PI < θ1 x y rb < 2 * PI))) in t1vrng.

    destruct rur as [rulb [rult |rueq]].
    2 : { rewrite <- rueq in *.
          (* case1 *)
          left.
          destruct tur as [tulb tuub].
          split; try assumption.
          rewrite rueq in tuub.
          unfold θb at 1.
          split; try assumption.
          exists Du, (θ1 x y ru), tup'.
          rewrite <- rueq in tuub.
          repeat (split; auto);
          right; reflexivity. }

    (* ru < rb (reminder: θd and (θ1 x y rb) are not related) *)
    destruct (Rle_dec (θ1 x y rb) θd) as [t1rbletd| t1rbgttd].
    ++ (* case1 *)
       left.
       split; try assumption.
       split; try assumption.
       exists Db, (θ1 x y rb), rtp.
       split.
       +++ split; try assumption.
           apply (Rle_trans _ (θ1 x y ru)).
           lra.
           apply Rnot_lt_le.
           intro t1rblttc.
           destruct (Rle_dec 0 y).
           ++++ assert (0 < θmax) as tmgt0. {
                  unfold θmax, calcθ₁.
                  arn.
                  apply (Rmult_lt_reg_r (/2)); try lra.
                  setl 0.
                  setr (atan2 y x).
                  destruct (total_order_T 0 x) as [[q |w]| s].
                  destruct r; try lra.
                  apply atan2Q1; try assumption.
                  rewrite <- w, atan2_PI2; lra.
                  destruct r as [zlty |zeqy].
                  specialize (atan2Q2 x y (ltac:(lra)) zlty); try lra.
                  rewrite <- zeqy, atan2_PI;
                    lra. } 
                
                destruct t1urng as [[zlttm restu ]| poof]; try lra; clear zlttm.
                destruct t1vrng as [[zlttm restv ]| poof]; try lra; clear zlttm.
                
                apply straight_rot in phaseu.
                specialize (theta1_rsgn_lim _ _ ru (ltac:(lra)) phaseu) as [rugtr rultr].
                clear rultr.
                specialize (rugtr (ltac:(lra))).
                autorewrite with null in *.
                destruct restu as [restu | poof]; try lra.
                
                specialize (theta1_rsgn_lim _ _ rb (ltac:(lra)) stt) as [rbgtr rbltr].
                clear rbltr.
                specialize (rbgtr (ltac:(lra))).
                autorewrite with null in *.
                destruct restv as [restv | poof]; try lra.
                
                eapply ottb_bigger_theta_bigger_r_std in t1rblttc; eauto.
                unfold θb in rvdef.
                rewrite <- rudef, <- rvdef in t1rblttc.
                lra.
                lra.
                specialize (theta1_rng _ _ ru (ltac:(lra)) phaseu) as [tl tu].
                lra.
                
           ++++ apply Rnot_le_lt in n.
                assert (θmax < 0) as tmgt0. {
                  unfold θmax, calcθ₁.
                  arn.
                  apply (Rmult_lt_reg_r (/2)); try lra.
                  setr 0.
                  setl (atan2 y x).
                  destruct (total_order_T 0 x) as [[q |w]| s].
                  specialize (atan2Q4 x y (ltac:(lra)) n); try lra.
                  rewrite <- w, atan2_mPI2; lra.
                  specialize (atan2Q3 x y (ltac:(lra)) n); try lra. } 
                
                destruct t1urng as [poof|[zlttm restu ]]; try lra; clear zlttm.
                destruct t1vrng as [poof|[zlttm restv ]]; try lra; clear zlttm.
                
                specialize (theta1_rsgn_lim _ _ ru (ltac:(lra)) phaseu) as [rugtr rultr].
                clear rultr.
                specialize (rugtr (ltac:(lra))).
                autorewrite with null in *.
                destruct restu as [poof | restu]; try lra.
                
                apply straight_rot in stt.
                specialize (theta1_rsgn_lim _ _ rb (ltac:(lra)) stt) as [rbgtr rbltr].
                clear rbltr.
                specialize (rbgtr (ltac:(lra))).
                autorewrite with null in *.
                destruct restv as [poof |restv]; try lra.
                
                eapply ottb_bigger_theta_bigger_r2_std in t1rblttc; eauto.
                unfold θb in rvdef.
                rewrite <- rudef, <- rvdef in t1rblttc.
                lra.
                lra.
                specialize (theta1_rng _ _ ru (ltac:(lra)) phaseu) as [tl tu].
                lra.
                
       +++ split; auto.
           left.
           apply (ottb_bigger_r_longer_path_std
                    _ _ _ _ Du Db _ _ nc2 stt zltru tup rult rtp u v).
           
    ++ right.
       apply Rnot_le_lt in t1rbgttd.
       change (θd < θb) in t1rbgttd.

       assert (0 < θd) as zlttd. lra.
       
       set (θu := θ1 x y ru) in *.
       change (0 < θmax /\ (θmax / 2 < θb < θmax \/
                            -2 * PI < θb < θmax / 2 - 2 * PI) \/
               θmax < 0 /\ (θmax < θb < θmax / 2 \/
                            θmax / 2 + 2 * PI < θb < 2 * PI)) in t1vrng.
       assert (0 < θb) as zlttb; try lra.

       assert (0 < θmax /\ (θmax / 2 < θd < θmax \/ -2 * PI < θd < θmax / 2 - 2 * PI) \/
               θmax < 0 /\ (θmax < θd < θmax / 2 \/ θmax / 2 + 2 * PI < θd < 2 * PI)) as tvrng;
         try lra.

       set (rd := (x * sin θd - y * cos θd) / (1 - cos θd)) in *.
       assert (rd < rb) as rdltrb. {
         rewrite rvdef.
         unfold rd.
         destruct (total_order_T 0 θmax); [destruct s|].
         - destruct t1urng as [[tordu [upr| unr]]|[tord poof]]; try lra.
           destruct t1vrng as [[tordv [vpr|vnr]]|[tord poof]]; try lra.
           destruct tvrng as [[tordd [dpr |dnr]]|[tord poof]]; try lra.
           apply ottb_bigger_theta_bigger_r_std; try assumption.
           apply (Rlt_le_trans _ θmax); lra.
         - lra.
         - destruct t1urng as [[tord poof]|[tordu [upr| unr]]]; try lra.
           destruct t1vrng as [[tord poof]|[tordv [vpr|vnr]] ]; try lra.
           destruct tvrng as  [[tord poof]|[tordd [dpr |dnr]] ]; try lra.
           apply ottb_bigger_theta_bigger_r2_std; try assumption.
           lra. }
       
       destruct tur as [tcletu [tulttd | tueqtd]].
       +++ assert (ru < rd) as ralerd. {
             rewrite rudef.
             unfold rd.
             destruct (total_order_T 0 θmax); [destruct s|].
             - destruct t1urng as [[tordu [upr| unr]]|[tord poof]]; try lra.
               destruct t1vrng as [[tordv [vpr|vnr]]|[tord poof]]; try lra.
               destruct tvrng as [[tordd [dpr |dnr]]|[tord poof]]; try lra.
               apply ottb_bigger_theta_bigger_r_std; try assumption.
               apply (Rlt_le_trans _ θmax); lra.
             - lra.
             - destruct t1urng as [[tord poof]|[tordu [upr| unr]]]; try lra.
               destruct t1vrng as [[tord poof]|[tordv [vpr|vnr]] ]; try lra.
               destruct tvrng as  [[tord poof]|[tordd [dpr |dnr]] ]; try lra.
               apply ottb_bigger_theta_bigger_r2_std; try assumption.
               lra. }

           assert (θmax / 2 < θd < θmax \/ -2 * PI < θd < θmax / 2 - 2 * PI \/
                   θmax < θd < θmax / 2 \/ θmax / 2 + 2 * PI < θd < 2 * PI) as tdr; try lra.
           unfold θmax in tdr.
           
           assert (straight rd 0 0 0 x y) as srd. {
             destruct (total_order_T 0 y); [destruct s|].
             eapply straight_r_dom1_std; try assumption.
             apply rdltrb.
             assumption.
             eapply straight_r_dom3_std; try auto.
             apply phaseu.
             eapply straight_r_dom2_std; try assumption.
             apply ralerd.
             assumption.
           }
           
           assert (~ (rd < 0 /\ calcθ₁ 0 0 0 x y = 2 * PI)) as rdc; try (intros [rdlt0 poof]; lra).
           specialize (intro_theta_path_std x y θd tdr srd rdc) as [trd [lengt0 d]].
           change (0 < rd * θd < Rabs rd * 2 * PI) in trd.
           change (0 <= rd * θd + calcL rd 0 0 0 x y θd) in lengt0.
           change (path_segment
                     {| nonneg := rd * θd + calcL rd 0 0 0 x y θd;
                        cond_nonneg := lengt0 |} (Hx rd 0 0 θd trd) (Hy rd 0 0 θd trd) o p) in d.
           set (Ld := rd * θd + calcL rd 0 0 0 x y θd) in *.
           set (Dd := {| nonneg := Ld; cond_nonneg := lengt0 |}) in *.
           
           specialize (ottb_compute_straight_t _ _ _ _ _ _ _ trd Dd srd d) as dddef.
           simpl in dddef.
           autorewrite with null in *.
           
           assert (0 < rd * (θ1 x y rd) < Rabs rd * 2 * PI) as trd'. {
             rewrite <- dddef.
             assumption. }
           
           set (f := (fun t => 0 < rd * t < Rabs rd * 2 * PI)).
           assert (existT f θd trd =
                   existT f (θ1 x y rd) trd') as tc1. {
             clear - trd' trd dddef.
             apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
               try assumption. }
           (* case2 *)
           left.
           split.

           right.
           split; try assumption.

           exists Dd, rd, trd.
           split; try lra.
           split; try assumption.
           left.
           eapply ottb_bigger_r_longer_path_std.
           apply nc2.
           apply srd.
           apply zltru.
           assumption.
           apply u.
           dependent rewrite tc1 in d.
           apply d.
           
       +++ assert (0 < ru * θd < Rabs ru * 2 * PI) as tup''. {
             rewrite <- tueqtd.
             assumption. }
           
           set (f := (fun t => 0 < ru * t < Rabs ru * 2 * PI)).
           assert (existT f θu tup' =
                   existT f θd tup'') as tc1. {
             clear - tup' tup'' tueqtd.
             apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
               try assumption. }
           dependent rewrite tc1 in u.
           (* case2 *)
           left.
           split; try assumption.
           right.
           split; try assumption.
           
           exists Du, ru, tup''.
           split; try lra.
           split; try assumption.
           right; reflexivity.

  + right.
    destruct rur as [rulb [rult |rueq]].
    2 : { exfalso.
          apply nstt.
          rewrite <- rueq.
          assumption. }

    assert (0 < y) as zlty. {
      apply Rnot_le_lt.
      intro yle0.
      apply nstt.
      apply condstraight.
      apply (Rle_lt_trans _ 0).
      apply (Rmult_le_reg_r (/ (2 * rb))).
      zltab.
      setr 0; try lra.
      setl (y); lra.
      destruct yle0 as [ylt0 |yeq0].
      apply Rplus_le_lt_0_compat.
      apply Rle_0_sqr.
      apply (Rlt_0_sqr); try lra.
      rewrite yeq0.
      arn.
      apply (Rlt_0_sqr); try lra. }

    destruct tmu as [tmu | poof].
    2 : { unfold θmax, calcθ₁ in poof.
          autorewrite with null in poof.
          apply Rmult_eq_reg_l in poof; try discrR.
          apply atan2_PI_impl in poof as [xrng yeq0].
          lra.
          assumption. }
    destruct tmub as [tmub|poof]; try lra.

    assert (0 < θmax) as zlttm. {
      unfold θmax, calcθ₁.
      arn.
      zltab.
      destruct (total_order_T 0 x); [destruct s|].
      apply atan2Q1; try assumption.
      rewrite <- e.
      rewrite atan2_PI2; try assumption.
      lra.
      specialize (atan2Q2 _ _ r zlty) as [atlb atub]; lra. }
    
    (* cutoff  between *)
    set (rz := (x² + y²) / (2 * y)).

    assert (2 * rb * y >= x² + y²) as nst. {
      apply Rnot_lt_ge.
      intro nst.
      apply nstt.
      apply condstraight.
      assumption. }

    assert (turning rz 0 0 0 x y) as phasez. {
      unfold turning, Tcx, Tcy.
      arn.
      rewrite Rsqr_minus.
      apply (Rplus_eq_reg_r (- rz² + 2 * y * rz)).
      setl (2 * y * rz).
      setr (x² + y²).
      unfold rz.
      field; lra. }

    assert (ru < rz <= rb) as [rzl rzu]. {
      split.
      unfold rz.
      apply straightcond in phaseu.
      apply (Rmult_lt_reg_l 2); try lra.
      apply (Rmult_lt_reg_l y); try lra.
      lrag phaseu.
      apply (Rmult_le_reg_l 2); try lra.
      apply (Rmult_le_reg_r y); try lra.
      unfold rz.
      apply Rge_le in nst.
      lrag nst. }

    assert (y <> 0) as yne0; try lra.
    specialize (intro_max_turning_path_std _ _ _ phasez no) as [rtp pt].
    change (0 < rz * θmax < Rabs rz * 2 * PI) in rtp.
    change (path_segment {| nonneg := rz * θmax; cond_nonneg := nna rz θmax rtp |}
                         (Hx rz 0 0 θmax rtp) (Hy rz 0 0 θmax rtp)
                         o p) in pt.
    set (Dz := {| nonneg := rz * θmax; cond_nonneg := nna rz θmax rtp |}) in *.

    destruct (Rle_dec θmax θd) as [tmletd | tmgttd].
    ++ right.
       (* case3 
       ru < rz
       rz <= rb
       θmax <= θd *)
       split; try assumption.
       split; try assumption.
       lra.
       split; try assumption.
       exists Dz, rz, rtp.
       split.
       +++ split; try lra.
       +++ split; try assumption.
           simpl.
           set (rm := (x * sin θmax - y * cos θmax) / (1 - cos θmax)) in *.
           assert (rm = rz) as rme. {
             unfold rm,θmax.
             unfold rz.
             rewrite tmax_radius; try assumption.
             reflexivity. }
           specialize (ottb_path_distance _ _ _ _ _ _ _ _ tup' u)
             as [[cnd dud]|[cnd dud]].
           exfalso.
           unfold turning in cnd.
           unfold straight in phaseu.
           rewrite <- cnd in phaseu.
           lra.
           rewrite dud.
           specialize (t1eqtm _ _ no yne0) as t1eqtm.
           rewrite Rplus_comm in t1eqtm.
           change (θ1 x y rz = θmax) in t1eqtm.
           arn.
           rewrite <- t1eqtm.
           fieldrewrite ((x - ru * sin (θ1 x y ru))² + (y - (ru - ru * cos (θ1 x y ru)))²)
                        ((x - ru * sin (θ1 x y ru))² + (y - ru * (1 - cos (θ1 x y ru)))²).

           set (d1 := (fun r:R_AbsRing =>
                         r * θ1 x y r + sqrt ((x - r * sin (θ1 x y r))² +
                                              (y - r * (1 - cos (θ1 x y r)))²))) in *.
           set (d2 := (fun r:R_AbsRing => r * θ1 x y r + sqrt (x² - (2 * r - y) * y))) in *.
           set (d' := (fun ru:R_AbsRing => (θ1 x y ru - sin (θ1 x y ru)))) in *.
           assert (forall (r:R), Rbar_lt 0 r -> Rbar_lt r rz ->
                                 is_derive d1 r (d' r)) as dderv. {
             intros r zltr rltrz.
             unfold d1, d'.
             apply full_path_dist_is_derive_s; try assumption.
             apply condstraight.
             unfold rz in rltrz.
             clear - rltrz zltr zlty.
             simpl in *.
             apply (Rmult_lt_reg_r (/ (2 * y))).
             zltab.
             setl r.
             zltab.
             lra. }

           assert (forall r : R, Rbar_lt 0 r -> Rbar_lt r rz -> is_derive d2 r (d' r))
             as dder2. {
             intros r zltr rltrz.
             apply (is_derive_ext_loc d1 d2).
             unfold locally, d1, d2.

             assert (0 < Rmin (rz - r) (r)) as egt0. {
               unfold Rmin.
               simpl in zltr, rltrz.
               destruct Rle_dec; try assumption.
               apply (Rplus_lt_reg_r r).
               setr rz; try assumption.
               arn.
               assumption. }
             
             set (eps := (mkposreal (_:R) egt0)).
             exists eps.
             intros r0 bar.
             simpl in *.
             assert (straight r0 0 0 0 x y) as rstr. {
               apply condstraight.
               apply (Rmult_lt_reg_r (/ (2 * y))); try zltab.
               setl r0; try lra.
               rewrite RmultRinv.
               change (r0 < rz).
               unfold ball in bar.
               simpl in bar.
               unfold AbsRing_ball, abs, minus, plus, opp in bar.
               simpl in bar.
               unfold Rmin, Rabs in bar;
                 destruct Rle_dec;
                 destruct Rcase_abs; lra.  }
             assert (0 < r0) as zltr0. {
               unfold ball, AbsRing_ball in bar.
               simpl in bar, r0.
               unfold AbsRing_ball, minus, plus, opp, abs in bar.
               simpl in bar.
               unfold Rmin, Rabs in bar;
                 destruct Rle_dec;
                 destruct Rcase_abs; lra. }
             assert (r0 <> 0) as r0ne0; try lra.
             rewrite (Darm_Q_straight_std _ _ _ rstr r0ne0).
             reflexivity.
             apply dderv; try assumption. }


           assert (forall r : R, Rbar_lt 0 r -> Rbar_lt r rz -> d' r > 0)
             as pder. {
             intros r zltr rltlz.
             unfold d'.
             apply Rlt_gt.
             simpl in zltr, rltlz.
             unfold rz in rltlz.
             assert (straight r 0 0 0 x y) as phaser. {
               apply condstraight.
               apply (Rmult_lt_reg_r (/ (2 * y))); try zltab.
               setl r; try lra. }
             assert (r <> 0) as rne0; try lra.
             assert (~ (r < 0 /\ θmax = 2 * PI)) as nna; try lra.
             specialize (intro_r_path_std _ _ _ phaser nc2 rne0 nna) as [[rclb rcub] rest].
             clear rest rcub.
             assert (0 < θ1 x y r) as zgtt1;
               try (apply (Rmult_lt_reg_r r); lra).

             apply x_minus_sin_x_pos; assumption. }
           rewrite Darm_Q_straight_std; try (lra||assumption).
           assert (0 = sqrt (x² - (2 * rz - y) * y)) as zdef. {
             unfold rz.
             rewrite <- sqrt_0.
             apply f_equal.
             unfold Rsqr.
             field; lra. }
           match goal with
           | |- _ <= ?R => rewrite <- (Rplus_0_r R)
           end.
           rewrite zdef.
           change (d2 ru <= d2 rz).

           set (arcl := fun x y r => r * θ1 x y r) in *.
           set (arclx := fun x y => extension_C0 (arcl x y) 0 rz) in *.
           set (arml := fun x y r => sqrt (x² - (2 * r - y) * y)) in *.
           set (armlx := fun x y => extension_C0 (arml x y) 0 rz) in *.
           simpl in armlx.
           set (d3 := fun r => plus (arclx x y r) (armlx x y r)) in *.
           simpl in d3.
           assert (forall r, 0 <= r <= rz -> d2 r = d3 r) as ird. {
             intros *.
             intros [rlb rub].
             unfold d2, d3, plus, arcl, arclx, armlx, arml, extension_C0.
             simpl.
             destruct Rbar_le_dec; [ destruct Rbar_le_dec |].
             reflexivity.
             simpl in r0, n.
             lra.
             simpl in n.
             lra. }
           rewrite (ird ru), (ird rz); try (split; lra).

           assert (forall r : R, Rbar_lt 0 r -> Rbar_lt r rz -> is_derive d3 r (d' r))
             as dder3. {
             intros *.
             simpl.
             intros zlr rltrz.
             apply (is_derive_ext_loc d2); try (apply dder2; simpl; assumption).
             unfold locally.
             simpl.
             assert (0 < Rmin r (rz - r)) as zlte. {
               unfold Rmin.
               destruct Rle_dec; lra. }
             exists (mkposreal (Rmin r (rz - r)) zlte).
             intros r0 br0.
             unfold ball in br0.
             simpl in br0.
             unfold AbsRing_ball, minus, opp, plus, abs in br0.
             simpl in br0.
             unfold d2.
             unfold d3, plus, arcl, arclx, armlx, arml, extension_C0.
             destruct Rbar_le_dec;
               [destruct Rbar_le_dec|].
             reflexivity.
             simpl in *.
             apply Rnot_le_lt in n.
             exfalso.
             apply Rabs_def2 in br0.
             destruct br0 as [lb ub].
             unfold Rmin in *.
             destruct Rle_dec;
               lra.
             simpl in n.
             apply Rnot_le_lt in n.
             exfalso.
             apply Rabs_def2 in br0.
             destruct br0 as [lb ub].
             unfold Rmin in *.
             destruct Rle_dec;
               lra. }

           assert (forall r : R, Rbar_le 0 r -> Rbar_le r rz -> continuous d3 r)
             as d3c. {
             simpl; intros.
             unfold d3.
             apply cont_dist_posy; auto.
           }

           left.
           apply (incr_function_le_cont_ep d3c dder3 pder); try (simpl; lra).
    ++ apply Rnot_le_lt in tmgttd.
       (* case2 left *)
       set (rd := (x * sin θd - y * cos θd) / (1 - cos θd)) in *.
       assert (rd < rz) as rdltrb. {
         specialize (chord_length_std _ _ _ phasez yne0) as id.
         simpl in id.
         change ((rz * (1 - cos θmax))² + (rz * sin θmax)² = y² + x²) in id.
         
         destruct t1urng as [[tordu [upr| unr]]|[tord poof]]; try lra.
         destruct (total_order_T 0 θmax); [destruct s|]; try lra.
         (* unfold rd, rz. *)
         unfold rz.
         rewrite tmax_radius.
         change (rd < (x * sin θmax - y * cos θmax) / (1 - cos θmax)).
         apply ottb_bigger_theta_bigger_r_ep_std; try assumption.
         split; try (left; assumption).
         destruct upr.
         destruct tur.
         apply (Rle_trans _ (θ1 x y ru)).
         left; assumption.
         assumption.
         change (θmax / 2 <= θmax <= θmax).
         lra.
         lra.
         assumption.  }

       destruct tur as [tcletu [tulttd | tueqtd]].
       +++ destruct t1urng as [[tordu [upr| unr]]|[tord poof]]; try lra.
           
           assert (0 < rd) as zltrd. {
             apply (Rlt_trans _ ru).
             lra.
             rewrite rudef.
             unfold rd.
             eapply ottb_bigger_theta_bigger_r_std; try (lra||assumption).
             split; try assumption.
             apply (Rlt_trans _ (θ1 x y ru)).
             destruct upr; try assumption.
             assumption. }

           assert (straight rd 0 0 0 x y) as srd. {
             clear - phasez rdltrb zltrd zlty.
             unfold turning, Tcx, Tcy in phasez.
             autorewrite with null in phasez.
             rewrite Rsqr_minus in phasez.
             assert (2 * y * rz = x² + y²) as zc. {
               apply (Rplus_eq_reg_r (rz² - 2 * y * rz)).
               lrag phasez. }
             clear phasez.
             apply condstraight.
             rewrite <- zc.
             clear zc.
             apply (Rmult_lt_reg_r (/ (y * 2))); try zltab.
             lrag rdltrb. }

           destruct (Rlt_dec rd ru) as [ralerd |regtrd].
           ++++ exfalso.
                eapply ottb_bigger_theta_bigger_r_std in tulttd.
                rewrite <- rudef in tulttd.
                change (ru < rd) in tulttd.
                lra.
                apply no.
                assumption.
                split.
                apply (Rlt_trans _ (θ1 x y ru)).
                destruct upr; try lra; assumption.
                assumption.
                assumption.
                lra.
                lra.
           ++++ apply Rnot_lt_le in regtrd.
                destruct regtrd as [regtrd | rueqrd].
                2 : {
                  (* ru = rd case *)
                  assert (θmax / 2 < θd < θmax \/
                          -2 * PI < θd < θmax / 2 - 2 * PI \/
                          θmax < θd < θmax / 2 \/
                          θmax / 2 + 2 * PI < θd < 2 * PI) as tdord; try lra.
                  assert (~ (rd < 0 /\ θmax = 2 * PI)) as tdm. {
                    unfold θmax.
                    intros [rblt0 els].
                    lra. }

                  specialize (intro_theta_path_std _ _ _ tdord srd tdm) as [rdp [dnnpf d]].
                  set (Ld := rd * θd + calcL rd 0 0 0 x y θd) in *.
                  set (Dd := {| nonneg := Ld; cond_nonneg := dnnpf |}) in *.
                  change (0 < rd * θd < Rabs rd * 2 * PI) in rdp.
                  change (path_segment Dd (Hx rd 0 0 θd rdp) (Hy rd 0 0 θd rdp) o p) in d.
                  
                  (* ottb_unique_D *)
                  assert (0 < ru * θd < Rabs ru * 2 * PI) as rdp'. {
                    rewrite rueqrd.
                    assumption. }
           
                  set (f := (fun r => 0 < r * θd < Rabs r * 2 * PI)).
                  assert (existT f ru rdp' =
                          existT f rd rdp) as tc1. {
                    clear - rdp rdp' rueqrd.
                    apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
                      try assumption. }
                  dependent rewrite <- tc1 in d.
                  clear tc1 rdp f.

                  specialize (ottb_compute_straight_t _ _ _ _ _ _ _ rdp' Dd phaseu d) as dddef.
                  simpl in dddef.
                  autorewrite with null in dddef.
                  
                  set (f := (fun θ => 0 < ru * θ < Rabs ru * 2 * PI)).
                  assert (existT f θd rdp' =
                          existT f (θ1 x y ru) tup') as tc1. {
                    clear - tup' rdp' dddef.
                    apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
                      try assumption. }
                  dependent rewrite <- tc1 in u.
                  clear tc1 f.
                  rewrite dddef in tulttd.
                  clear - tulttd.
                  exfalso.
                  lra. }
                
                assert (θmax / 2 < θd < θmax \/ -2 * PI < θd < θmax / 2 - 2 * PI \/
                        θmax < θd < θmax / 2 \/ θmax / 2 + 2 * PI < θd < 2 * PI) as tdr; try lra.
                unfold θmax in tdr.
                
                
                assert (~ (rd < 0 /\ calcθ₁ 0 0 0 x y = 2 * PI)) as rdc; try (intros [rdlt0 poof]; lra).
                specialize (intro_theta_path_std x y θd tdr srd rdc) as [trd [lengt0 d]].
                change (0 < rd * θd < Rabs rd * 2 * PI) in trd.
                change (0 <= rd * θd + calcL rd 0 0 0 x y θd) in lengt0.
                change (path_segment
                          {| nonneg := rd * θd + calcL rd 0 0 0 x y θd;
                             cond_nonneg := lengt0 |} (Hx rd 0 0 θd trd) (Hy rd 0 0 θd trd) o p) in d.
                set (Ld := rd * θd + calcL rd 0 0 0 x y θd) in *.
                set (Dd := {| nonneg := Ld; cond_nonneg := lengt0 |}) in *.
                
                specialize (ottb_compute_straight_t _ _ _ _ _ _ _ trd Dd srd d) as dddef.
                simpl in dddef.
                autorewrite with null in *.
                
                assert (0 < rd * (θ1 x y rd) < Rabs rd * 2 * PI) as trd'. {
                  rewrite <- dddef.
                  assumption. }
                
                set (f := (fun t => 0 < rd * t < Rabs rd * 2 * PI)).
                assert (existT f θd trd =
                        existT f (θ1 x y rd) trd') as tc1. {
                  clear - trd' trd dddef.
                  apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
                    try assumption. }
                (* case2 *)
                left.
                split.
                left.
                split; try assumption.
                lra.
                
                exists Dd, rd, trd.
                split; try lra.
                split; try assumption.
                left.
                eapply ottb_bigger_r_longer_path_std.
                apply nc2.
                apply srd.
                apply zltru.
                apply regtrd.
                apply u.
                apply d.
       +++ assert (0 < ru * θd < Rabs ru * 2 * PI) as tup''. {
             rewrite <- tueqtd.
             assumption. }
           set (θu := θ1 x y ru) in *.
           set (f := (fun t => 0 < ru * t < Rabs ru * 2 * PI)).
           assert (existT f θu tup' =
                   existT f θd tup'') as tc1. {
             clear - tup' tup'' tueqtd.
             apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
               try assumption. }
           dependent rewrite tc1 in u.
           (* case2 *)
           left.
           split.
           left.
           split; try assumption.
           lra.

           exists Du, ru, tup''.
           split; try lra.
           split; try assumption.
           right; reflexivity.
Qed.


Lemma maxlength_path_turn_std :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu : turning ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= θd /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θmax twp) (Hy rw 0 0 θmax twp) o p /\
           Du <= Dw)).
Proof.
  intros until 5.
  intro u.

  specialize PI_RGT_0 as pigt0.

  assert (~(x = 0 /\ y = 0)) as no; try lra.

  assert (-2 * PI < θmax <= 2 * PI) as [tml tmu]. {
    unfold θmax, calcθ₁.
    arn.
    split.
    apply (Rmult_lt_reg_r (/2)); try lra.
    setl (-PI).
    setr (atan2 y x).
    apply atan2_bound; try assumption.
    apply (Rmult_le_reg_r (/2)); try lra.
    setr (PI).
    setl (atan2 y x).
    apply atan2_bound; try assumption. }

  assert (θmax / 2 <= PI) as tmub; try lra.
  assert (- PI < θmax / 2) as tmlb; try lra.

  assert (0 < θmax / 2 + 2 * PI) as tm2lb; try lra.
  assert (θmax / 2 - 2 * PI < 0) as tm2ub; try lra.

  assert (0 < ru) as zltru. lra.
  assert (0 < θu) as zlttu. {
    eapply zlt_mult.
    instantiate (1:=ru).
    destruct tup.
    assumption.
    left; assumption. }

  assert (rb <> 0) as rbne0. lra.
  assert (0 < rb) as zltrb. lra.
  assert (~ (rb < 0 /\ θmax = 2 * PI)) as trm. {
    unfold θmax.
    intros [rblt0 els].
    lra. }

  generalize nc; intro nc2.
  apply thmaxne0 in nc2.
  change (θmax <> 0) in nc2.

  specialize (ottb_compute_turning_t_s _ _ _ _ tup Du no phaseu u) as dudef.
  simpl in dudef.
  change (ru * θmax <= ru * θu < Rabs ru * 2 * PI) in dudef.
  rewrite (Rabs_pos_eq ru) in dudef; try lra.

  assert (0 < y) as zlty. {
    apply turningcond in phaseu.
    specialize (posss _ _ no) as zlt2.
    rewrite <- phaseu in zlt2.
    apply zlt_mult in zlt2; lra. }

  assert (0 < θmax) as zlttm. {
    unfold θmax, calcθ₁.
    arn.
    setl (2 * 0).
    apply Rmult_lt_compat_l; try lra.
    destruct (total_order_T 0 x); [destruct s|].
    - specialize (atan2Q1 _ _ r zlty) as [at2l at2u].
      lra.
    - rewrite <- e.
      rewrite (atan2_PI2 _ zlty).
      lra.
    - specialize (atan2Q2 _ _ r zlty) as [at2l at2u].
      lra. }
  
  destruct dudef as [tul tuu].
  
  specialize (ottb_compute_turning_r_s _ _ _ _ tup Du phaseu no u) as rudef.

  assert (straight rb 0 0 0 x y \/
          ~ straight rb 0 0 0 x y) as [stt | nstt]. {
    unfold straight.
    destruct (Rlt_dec (rb²) ((x - Tcx rb 0 0)² +
                             (y - Tcy rb 0 0)²)).
    left; assumption.
    right; assumption. }
  
  + exfalso.
    apply straightcond in stt.
    apply turningcond in phaseu.
    rewrite <- phaseu in stt.
    assert (rb < ru) as rbltru. {
      apply (Rmult_lt_reg_l 2); try lra.
      apply (Rmult_lt_reg_r y); try lra. }
    lra.
  + specialize (intro_max_turning_path_std _ _ _ phaseu no) as [rtp u2].
    unfold θmax in *; clear θmax.
    set (θmax := calcθ₁ 0 0 0 x y) in *.
    set (Du2 := {| nonneg := ru * θmax; cond_nonneg :=
                                          nna ru θmax rtp |}) in *.
    split; try lra.
    split.
    apply Rmult_le_reg_l in tul; try lra.

    exists Du2, ru, rtp.
    split; try lra.
    split; try lra.
    apply u2.
    right.

    specialize (ottb_path_distance _ _ _ _ _ _ _ _ tup u) as [[trn dst] | [stt dst]].
    simpl.
    rewrite dst.
    rewrite <- eqv_calcs.
    unfold θmax.
    reflexivity.
    arn.
    assumption.
    assumption.

    exfalso.
    apply straightcond in stt.
    apply turningcond in phaseu.
    clear - stt phaseu.
    lra.
Qed.

Theorem maxlength_path_std :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (straight rb 0 0 0 x y /\ θ1 x y rb <= θd /\
       exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx rb 0 0 θv tvp) (Hy rb 0 0 θv tvp) o p
           /\ Du <= Dv)) \/
      (((θd < θmax /\ ra <= (x² + y²)/(2*y) <= rb)\/
        (straight rb 0 0 0 x y /\ θd < θ1 x y rb)) /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θd twp) (Hy rw 0 0 θd twp) o p /\
           Du <= Dw)) \/
      (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= θd /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θmax twp) (Hy rw 0 0 θmax twp) o p /\
           Du <= Dw)).
Proof.
  intros * zltra rurng turng * npx psu.
  generalize psu; intro phaseu.
  apply ottb_r_constraints in phaseu as [ phaseu|phaseu].
  right; right.
  eapply maxlength_path_turn_std; try eassumption.
  eapply maxlength_path_straight_std; try eassumption.
Qed.

Corollary maxlength_path_std_arg1_impl_not_arg2 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (straight rb 0 0 0 x y /\ θ1 x y rb <= θd) ->
      ~((θd < θmax /\ 2 * ra * y <= (x² + y²) <= 2 * rb *y)\/
        (straight rb 0 0 0 x y /\ θd < θ1 x y rb)).
Proof.
  intros until 4.
  intros u [a1c1 a1c2].
  apply straightcond in a1c1.
  lra.
Qed.

Corollary maxlength_path_std_arg2_impl_not_arg1 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      ((θd < θmax /\ 2 * ra * y <= (x² + y²) <= 2 * rb *y)\/
        (straight rb 0 0 0 x y /\ θd < θ1 x y rb)) ->
      ~(straight rb 0 0 0 x y /\ θ1 x y rb <= θd).
Proof.
  intros until 4.
  intros u [a2c1 |a2c2].
  intros [a1c1 a1c2].
  apply straightcond in a1c1.
  lra.
  lra.
Qed.


Corollary maxlength_path_std_arg1_impl_not_arg3 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (straight rb 0 0 0 x y /\ θ1 x y rb <= θd) ->
      ~(2 * ra * y <= (x² + y²) <= 2 * rb * y /\ θmax <= θd).
Proof.
  intros until 4.
  intros u [a1c1 a1c2].
  intros [a3c1 a3c2].
  apply straightcond in a1c1.
  lra.
Qed.

Corollary maxlength_path_std_arg3_impl_not_arg1 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (2 * ra * y <= (x² + y²) <= 2 * rb * y /\ θmax <= θd) ->
      ~(straight rb 0 0 0 x y /\ θ1 x y rb <= θd).
Proof.
  intros until 4.
  intros u [a3c1 a3c2].
  intros [a1c1 a1c2].
  apply straightcond in a1c1.
  lra.
Qed.

Corollary maxlength_path_std_arg2_impl_not_arg3 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (straight rb 0 0 0 x y /\ θd < θ1 x y rb) ->
      ~(2 * ra * y <= (x² + y²) <= 2 * rb * y /\ θmax <= θd).
Proof.
  intros until 4.
  intros u [a1c1 a1c2].
  intros [a3c1 a3c2].
  apply straightcond in a1c1.
  lra.
Qed.

Corollary maxlength_path_std_arg3_impl_not_arg2 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (2 * ra * y <= (x² + y²) <= 2 * rb * y /\ θmax <= θd) ->
      ~(straight rb 0 0 0 x y /\ θd < θ1 x y rb).
Proof.
  intros until 4.
  intros u [a3c1 a3c2].
  intros [a1c1 a1c2].
  apply straightcond in a1c1.
  lra.
Qed.

(* Third term does not exist because minimum theta value would be thetamax/2, 
disallowed because it would require r=0, ra is the minimum r and 0 < ra *)


Lemma minlength_path_straight_std :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (straight ra 0 0 0 x y /\ θc <= θ1 x y ra <= θd /\
       exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx ra 0 0 θv tvp) (Hy ra 0 0 θv tvp) o p
           /\  Dv <= Du)) \/
      (θ1 x y ra < θc /\ 
       (((ra <= (x² + y²)/(2*y) \/ y = 0)/\ θc < θmax) \/
        (y < 0 /\ θmax < 0)) /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θc twp) (Hy rw 0 0 θc twp) o p /\
           Dw <= Du)).
Proof.
  intros * lt rur tur phaseu * nc u.

  specialize PI_RGT_0 as pigt0.

  assert (~(x = 0 /\ y = 0)) as no. {
    apply straightcond in phaseu.
    intros [xeq0 yeq0].
    rewrite xeq0, yeq0 in phaseu.
    clear - phaseu.
    unfold Rsqr in phaseu.
    lra. }

  assert (-2 * PI < θmax <= 2 * PI) as [tml tmu]. {
    unfold θmax, calcθ₁.
    arn.
    split.
    apply (Rmult_lt_reg_r (/2)); try lra.
    setl (-PI).
    setr (atan2 y x).
    apply atan2_bound; try assumption.
    apply (Rmult_le_reg_r (/2)); try lra.
    setr (PI).
    setl (atan2 y x).
    apply atan2_bound; try assumption. }

  assert (θmax / 2 <= PI) as tmub; try lra.
  assert (- PI < θmax / 2) as tmlb; try lra.

  assert (0 < θmax / 2 + 2 * PI) as tm2lb; try lra.
  assert (θmax / 2 - 2 * PI < 0) as tm2ub; try lra.

  assert (0 < ru) as zltru. lra.
  assert (0 < θu) as zlttu. {
    eapply zlt_mult.
    instantiate (1:=ru).
    destruct tup.
    assumption.
    left; assumption. }

  assert (ra <> 0) as rbne0. lra.
  assert (0 < ra) as zltrb. lra.
  assert (~ (ra < 0 /\ θmax = 2 * PI)) as trm. {
    unfold θmax.
    intros [rblt0 els].
    lra. }

  generalize nc; intro nc2.
  apply thmaxne0 in nc2.
  change (θmax <> 0) in nc2.

  specialize (ottb_compute_straight_t _ _ _ _ _ _ _ tup Du phaseu u) as dudef.
  autorewrite with null in dudef.
  change (θu = θ1 x y ru) in dudef.
  assert (0 < ru * (θ1 x y ru) < Rabs ru * 2 * PI) as tup'. {
    rewrite <- dudef.
    assumption. }
  
  set (f := (fun t => 0 < ru * t < Rabs ru * 2 * PI)).
  assert (existT f θu tup =
          existT f (θ1 x y ru) tup') as tc1. {
    clear - tup' tup dudef.
    apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
      try assumption. }
  
  dependent rewrite tc1 in u.
  clear tc1.
  rewrite dudef in *.
  clear dudef θu f.

  specialize (ottb_compute_straight_r
                _ _ _ _ _ _ _ tup' _ phaseu u) as rudef.
  autorewrite with null in *.

  specialize (ottb_tinrng _ _ _ _ _ _ _ tup Du phaseu u) as t1urng.
  simpl in t1urng.
  change ((0 < θmax /\ (θmax / 2 < θ1 x y ru < θmax \/
                        -2 * PI < θ1 x y ru < θmax / 2 - 2 * PI)) \/
          (θmax < 0 /\ (θmax < θ1 x y ru < θmax / 2 \/
                        θmax / 2 + 2 * PI < θ1 x y ru < 2 * PI))) in t1urng.

  (* path_segment with r=0 -> theta=thetamax/2 *)
  (* 0 < ra -> thetamax/2 < thetaa *)
  (* issue is where does thetac fall, with respect to thetamax/2? *)
  (* thetac < thetamax/2 -> thetaa,ra determines the min *)
  (* thetamax/2 < thetac -> dominated by rc or ra depending on
                            rc < ra -> thetaa,ra is the min
                            otherwise  thetac,rc is the min *)
  
  assert ((straight ra 0 0 0 x y)
          \/ ~ straight ra 0 0 0 x y) as [stt | nstt]. {
    unfold straight.
    destruct (Rlt_dec (ra²) ((x - Tcx ra 0 0)² +
                             (y - Tcy ra 0 0)²)).
    left; assumption.
    right; assumption. }
  
  + (* introduce ra path *)
    specialize (intro_r_path_std _ _ _ stt nc2 rbne0 trm) as [rtp [dnnpf v]].
    set (θa := θ1 x y ra) in *.
    set (La := ra * θa + calcL ra 0 0 0 x y θa) in *.
    set (Da := {| nonneg := La; cond_nonneg := dnnpf |}) in *.
    change (path_segment Da (Hx ra 0 0 θa rtp) (Hy ra 0 0 θa rtp) o p) in v.

    specialize (ottb_compute_straight_r
                  _ _ _ _ _ _ _ rtp _ stt v) as rvdef.
    autorewrite with null in *.
    specialize (ottb_tinrng _ _ _ _ _ _ _ rtp Da stt v) as t1vrng.
    simpl in t1vrng.
    change ((0 < θmax /\ (θmax / 2 < θ1 x y ra < θmax \/
                          -2 * PI < θ1 x y ra < θmax / 2 - 2 * PI)) \/
            (θmax < 0 /\ (θmax < θ1 x y ra < θmax / 2 \/
                          θmax / 2 + 2 * PI < θ1 x y ra < 2 * PI))) in t1vrng.

    destruct rur as [[ralt |raeq] ruub].
    2 : { rewrite raeq in *.
          left.
          (* case1 *)
          split; try assumption.
          split.
          assert (θ1 x y ru = θa) as tueqta. {
            unfold θa.
            rewrite raeq.
            reflexivity.
          }
          rewrite <- tueqta; assumption.
          exists Du, (θ1 x y ru), tup'.
          repeat (split; auto).
          right; reflexivity. }

    (* ra < ru (reminder: θc and (θ1 x y ra) are not related) *)
    destruct (Rlt_dec (θ1 x y ra) θc) as [t1rbletd| t1rbgttd].
    ++ right.
       change (θa < θc) in t1rbletd.

       assert (0 < θa) as zltta. {
         destruct rtp.
         clear - lt r.
         apply (Rmult_lt_reg_l ra); try assumption.
         setl 0.
         assumption. } 

       assert (0 < θc) as zlttd; try lra.
       
       set (θu := θ1 x y ru) in *.
       change (0 < θmax /\ (θmax / 2 < θa < θmax \/ -2 * PI < θa < θmax / 2 - 2 * PI) \/
               θmax < 0 /\ (θmax < θa < θmax / 2 \/ θmax / 2 + 2 * PI < θa < 2 * PI)) in t1vrng.

       assert (0 < θmax /\ (θmax / 2 < θc < θmax \/ -2 * PI < θc < θmax / 2 - 2 * PI) \/
               θmax < 0 /\ (θmax < θc < θmax / 2 \/ θmax / 2 + 2 * PI < θc < 2 * PI)) as tvrng;
         try lra.

       set (rc := (x * sin θc - y * cos θc) / (1 - cos θc)) in *.
       assert (ra < rc) as rdltrb. {
         rewrite rvdef.
         unfold rc.
         destruct (total_order_T 0 θmax); [destruct s|].
         - destruct t1urng as [[tordu [upr| unr]]|[tord poof]]; try lra.
           destruct t1vrng as [[tordv [vpr|vnr]]|[tord poof]]; try lra.
           destruct tvrng as [[tordd [dpr |dnr]]|[tord poof]]; try lra.
           apply ottb_bigger_theta_bigger_r_std; try assumption.
           apply (Rlt_le_trans _ θmax); lra.
         - lra.
         - destruct t1urng as [[tord poof]|[tordu [upr| unr]]]; try lra.
           destruct t1vrng as [[tord poof]|[tordv [vpr|vnr]] ]; try lra.
           destruct tvrng as  [[tord poof]|[tordd [dpr |dnr]] ]; try lra.
           apply ottb_bigger_theta_bigger_r2_std; try assumption.
           lra. }

       destruct tur as [[tclttu | tceqtu] tuletc].
       +++ assert (rc < ru) as ralerd. {
             rewrite rudef.
             unfold rc.
             destruct (total_order_T 0 θmax); [destruct s|].
             - destruct t1urng as [[tordu [upr| unr]]|[tord poof]]; try lra.
               destruct t1vrng as [[tordv [vpr|vnr]]|[tord poof]]; try lra.
               destruct tvrng as [[tordd [dpr |dnr]]|[tord poof]]; try lra.
               apply ottb_bigger_theta_bigger_r_std; try assumption.
               apply (Rlt_le_trans _ θmax); lra.
             - lra.
             - destruct t1urng as [[tord poof]|[tordu [upr| unr]]]; try lra.
               destruct t1vrng as [[tord poof]|[tordv [vpr|vnr]] ]; try lra.
               destruct tvrng as  [[tord poof]|[tordd [dpr |dnr]] ]; try lra.
               apply ottb_bigger_theta_bigger_r2_std; try assumption.
               lra. }
           
           assert (θmax / 2 < θc < θmax \/ -2 * PI < θc < θmax / 2 - 2 * PI \/
                   θmax < θc < θmax / 2 \/ θmax / 2 + 2 * PI < θc < 2 * PI) as tdr; try lra.
           unfold θmax in tdr.
           
           assert (straight rc 0 0 0 x y) as srd. {
             destruct (total_order_T 0 y); [destruct s|].
             eapply straight_r_dom1_std; try assumption.
             apply ralerd.
             assumption.
             eapply straight_r_dom3_std; try auto.
             apply phaseu.
             eapply straight_r_dom2_std; try assumption.
             apply rdltrb.
             assumption.
           }
           
           assert (~ (rc < 0 /\ calcθ₁ 0 0 0 x y = 2 * PI))
             as rdc; try (intros [rdlt0 poof]; lra).
           specialize (intro_theta_path_std x y θc tdr srd rdc)
             as [trd [lengt0 d]].
           change (0 < rc * θc < Rabs rc * 2 * PI) in trd.
           change (0 <= rc * θc + calcL rc 0 0 0 x y θc) in lengt0.
           change (path_segment
                     {| nonneg := rc * θc + calcL rc 0 0 0 x y θc;
                        cond_nonneg := lengt0 |}
                     (Hx rc 0 0 θc trd) (Hy rc 0 0 θc trd) o p) in d.
           set (Lc := rc * θc + calcL rc 0 0 0 x y θc) in *.
           set (Dc := {| nonneg := Lc; cond_nonneg := lengt0 |}) in *.
           
           specialize (ottb_compute_straight_t _ _ _ _ _ _ _ trd Dc srd d) as dddef.
           simpl in dddef.
           autorewrite with null in *.
           
           assert (0 < rc * (θ1 x y rc) < Rabs rc * 2 * PI) as trd'. {
             rewrite <- dddef.
             assumption. }
           
           set (f := (fun t => 0 < rc * t < Rabs rc * 2 * PI)).
           assert (existT f θc trd =
                   existT f (θ1 x y rc) trd') as tc1. {
             clear - trd' trd dddef.
             apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
               try assumption. }
           (* case2 *)
           split.
           lra.
           split.
           destruct (total_order_T y 0) as [yle0 |ygt0];
             [destruct yle0 as [ylt0|yeq0]|].
           right.
           split; try assumption.
           unfold θmax.
           rewrite calcth1_atan2_s.
           setl (-(2* - atan2 y x)).
           setr (-0).
           apply Ropp_lt_contravar.
           zltab.
           setl (-0).
           apply Ropp_lt_contravar.
           destruct (total_order_T x 0) as [xle0 |xgt0];
             [destruct xle0 as [xlt0|xeq0]|].
           apply (Rlt_trans _ (- (PI/2))).
           apply atan2Q3;
             try lra.
           apply (Rmult_lt_reg_r 2); try lra.
           rewrite xeq0.
           rewrite atan2_mPI2; try assumption.
           lra.
           apply atan2Q4;
             try lra.
           left.
           split.
           right.
           assumption.
           unfold θmax.
           rewrite calcth1_atan2_s.
           rewrite yeq0 in *.
           destruct (total_order_T x 0) as [xle0 |xgt0];
             [destruct xle0 as [xlt0|xeq0]|].
           rewrite atan2_PI; try assumption.
           lra.
           exfalso; lra.
           exfalso; lra.
           left; split.
           left.
           apply (Rmult_le_reg_r (2 * y)).
           zltab.
           apply straightcond in stt.
           clear - stt ygt0.
           left.
           lrag stt.
           destruct t1urng as [[tord poof]|[tordu [upr| unr]]]; try lra.
           exfalso.
           generalize tordu.
           apply Rlt_asym.
           unfold θmax.
           rewrite calcth1_atan2_s.
           setl (2 * 0).
           apply Rmult_lt_compat_l; try lra.

           destruct (total_order_T x 0) as [xle0 |xgt0];
             [destruct xle0 as [xlt0|xeq0]|].
           apply (Rlt_trans _ (PI/2)); try lra.
           apply atan2Q2; try assumption.
           rewrite xeq0.
           rewrite atan2_PI2; try lra.
           apply atan2Q1; try assumption.

           exists Dc, rc, trd.
           split; [lra|].
           split; try assumption.
           left.
           eapply ottb_bigger_r_longer_path_std.
           apply nc2.
           apply phaseu.
           assert (0 < rc) as zltrc; try lra.
           apply zltrc.
           assumption.
           apply d.
           apply u.

       +++ assert (0 < ru * θc < Rabs ru * 2 * PI) as tup''. {
             rewrite tceqtu.
             assumption. }
           
           set (f := (fun t => 0 < ru * t < Rabs ru * 2 * PI)).
           assert (existT f θu tup' =
                   existT f θc tup'') as tc1. {
             clear - tup' tup'' tceqtu.
             apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
               auto. }
           dependent rewrite tc1 in u.
           (* case2 *)
           split.
           lra.

           split.
           destruct (total_order_T y 0) as [yle0 |ygt0];
             [destruct yle0 as [ylt0|yeq0]|].
           right.
           split; try assumption.
           unfold θmax.
           rewrite calcth1_atan2_s.
           setl (-(2* - atan2 y x)).
           setr (-0).
           apply Ropp_lt_contravar.
           zltab.
           setl (-0).
           apply Ropp_lt_contravar.
           destruct (total_order_T x 0) as [xle0 |xgt0];
             [destruct xle0 as [xlt0|xeq0]|].
           apply (Rlt_trans _ (- (PI/2))).
           apply atan2Q3;
             try lra.
           apply (Rmult_lt_reg_r 2); try lra.
           rewrite xeq0.
           rewrite atan2_mPI2; try assumption.
           lra.
           apply atan2Q4;
             try lra.
           left.
           split.
           right.
           assumption.
           unfold θmax.
           rewrite calcth1_atan2_s.
           rewrite yeq0 in *.
           destruct (total_order_T x 0) as [xle0 |xgt0];
             [destruct xle0 as [xlt0|xeq0]|].
           rewrite atan2_PI; try assumption.
           lra.
           exfalso; lra.
           exfalso; lra.
           left; split.
           left.
           apply (Rmult_le_reg_r (2 * y)).
           zltab.
           apply straightcond in stt.
           clear - stt ygt0.
           left.
           lrag stt.
           destruct t1urng as [[tord poof]|[tordu [upr| unr]]]; try lra.
           exfalso.
           generalize tordu.
           apply Rlt_asym.
           unfold θmax.
           rewrite calcth1_atan2_s.
           setl (2 * 0).
           apply Rmult_lt_compat_l; try lra.
           destruct (total_order_T x 0) as [xle0 |xgt0];
             [destruct xle0 as [xlt0|xeq0]|].
           apply (Rlt_trans _ (PI/2)); try lra.
           apply atan2Q2; try assumption.
           rewrite xeq0.
           rewrite atan2_PI2; try lra.
           apply atan2Q1; try assumption.

           exists Du, ru, tup''.
           split; try lra.
           split; try assumption.
           right; reflexivity.

    ++ left.
       apply Rnot_lt_le in t1rbgttd.
       (* case1 *)
       split; try assumption.
       split.
       split; try assumption.

       assert (θa < θ1 x y ru) as talttu. {
         apply Rnot_le_lt.
         intros [trltta |treqta].
         destruct t1urng as [[tordu [upr| unr]]|[tordu [upr| unr]]]; try lra.
         destruct t1vrng as [[tordv [vpr|vnr]]|[tordv [vpr|vnr]] ]; try lra.
         
         eapply ottb_bigger_theta_bigger_r_std in trltta;
           [|apply no|assumption | assumption| assumption| ].
         rewrite <- rvdef in trltta.
         rewrite <- rudef in trltta.
         lra.
         unfold θa; lra.
         
         destruct rtp as [zltrata rataltra2pi].
         generalize zltrata; intro zltta.
         rewrite <- (Rmult_0_r ra) in zltta.
         apply Rmult_lt_reg_l in zltta; try assumption.
         unfold θa in zltta.
         lra.
         destruct t1vrng as [[tordv [vpr|vnr]]|[tordv [vpr|vnr]] ]; try lra.
         assert (0 < θa) as zltta; try lra.
         unfold θa in *; lra.
         eapply ottb_bigger_theta_bigger_r2_std in trltta;
           [|apply no| assumption| assumption | assumption| unfold θa; lra].
         rewrite <- rvdef in trltta.
         rewrite <- rudef in trltta.
         lra.

         rewrite treqta in *.
         rewrite <- rvdef in rudef.
         lra.
       }
       lra.
       exists Da, (θ1 x y ra), rtp.
       split.
       +++ split; try assumption.
           apply (Rle_trans _ (θ1 x y ru)); try lra.
           apply Rnot_lt_le.
           intro t1rultta.
           destruct (Rle_dec 0 y).
           ++++ assert (0 < θmax) as tmgt0. {
                  unfold θmax, calcθ₁.
                  arn.
                  apply (Rmult_lt_reg_r (/2)); try lra.
                  setl 0.
                  setr (atan2 y x).
                  destruct (total_order_T 0 x) as [[q |w]| s].
                  destruct r; try lra.
                  apply atan2Q1; try assumption.
                  rewrite <- w, atan2_PI2; lra.
                  destruct r.
                  specialize (atan2Q2 x y (ltac:(lra)) H); try lra.
                  rewrite <- H, atan2_PI.
                  lra.
                  lra. }
                
                destruct t1urng as [[zlttm restu ]| poof]; try lra; clear zlttm.
                destruct t1vrng as [[zlttm restv ]| poof]; try lra; clear zlttm.
                
                apply straight_rot in phaseu.
                specialize (theta1_rsgn_lim _ _ ru (ltac:(lra)) phaseu) as [rugtr rultr].
                clear rultr.
                specialize (rugtr (ltac:(lra))).
                autorewrite with null in *.
                destruct restu as [restu | poof]; try lra.
                
                specialize (theta1_rsgn_lim _ _ ra (ltac:(lra)) stt) as [rbgtr rbltr].
                clear rbltr.
                specialize (rbgtr (ltac:(lra))).
                autorewrite with null in *.
                destruct restv as [restv | poof]; try lra.
                
                eapply ottb_bigger_theta_bigger_r_std in t1rultta; eauto.
                unfold θa in rvdef.
                rewrite <- rudef, <- rvdef in t1rultta.
                lra.
                lra.
                
           ++++ apply Rnot_le_lt in n.
                assert (θmax < 0) as tmgt0. {
                  unfold θmax, calcθ₁.
                  arn.
                  apply (Rmult_lt_reg_r (/2)); try lra.
                  setr 0.
                  setl (atan2 y x).
                  destruct (total_order_T 0 x) as [[q |w]| s].
                  specialize (atan2Q4 x y (ltac:(lra)) n); try lra.
                  rewrite <- w, atan2_mPI2; lra.
                  specialize (atan2Q3 x y (ltac:(lra)) n); try lra. }
                
                destruct t1urng as [poof|[zlttm restu ]]; try lra; clear zlttm.
                destruct t1vrng as [poof|[zlttm restv ]]; try lra; clear zlttm.
                
                specialize (theta1_rsgn_lim _ _ ru (ltac:(lra)) phaseu) as [rugtr rultr].
                clear rultr.
                specialize (rugtr (ltac:(lra))).
                autorewrite with null in *.
                destruct restu as [poof | restu]; try lra.
                
                apply straight_rot in stt.
                specialize (theta1_rsgn_lim _ _ ra (ltac:(lra)) stt) as [rbgtr rbltr].
                clear rbltr.
                specialize (rbgtr (ltac:(lra))).
                autorewrite with null in *.
                destruct restv as [poof |restv]; try lra.
                
                eapply ottb_bigger_theta_bigger_r2_std in t1rultta; eauto.
                unfold θa in rvdef.
                rewrite <- rudef, <- rvdef in t1rultta.
                lra.
                lra.
                
       +++ split; auto.
           left.
           apply (ottb_bigger_r_longer_path_std
                    _ _ _ _ Da Du _ _ nc2 phaseu lt rtp ralt tup' v u).
           
  + right.
    destruct rur as [[rult |rueq] ruub ].
    2 : { exfalso.
          apply nstt.
          rewrite rueq.
          assumption. }

    assert (0 < y) as zlty. {
      apply Rnot_le_lt.
      intro yle0.
      apply nstt.
      apply condstraight.
      apply (Rle_lt_trans _ 0).
      apply (Rmult_le_reg_r (/ (2 * ra))).
      zltab.
      setr 0; try lra.
      setl (y); lra.
      destruct yle0 as [ylt0 |yeq0].
      apply Rplus_le_lt_0_compat.
      apply Rle_0_sqr.
      apply (Rlt_0_sqr); try lra.
      rewrite yeq0.
      arn.
      apply (Rlt_0_sqr); try lra. }

    destruct tmu as [tmu | poof].
    2 : { unfold θmax, calcθ₁ in poof.
          autorewrite with null in poof.
          apply Rmult_eq_reg_l in poof; try discrR.
          apply atan2_PI_impl in poof as [xrng yeq0].
          lra.
          assumption. }
    destruct tmub as [tmub|poof]; try lra.

    assert (0 < θmax) as zlttm. {
      unfold θmax, calcθ₁.
      arn.
      zltab.
      destruct (total_order_T 0 x); [destruct s|].
      apply atan2Q1; try assumption.
      rewrite <- e.
      rewrite atan2_PI2; try assumption.
      lra.
      specialize (atan2Q2 _ _ r zlty) as [atlb atub]; lra. }
    
    set (rz := (x² + y²) / (2 * y)).

    assert (2 * ra * y >= x² + y²) as nst. {
      apply Rnot_lt_ge.
      intro nst.
      apply nstt.
      apply condstraight.
      assumption. }

    assert (turning rz 0 0 0 x y) as phasez. {
      unfold turning, Tcx, Tcy.
      arn.
      rewrite Rsqr_minus.
      apply (Rplus_eq_reg_r (- rz² + 2 * y * rz)).
      setl (2 * y * rz).
      setr (x² + y²).
      unfold rz.
      field; lra. }

    assert (ru < rz <= ra) as [rzl rzu]. {
      split.
      unfold rz.
      apply straightcond in phaseu.
      apply (Rmult_lt_reg_l 2); try lra.
      apply (Rmult_lt_reg_l y); try lra.
      lrag phaseu.
      apply (Rmult_le_reg_l 2); try lra.
      apply (Rmult_le_reg_r y); try lra.
      unfold rz.
      apply Rge_le in nst.
      lrag nst. }

    assert (y <> 0) as yne0; try lra.
Qed.


Lemma minlength_path_turn_std :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu : turning ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (straight ra 0 0 0 x y /\ θc <= θ1 x y ra <= θd /\
       exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx ra 0 0 θv tvp) (Hy ra 0 0 θv tvp) o p
           /\  Dv <= Du)) \/
      (θ1 x y ra < θc /\ 
       (((ra <= (x² + y²)/(2*y) \/ y = 0)/\ θc < θmax) \/
        (y < 0 /\ θmax < 0)) /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θc twp) (Hy rw 0 0 θc twp) o p /\
           Dw <= Du)) \/
      (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= Rmax θc (θ1 x y ra) /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θmax twp) (Hy rw 0 0 θmax twp) o p /\
           Dw <= Du)).
Proof.
  intros * lt rur tur phaseu * nc u.
  
  specialize PI_RGT_0 as pigt0.

  assert (~(x = 0 /\ y = 0)) as no; try lra.


  assert (-2 * PI < θmax <= 2 * PI) as [tml tmu]. {
    unfold θmax, calcθ₁.
    arn.
    split.
    apply (Rmult_lt_reg_r (/2)); try lra.
    setl (-PI).
    setr (atan2 y x).
    apply atan2_bound; try assumption.
    apply (Rmult_le_reg_r (/2)); try lra.
    setr (PI).
    setl (atan2 y x).
    apply atan2_bound; try assumption. }

  assert (θmax / 2 <= PI) as tmub; try lra.
  assert (- PI < θmax / 2) as tmlb; try lra.

  assert (0 < θmax / 2 + 2 * PI) as tm2lb; try lra.
  assert (θmax / 2 - 2 * PI < 0) as tm2ub; try lra.

  assert (0 < ru) as zltru. lra.
  assert (0 < θu) as zlttu. {
    eapply zlt_mult.
    instantiate (1:=ru).
    destruct tup.
    assumption.
    left; assumption. }

  assert (ra <> 0) as rbne0. lra.
  assert (0 < ra) as zltrb. lra.
  assert (~ (ra < 0 /\ θmax = 2 * PI)) as trm. {
    unfold θmax.
    intros [rblt0 els].
    lra. }

  generalize nc; intro nc2.
  apply thmaxne0 in nc2.
  change (θmax <> 0) in nc2.

  specialize (ottb_compute_turning_t_s _ _ _ _ tup Du no phaseu u) as dudef.
  simpl in dudef.
  change (ru * θmax <= ru * θu < Rabs ru * 2 * PI) in dudef.
  rewrite (Rabs_pos_eq ru) in dudef; try lra.

  assert (0 < y) as zlty. {
    apply turningcond in phaseu.
    specialize (posss _ _ no) as zlt2.
    rewrite <- phaseu in zlt2.
    apply zlt_mult in zlt2; lra. }

  assert (0 < θmax) as zlttm. {
    unfold θmax, calcθ₁.
    arn.
    setl (2 * 0).
    apply Rmult_lt_compat_l; try lra.
    destruct (total_order_T 0 x); [destruct s|].
    - specialize (atan2Q1 _ _ r zlty) as [at2l at2u].
      lra.
    - rewrite <- e.
      rewrite (atan2_PI2 _ zlty).
      lra.
    - specialize (atan2Q2 _ _ r zlty) as [at2l at2u].
      lra. }
  
  destruct dudef as [tul tuu].
  apply Rmult_le_reg_l in tul; try lra.
  rewrite Rmult_assoc in tuu.
  apply Rmult_lt_reg_l in tuu; try lra.

  specialize (ottb_compute_turning_r_s _ _ _ _ tup Du phaseu no u) as rudef.

  specialize (intro_max_turning_path_std _ _ _ phaseu no) as [tup2 u2].
  unfold θmax in *; clear θmax.

  assert (y <> 0) as yne0; try lra.
  specialize (t1eqtm _ _ no yne0) as t1d.
  rewrite <- rudef in t1d.
  set (θmax := calcθ₁ 0 0 0 x y) in *.
  set (Du2 := {| nonneg := ru * θmax; cond_nonneg := nna ru θmax tup2 |}) in *.
  change (path_segment Du2 (Hx ru 0 0 θmax tup2) (Hy ru 0 0 θmax tup2) o p)
    in u2.
  
  rename tup into tup'.
  generalize tup2; intro tup.
  rewrite <- t1d in tup.

  
  assert ((straight ra 0 0 0 x y)
          \/ ~ straight ra 0 0 0 x y) as [stt | nstt]. {
    unfold straight.
    destruct (Rlt_dec (ra²) ((x - Tcx ra 0 0)² +
                             (y - Tcy ra 0 0)²)).
    left; assumption.
    right; assumption. }
  
  + (* introduce ra path *)
    specialize (intro_r_path_std _ _ _ stt nc2 rbne0 trm) as [rtp [dnnpf v]].
    set (θa := θ1 x y ra) in *.
    set (La := ra * θa + calcL ra 0 0 0 x y θa) in *.
    set (Da := {| nonneg := La; cond_nonneg := dnnpf |}) in *.
    change (path_segment Da (Hx ra 0 0 θa rtp) (Hy ra 0 0 θa rtp) o p) in v.

    specialize (ottb_compute_straight_r
                  _ _ _ _ _ _ _ rtp _ stt v) as rvdef.
    autorewrite with null in *.
    specialize (ottb_tinrng _ _ _ _ _ _ _ rtp Da stt v) as t1vrng.
    simpl in t1vrng.
    change ((0 < θmax /\ (θmax / 2 < θ1 x y ra < θmax \/
                          -2 * PI < θ1 x y ra < θmax / 2 - 2 * PI)) \/
            (θmax < 0 /\ (θmax < θ1 x y ra < θmax / 2 \/
                          θmax / 2 + 2 * PI < θ1 x y ra < 2 * PI))) in t1vrng.

    destruct rur as [[ralt |raeq] ruub].
    2 : { rewrite raeq in *.
          exfalso.
          clear - stt phaseu.
          apply straightcond in stt.
          apply turningcond in phaseu.
          rewrite phaseu in stt.
          lra. }

    (* ra < ru (reminder: θc and (θ1 x y ra) are not related) *)
    destruct (Rlt_dec (θ1 x y ra) θc) as [t1rbletd| t1rbgttd].
    ++ right.
       change (θa < θc) in t1rbletd.

       assert (0 < θa) as zltta. {
         destruct rtp.
         clear - lt r.
         apply (Rmult_lt_reg_l ra); try assumption.
         setl 0.
         assumption. } 

       assert (0 < θc) as zlttd; try lra.
       
       change (0 < θmax /\ (θmax / 2 < θa < θmax \/ -2 * PI < θa < θmax / 2 - 2 * PI) \/
               θmax < 0 /\ (θmax < θa < θmax / 2 \/ θmax / 2 + 2 * PI < θa < 2 * PI)) in t1vrng.

       destruct (Rge_dec θc θmax).
       {
         apply Rge_le in r.
         right.
         split; try lra.
         split.
         unfold Rmax; destruct Rle_dec; lra.
         
         exists Du2, ru, tup2.
         split.
         lra.
         split.
         apply u2.
         simpl.

         specialize (ottb_path_distance _ _ _ _ _ _ _ _ _ u) as [[trn dst] | [stu dst]].
         simpl.
         rewrite dst.
         rewrite <- eqv_calcs.
         unfold θmax.
         right.
         reflexivity.
         arn.
         assumption.
         assumption.

         exfalso.
         apply straightcond in stu.
         apply turningcond in phaseu.
         clear - stu phaseu.
         lra. }
       
       apply Rnot_ge_lt in n.
       set (rc := (x * sin θc - y * cos θc) / (1 - cos θc)) in *.
       assert (ra < rc) as rdltrb. {
         rewrite rvdef.
         unfold rc.
         destruct t1vrng as [[tordv [vpr|vnr]]|[tord poof]]; try lra.
         apply ottb_bigger_theta_bigger_r_std; try assumption.
         split; try lra.
         destruct vpr as [vprl vprh].
         change (θmax / 2 < θc).
         apply (Rlt_le_trans _ θa); lra.
         change (θc < θmax).
         assumption.
         lra. }
       
       destruct tur as [[tclttu | tceqtu] tuletc].
       +++ assert (rc < ru) as ralerd. {
             rewrite rudef.
             unfold rc.
             destruct t1vrng as [[tordv [vpr|vnr]]|[tord poof]]; try lra.

             rewrite Rplus_comm.
             rewrite tmax_radius; try lra.
             change ((x * sin θc - y * cos θc) / (1 - cos θc) <
                     (x * sin θmax - y * cos θmax) / (1 - cos θmax)).
             destruct vpr as [vprl vprh].
             apply ottb_bigger_theta_bigger_r_ep_std; try lra.
             split; try lra.
             apply (Rle_trans _ θa); try lra.
             left; assumption.
             left; assumption.
             change (θmax / 2 <= θmax <= θmax).
             split; lra. }
           
           assert (θmax / 2 < θc < θmax \/ -2 * PI < θc < θmax / 2 - 2 * PI \/
                   θmax < θc < θmax / 2 \/ θmax / 2 + 2 * PI < θc < 2 * PI) as tdr; try lra.
           unfold θmax in tdr.
           
           assert (straight rc 0 0 0 x y) as srd. {
             apply turningcond in phaseu.
             apply condstraight.
             rewrite <- phaseu.
             repeat rewrite Rmult_assoc.
             repeat rewrite (Rmult_comm _ y).
             repeat rewrite <- Rmult_assoc.
             apply Rmult_lt_compat_l; try lra. }
           
           assert (~ (rc < 0 /\ calcθ₁ 0 0 0 x y = 2 * PI)) as rdc; try (intros [rdlt0 poof]; lra).
           specialize (intro_theta_path_std x y θc tdr srd rdc) as [trd [lengt0 d]].
           change (0 < rc * θc < Rabs rc * 2 * PI) in trd.
           change (0 <= rc * θc + calcL rc 0 0 0 x y θc) in lengt0.
           change (path_segment
                     {| nonneg := rc * θc + calcL rc 0 0 0 x y θc;
                        cond_nonneg := lengt0 |} (Hx rc 0 0 θc trd) (Hy rc 0 0 θc trd) o p) in d.
           set (Lc := rc * θc + calcL rc 0 0 0 x y θc) in *.
           set (Dc := {| nonneg := Lc; cond_nonneg := lengt0 |}) in *.
           
           specialize (ottb_compute_straight_t _ _ _ _ _ _ _ trd Dc srd d) as dddef.
           simpl in dddef.
           autorewrite with null in *.
           
           assert (0 < rc * (θ1 x y rc) < Rabs rc * 2 * PI) as trd'. {
             rewrite <- dddef.
             assumption. }
           
           set (f := (fun t => 0 < rc * t < Rabs rc * 2 * PI)).
           assert (existT f θc trd =
                   existT f (θ1 x y rc) trd') as tc1. {
             clear - trd' trd dddef.
             apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
               try assumption. }
           left.
           split; try lra.
           split; try lra.

           exists Dc, rc, trd.
           split; [lra|].
           split; try assumption.
           left.

           eapply ottb_bigger_r_longer_path_turn_std.
           apply no.
           apply phaseu.
           assert (0 < rc) as zltrc; try lra.
           apply zltrc.
           assumption.
           apply d.
           apply u.
           
       +++ assert (0 < ru * θc < Rabs ru * 2 * PI) as tup''. {
             rewrite tceqtu.
             assumption. }
           
           set (f := (fun t => 0 < ru * t < Rabs ru * 2 * PI)).
           assert (existT f θu tup' =
                   existT f θc tup'') as tc1. {
             clear - tup' tup'' tceqtu.
             apply ProofIrrelevance.ProofIrrelevanceTheory.subsetT_eq_compat;
               auto. }
           dependent rewrite tc1 in u.
           exfalso.
           lra.

    ++ left.
       apply Rnot_lt_le in t1rbgttd.
       (* case1 *)
       split; try assumption.
       split.
       destruct t1vrng as [[zlttm2 rst] | [tmlt0 poof]]; try lra.
       destruct rst as [[rst1l rst1u] | rst2].
       unfold θa in *; lra.
       unfold θa in *; lra.

       exists Da, (θ1 x y ra), rtp.
       split.
       +++ split; try assumption.
           apply (Rle_trans _ (θ1 x y ru)); try lra.
                
       +++ split; auto.
           left.
           apply (ottb_bigger_r_longer_path_turn_std
                    _ _ _ _ Da Du _ _ no phaseu lt rtp ralt tup' v u).
           
  + right.
    destruct rur as [[rult |rueq] ruub ].

    exfalso.
    apply nstt.
    apply condstraight.
    apply turningcond in phaseu.
    rewrite <- phaseu.
    repeat rewrite Rmult_assoc.
    repeat rewrite (Rmult_comm _ y).
    repeat rewrite <- Rmult_assoc.
    apply Rmult_lt_compat_l; try lra.

    right.
    (* case3 *)
    split; try lra.
    split.
    rewrite rueq, t1d.
    unfold Rmax; destruct Rle_dec; lra.

    exists Du2, ru, tup2.
    split ; try lra.
    split; try assumption.
    simpl.

    specialize (ottb_path_distance _ _ _ _ _ _ _ _ _ u) as [[trn dst] | [stt dst]].
    simpl.
    rewrite dst.
    rewrite <- eqv_calcs.
    unfold θmax.
    right.
    reflexivity.
    arn.
    assumption.
    assumption.

    exfalso.
    apply straightcond in stt.
    apply turningcond in phaseu.
    clear - stt phaseu.
    lra.
Qed.


Theorem minlength_path_std :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (straight ra 0 0 0 x y /\ θc <= θ1 x y ra <= θd /\
       exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx ra 0 0 θv tvp) (Hy ra 0 0 θv tvp) o p
           /\  Dv <= Du)) \/
      (θ1 x y ra < θc /\ 
       (((ra <= (x² + y²)/(2*y) \/ y = 0)/\ θc < θmax) \/
        (y < 0 /\ θmax < 0)) /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θc twp) (Hy rw 0 0 θc twp) o p /\
           Dw <= Du)) \/
      (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= Rmax θc (θ1 x y ra) /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θmax twp) (Hy rw 0 0 θmax twp) o p /\
           Dw <= Du)).
Proof.
  intros * zltra rurng turng * npx psu.
  generalize psu; intro phaseu.
  apply ottb_r_constraints in phaseu as [ phaseu|phaseu].
  eapply minlength_path_turn_std; eassumption.
  specialize minlength_path_straight_std as [case1 |case2]; try eassumption.
  left; assumption.
  right; left; assumption.
Qed.

Corollary minlength_path_std_arg1_impl_not_arg2 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (straight ra 0 0 0 x y /\ θc <= θ1 x y ra <= θd) ->
      ~ (θ1 x y ra < θc /\ 
       (((ra <= (x² + y²)/(2*y) \/ y = 0)/\ θc < θmax) \/
        (y < 0 /\ θmax < 0))).
Proof.
  intros until 4.
  intros u [sra [tcleta taletd]].
  intros [talttc [[[raltrm | yeq0] tclttm] | [ylt0 tmlt0]]];
  apply straightcond in sra;
  lra.
Qed.


Corollary minlength_path_std_arg2_impl_not_arg1 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (θ1 x y ra < θc /\ 
       (((ra <= (x² + y²)/(2*y) \/ y = 0)/\ θc < θmax) \/
        (y < 0 /\ θmax < 0))) ->
      ~ (straight ra 0 0 0 x y /\ θc <= θ1 x y ra <= θd).
Proof.
  intros until 4.
  intros u [talttc [[[raltrm | yeq0] tclttm] | [ylt0 tmlt0]]];
  intros [sra [tcleta taletd]];
  apply straightcond in sra; try lra.
Qed.

Corollary minlength_path_std_arg2_impl_not_arg3 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (θ1 x y ra < θc /\ 
       (((ra <= (x² + y²)/(2*y) \/ y = 0)/\ θc < θmax) \/
        (y < 0 /\ θmax < 0))) ->
      ~ (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= Rmax θc (θ1 x y ra)).
Proof.
  intros until 4.
  intros u [talttc [[[raltrm | yeq0] tclttm] | [ylt0 tmlt0]]];
  intros [[ralerm rmlerb] tmltrm];
  unfold Rmax in *; destruct Rle_dec; try lra.
  specialize (posss x y ltac:(lra)) as ps.
  assert ((x² + y²) / (2 * y) < 0) as rmlt0. {
    setl (-((x² + y²) / (2 * (-y)))); try lra.
    apply (Rmult_lt_reg_r (2 * - y)); try zltab.
    setl (- (x² + y²)); try lra. }
  lra.
Qed.

Corollary minlength_path_std_arg3_impl_not_arg2 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= Rmax θc (θ1 x y ra)) ->
      ~ (θ1 x y ra < θc /\ 
         (((ra <= (x² + y²)/(2*y) \/ y = 0)/\ θc < θmax) \/
          (y < 0 /\ θmax < 0))).
Proof.
  intros until 4.
  intros u [[raltrm1 rmltrb] tmletcta].
  intros [talttc [[[raltrm | yeq0] tclttm] | [ylt0 tmlt0]]];
    unfold Rmax in tmletcta;
    destruct Rle_dec; try lra.
  specialize (posss x y ltac:(lra)) as ps.
  assert ((x² + y²) / (2 * y) < 0) as rmlt0. {
    setl (-((x² + y²) / (2 * (-y)))); try lra.
    apply (Rmult_lt_reg_r (2 * - y)); try zltab.
    setl (- (x² + y²)); try lra. }
  lra.
Qed.

Corollary minlength_path_std_arg1_impl_not_arg3 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (straight ra 0 0 0 x y /\ θc <= θ1 x y ra <= θd) ->
      ~ (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= Rmax θc (θ1 x y ra)).
Proof.
  intros until 4.
  intros u [sra [tcleta taletd]].
  apply straightcond in sra.
  intros [[ralerm rmlerb] tmltrm];
    unfold Rmax in *; destruct Rle_dec; try lra.

  apply condstraight in sra.
  assert (ra <> 0) as rane0; try lra.
  specialize (theta1_rsgn_bnd _ _ _ rane0 sra) as [L R].
  specialize (L lt); clear R.
  destruct L as [zleta talt2pi].

  destruct (total_order_T y 0); [destruct s|].

  + specialize (posss x y ltac:(lra)) as ps.
    assert ((x² + y²) / (2 * y) < 0) as rmlt0. {
      setl (-((x² + y²) / (2 * (-y)))); try lra.
      apply (Rmult_lt_reg_r (2 * - y)); try zltab.
      setl (- (x² + y²)); try lra. }
    lra.

  + clear - tmltrm talt2pi e nc.
    unfold θmax in *.
    rewrite calcth1_atan2_s in tmltrm.
    rewrite e in *; clear e.
    assert (x < 0) as xlt0; try lra.
    rewrite atan2_PI in tmltrm; try assumption.
    lra.

  + assert (~ (x = 0 /\ y = 0)  ) as no by lra.
    specialize (t1eqtm _ _ no ltac:(lra)) as tmid.
    change (θ1 x y ((y² + x²) / (2 * y)) = θmax) in tmid.
    rewrite Rplus_comm in tmid.
    rewrite <- tmid in tmltrm.
    set (rm := (x² + y²) / (2 * y)) in *.
    apply straightcond in sra.
    assert (ra < rm) as raltrm. {
      unfold rm.
      apply (Rmult_lt_reg_r (2 * y)).
      zltab.
      lrag sra. }
    clear ralerm.

    apply condstraight in sra.
    specialize (intro_r_path_std _ _ _ sra) as [rta [Dagt0 a]].
    apply thmaxne0; lra.
    lra.
    lra.
    set (Da := {| nonneg := ra * θ1 x y ra +
                            calcL ra 0 0 0 x y (θ1 x y ra); cond_nonneg := Dagt0 |}) in a.
    change (path_segment Da (Hx ra 0 0 (θ1 x y ra) rta) (Hy ra 0 0 (θ1 x y ra) rta) o p) in a.

    specialize (ottb_compute_straight_r_s _ _ _ _ rta Da sra a) as radef.

    assert (0 < θmax) as zlttm. {
      unfold θmax.
      rewrite thms.
      setl (2 * 0).
      apply Rmult_lt_compat_l; try lra.
      destruct (total_order_T 0 x) as [[zltx|zeqx] |xlt0].
      apply atan2Q1; assumption.
      rewrite <- zeqx, atan2_PI2; lra.
      specialize (atan2Q2 _ _ xlt0 r0) as [q2rl q2ru].
      lra. }
      
    specialize (ottb_tinrng _ _ _ _ _ _ _ rta Da sra a)
      as [quad | poof] ;  try (unfold θmax in *; lra).
Qed.

Corollary minlength_path_std_arg3_impl_not_arg1 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0)),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= Rmax θc (θ1 x y ra)) ->
      ~(straight ra 0 0 0 x y /\ θc <= θ1 x y ra <= θd).
Proof.
  intros until 4.
  intros u [[ralerm rmlerb] tmltrm].
  intros [sra [tcleta taletd]];
    apply straightcond in sra;
    unfold Rmax in *; destruct Rle_dec; try lra.

  apply condstraight in sra.
  assert (ra <> 0) as rane0; try lra.
  specialize (theta1_rsgn_bnd _ _ _ rane0 sra) as [L R].
  specialize (L lt); clear R.
  destruct L as [zleta talt2pi].

  destruct (total_order_T y 0); [destruct s|].

  + specialize (posss x y ltac:(lra)) as ps.
    assert ((x² + y²) / (2 * y) < 0) as rmlt0. {
      setl (-((x² + y²) / (2 * (-y)))); try lra.
      apply (Rmult_lt_reg_r (2 * - y)); try zltab.
      setl (- (x² + y²)); try lra. }
    lra.

  + clear - tmltrm talt2pi e nc.
    unfold θmax in *.
    rewrite calcth1_atan2_s in tmltrm.
    rewrite e in *; clear e.
    assert (x < 0) as xlt0; try lra.
    rewrite atan2_PI in tmltrm; try assumption.
    lra.

  + assert (~ (x = 0 /\ y = 0)  ) as no by lra.
    specialize (t1eqtm _ _ no ltac:(lra)) as tmid.
    change (θ1 x y ((y² + x²) / (2 * y)) = θmax) in tmid.
    rewrite Rplus_comm in tmid.
    rewrite <- tmid in tmltrm.
    set (rm := (x² + y²) / (2 * y)) in *.
    apply straightcond in sra.

    assert (ra < rm) as raltrm. {
      unfold rm.
      apply (Rmult_lt_reg_r (2 * y)).
      zltab.
      lrag sra. }
    clear ralerm.

    apply condstraight in sra.
    specialize (intro_r_path_std _ _ _ sra) as [rta [Dagt0 a]].
    apply thmaxne0; lra.
    lra.
    lra.
    set (Da := {| nonneg := ra * θ1 x y ra +
                            calcL ra 0 0 0 x y (θ1 x y ra); cond_nonneg := Dagt0 |}) in a.
    change (path_segment Da (Hx ra 0 0 (θ1 x y ra) rta) (Hy ra 0 0 (θ1 x y ra) rta) o p) in a.

    specialize (ottb_compute_straight_r_s _ _ _ _ rta Da sra a) as radef.

    assert (0 < θmax) as zlttm. {
      unfold θmax.
      rewrite thms.
      setl (2 * 0).
      apply Rmult_lt_compat_l; try lra.
      destruct (total_order_T 0 x) as [[zltx|zeqx] |xlt0].
      apply atan2Q1; assumption.
      rewrite <- zeqx, atan2_PI2; lra.
      specialize (atan2Q2 _ _ xlt0 r0) as [q2rl q2ru].
      lra. }
      
    specialize (ottb_tinrng _ _ _ _ _ _ _ rta Da sra a)
      as [quad | poof] ;  try (unfold θmax in *; lra).
Qed.  

(* end hide *)

(** Theorem 10 (Maximum bearing-constrained path length) from the paper. *)
Theorem maxlength_path :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (nc : θmax <> 0),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (straight rb θ₀ x₀ y₀ x₁ y₁ /\ θ1 x y rb <= θd /\
       exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx rb θ₀ x₀ θv tvp) (Hy rb θ₀ y₀ θv tvp) o p
           /\ Du <= Dv)) \/
      (((θd < θmax /\ ra <= (x² + y²)/(2*y) <= rb)\/
        (straight rb θ₀ x₀ y₀ x₁ y₁ /\ θd < θ1 x y rb)) /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw θ₀ x₀ θd twp) (Hy rw θ₀ y₀ θd twp) o p /\
           Du <= Dw)) \/
      (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= θd /\
       exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw θ₀ x₀ θmax twp) (Hy rw θ₀ y₀ θmax twp) o p /\
           Du <= Dw)).
Proof.
  intros until 5.
  intro u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  unfold x, y in *; clear x y.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  set (θmax := calcθ₁ 0 0 0 x y) in *.

  assert (~(0 <= x /\ y = 0)) as npx. {
    intros [zlex yeq0].
    apply nc.
    unfold θmax.
    rewrite thms, yeq0.
    destruct zlex as [zltx |zeqx].
    rewrite atan2_0.
    field.
    assumption.
    exfalso.
    
    specialize (ottb_r_constraints _ _ _ _ _ _ _ _ tup u) as [phaseu|phaseu];
      [apply turningcond in phaseu|apply straightcond in phaseu];
    rewrite <- zeqx, yeq0 in phaseu;
    autorewrite with null in phaseu;
    try lra.

    assert (y₁ - y₀ = x * sin θ₀ + y * cos θ₀) as y1y0. {
      unfold x, y.
      setr ((y₁ - y₀) * ((sin θ₀)² + (cos θ₀)²)).
      rewrite sin2_cos2.
      field. }

    assert (x₁ - x₀ = x * cos θ₀ - y * sin θ₀) as x1x0. {
      unfold x, y.
      setr ((x₁ - x₀) * ((sin θ₀)² + (cos θ₀)²)).
      rewrite sin2_cos2.
      field. }
    rewrite <- zeqx in y1y0, x1x0.
    rewrite yeq0 in y1y0, x1x0.
    autorewrite with null in y1y0, x1x0.
    lra. }

  specialize (maxlength_path_std _ _ _ _ _ _ Du ru θu tup lt rur tur npx u)
    as [[g1 [g2 [Dv [pv [tvp v]]]]] |
        [[g [Dv [pv [tvp v]]]] |
         [g1 [ g2 [Dv [pv [tvp v]]]]]]].
  left.
  split; try (apply rot_straight; apply g1).
  split; try (assumption).
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
  right; left.
  split.
  destruct g as [[g1 g2]| [g3 g4]].
  left; split; assumption.
  right; split; try assumption.
  apply rot_straight; assumption.
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
  right; right.
  split; try assumption.
  split; try assumption.
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.

(** Theorem 9 (Minimum bearing-constrained path length) from the paper. *)

Theorem minlength_path :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (nc : θmax <> 0),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (straight ra θ₀ x₀ y₀ x₁ y₁ /\ θc <= θ1 x y ra <= θd /\
       exists Dv θv tvp,
         (θc <= θv <= θd /\
          path_segment Dv (Hx ra θ₀ x₀ θv tvp) (Hy ra θ₀ y₀ θv tvp) o p
          /\  Dv <= Du)) \/
      (θ1 x y ra < θc /\ 
       (((ra <= (x² + y²)/(2*y) \/ y = 0)/\ θc < θmax) \/
        (y < 0 /\ θmax < 0)) /\
       exists Dw rw twp,
         (ra <= rw <= rb /\
          path_segment Dw (Hx rw θ₀ x₀ θc twp) (Hy rw θ₀ y₀ θc twp) o p /\
          Dw <= Du)) \/
      (ra <= (x² + y²)/(2*y) <= rb /\ θmax <= Rmax θc (θ1 x y ra) /\
       exists Dw rw twp,
         (ra <= rw <= rb /\
          path_segment Dw (Hx rw θ₀ x₀ θmax twp) (Hy rw θ₀ y₀ θmax twp) o p /\
          Dw <= Du)).
Proof.
  intros until 5.
  intro u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  unfold x, y in *; clear x y.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *.
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *.
  set (θmax := calcθ₁ 0 0 0 x y) in *.

  assert (~(0 <= x /\ y = 0)) as npx. {
    intros [zlex yeq0].
    apply nc.
    unfold θmax.
    rewrite thms, yeq0.
    destruct zlex as [zltx |zeqx].
    rewrite atan2_0.
    field.
    assumption.
    exfalso.
    
    specialize (ottb_r_constraints _ _ _ _ _ _ _ _ tup u) as [phaseu|phaseu];
      [apply turningcond in phaseu|apply straightcond in phaseu];
    rewrite <- zeqx, yeq0 in phaseu;
    autorewrite with null in phaseu;
    try lra.

    assert (y₁ - y₀ = x * sin θ₀ + y * cos θ₀) as y1y0. {
      unfold x, y.
      setr ((y₁ - y₀) * ((sin θ₀)² + (cos θ₀)²)).
      rewrite sin2_cos2.
      field. }

    assert (x₁ - x₀ = x * cos θ₀ - y * sin θ₀) as x1x0. {
      unfold x, y.
      setr ((x₁ - x₀) * ((sin θ₀)² + (cos θ₀)²)).
      rewrite sin2_cos2.
      field. }
    rewrite <- zeqx in y1y0, x1x0.
    rewrite yeq0 in y1y0, x1x0.
    autorewrite with null in y1y0, x1x0.
    lra. }

  specialize (minlength_path_std _ _ _ _ _ _ Du ru θu tup lt rur tur npx u)
    as [[g1 [g2 [Dv [pv [tvp v]]]]] |
        [[g1 [g2 [Dv [pv [tvp v]]]]] |
         [g1 [ g2 [Dv [pv [tvp v]]]]]]].
  left.
  split; try (apply rot_straight; apply g1).
  split; try (assumption).
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
  right; left.
  split; try assumption.
  split; try assumption.
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
  right; right.
  split; try assumption.
  split; try assumption.
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.

(* begin hide *)

Lemma trigeqvx2 : forall θ,
    ((1 - cos θ)² + (sin θ)² * (sin θ)² + (sin θ)² * (1 - cos θ)²
       - 2 * (1 - cos θ) * sin θ * sin θ) * (1 + cos θ) =
    ((sin θ)² - cos θ * (sin θ)²).
Proof.
  intros.
  unfold Rsqr.
  setl (1 - cos θ
        - ((sin θ)² + (cos θ)²)
        - sin θ * sin θ * cos θ
        + cos θ * cos θ * cos θ
        + sin θ * sin θ * ((sin θ)² + (cos θ)²)
        + sin θ * sin θ * cos θ * ((sin θ)² + (cos θ)²)
       ).
  rewrite sin2_cos2.
  arn.
  setl (- cos θ
        + cos θ * cos θ * cos θ
        + (sin θ)²).
  apply (Rplus_eq_reg_r (- (sin θ)²)).
  setl (- cos θ * ( 1 - (cos θ)²)).
  setr (- cos θ * (sin θ)²).
  specialize (sin2_cos2 θ) as s2c2.
  apply (Rplus_eq_compat_r (- (cos θ)²)) in s2c2.
  assert ((sin θ)² = 1 - (cos θ)²) as id2; try (lrag s2c2).
  rewrite <- id2.
  reflexivity.
Qed.


Lemma trigeqvy2 : forall θ,
    ((1 - cos θ)² + (cos θ)² * (sin θ)² + (cos θ)² * (1 - cos θ)² +
     2 * (1 - cos θ) * cos θ * (1 - cos θ)) * (1 + cos θ) =
    (1 + cos θ)² - cos θ * (1 + cos θ)².
Proof.
  intros.
  unfold Rsqr.
  setl (1 + cos θ
        - 2 * (cos θ)²
        - 2 * (cos θ)² * cos θ
        + (cos θ)² * ((sin θ)² + (cos θ)²)
        + (cos θ)² * cos θ * ((sin θ)² + (cos θ)²)
       ).
  rewrite sin2_cos2.
  setl (1 + cos θ - (cos θ)² - (cos θ)² * cos θ).
  setr (1 + cos θ - (cos θ)² - (cos θ)² * cos θ).
  reflexivity.
Qed.
  
Lemma trigeqvxy : forall θ,
    ((1 - cos θ) * cos θ * sin θ - sin θ * sin θ * cos θ * sin θ -
     sin θ * (1 - cos θ) * cos θ * (1 - cos θ) - (1 - cos θ) * sin θ * (1 - cos θ)) * 
    (1 + cos θ) = (cos θ * (1 + cos θ) * sin θ - (1 + cos θ) * sin θ).
Proof.
  intros.
  unfold Rsqr.
  setl (- sin θ
        + sin θ * cos θ
        + 2 * sin θ * cos θ * cos θ
        - sin θ * cos θ * ((sin θ)² + (cos θ)²)
        - sin θ * cos θ * cos θ * ((sin θ)² + (cos θ)²)
       ).
  rewrite sin2_cos2.
  arn.
  setl (cos θ * (1 + cos θ) * sin θ - (1 + cos θ) * sin θ).
  reflexivity.
Qed.





Lemma linear2form : forall x y θ,
    cos (θ/2) <> 0 -> 
    (x * (1 - cos θ) - (x * sin θ - y * cos θ) * sin θ)² +
    (y * (1 - cos θ) - (x * sin θ - y * cos θ) * (1 - cos θ))² =
    4 * (sin (θ / 2))² * (y * cos(θ / 2) - x * sin(θ / 2))².
Proof.
  intros.
  setr (4 * (sin (θ / 2))² * (cos (θ / 2))² * (y  - x * sin (θ / 2) / cos (θ / 2))²); try assumption.
  replace (y - x * sin (θ / 2) / cos (θ / 2)) with (y - x * tan (θ / 2)); try assumption.
  2 : { unfold tan; field; assumption. }
  rewrite sint22, cost22, tant2; try assumption.
  rewrite <- RmultRinv.
  apply (Rmult_eq_reg_r (1 + cos θ));
    [|rewrite cost2_cost in H; intro; apply H; lra].
  setr ((1 - cos θ) * (y * (1 + cos θ) - x * sin θ)²);
    [rewrite cost2_cost in H; intro; apply H; lra |].

  repeat rewrite Rsqr_minus at 1.
  repeat rewrite Rmult_minus_distr_r.
  repeat rewrite Rsqr_minus at 1.
  repeat rewrite Rsqr_mult.
  setl (x² * (((1 - cos θ)²
              + (sin θ)² * (sin θ)²
              + (sin θ)² * (1 - cos θ)²
                - 2 * (1 - cos θ) * sin θ * sin θ) * (1 + cos θ))
        + y² * (((1 - cos θ)²
                + (cos θ)² * (sin θ)²
                + (cos θ)² * (1 - cos θ)²
                + 2 * (1 - cos θ) * cos θ * (1 - cos θ)) * (1 + cos θ))
        + 2 * x * y * (((1 - cos θ) * cos θ * sin θ
                       - sin θ * sin θ * cos θ * sin θ
                       - sin θ * (1 - cos θ) * cos θ * (1 - cos θ)
                       - (1 - cos θ) * sin θ * (1 - cos θ)) * (1 + cos θ))
       ).

  setr (x² * ((sin θ)²
              - cos θ * (sin θ)²)
        + y² * ((1 + cos θ)²
                - cos θ * (1 + cos θ)²)
        + 2 * x * y * (cos θ * (1 + cos θ) * sin θ
                       - (1 + cos θ) * sin θ)
       ).

  rewrite trigeqvx2.
  rewrite trigeqvy2.
  rewrite trigeqvxy.
  reflexivity.
Qed.



Lemma dist_linear_wave :
  forall x y θ,
    let r := (x * sin θ - y * cos θ) / (1 - cos θ) in
    cos θ < 1 ->
    - 1 < cos θ ->
    ((x - r * sin θ)² + (y - r * (1 - cos θ))²) = (x - y * cos (θ / 2) / sin (θ / 2))².
Proof.
  intros * costlt1 n1ltcost.
  assert (0 < 1 - cos θ) as pd; try lra.

  + assert (sin (θ / 2) <> 0) as st2ne0. {
    intro sint2eq0.
    generalize costlt1.
    change (~ cos θ < 1).
    apply Rle_not_lt.
    right.
    symmetry.
    apply sin_eq_0_0 in sint2eq0 as [k t2d].
    assert (θ = 2 * IZR k * PI) as td; try lra.
    rewrite <- (Rplus_0_l θ).
    rewrite td, cos_period1, cos_0.
    reflexivity. }
  
  unfold r.
  clear r.
  rewrite <- RmultRinv.
  
  setl (((x * (1 - cos θ) - (x * sin θ - y * cos θ) * sin θ)²  +
         (y * (1 - cos θ) - (x * sin θ - y * cos θ) * (1 - cos θ))²) * (/ (1 - cos θ))²);
    try lra.

  rewrite linear2form ; [| rewrite cost2_cost_not ; lra ].
  setl (4 * ((sin (θ / 2))²)² * (y * cos (θ / 2) * / sin (θ / 2) - x )² * (/ (1 - cos θ))²);
    try lra.
  rewrite sint22.
  setl ((y * cos (θ / 2) * / sin (θ / 2) - x)²); try lra.
  rewrite RmultRinv.
  rewrite Rsqr_neg.
  setl ((x - y * cos (θ/2) / sin (θ/2))²); try assumption.
  reflexivity.
Qed.

Lemma plane_wave_form_std :
  forall (D:nonnegreal) (x y r θc:R) rtp
         (rp : 0 < r)
         (no : ~ (x = 0 /\ y = 0))
         (phase : straight r 0 0 0 x y)
         (P : path_segment D (Hx r 0 0 θc rtp) (Hy r 0 0 θc rtp) (mkpt 0 0) (mkpt x y)),
  nonneg D = r * θc + Rabs (x - y * cos (θc / 2) / sin (θc / 2)).
Proof.
  intros.

  set (o := {| ptx := 0; pty := 0 |}) in *.
  set (p := {| ptx := x; pty := y |}) in *.
  specialize (not_colinear_s _ _ _ _ rtp D P) as nc.
  specialize (ottb_compute_r_s _ _ _ _ rtp D no P) as [[trn rd] | [str rd]];
    [apply turningcond in trn; apply straightcond in phase; lra| clear str].
  specialize (ottb_compute_straight_t_s _ _ _ _ rtp D phase P) as tcd.
  specialize (ottb_path_distance _ _ _ _ _ _ _ _ rtp P) as [[trn dd] | [str dd]];
    [apply turningcond in trn; apply straightcond in phase; lra| clear str].
  autorewrite with null in dd.
  replace (y - (r - r * cos θc)) with (y - r * (1 - cos θc)) in dd by lra.

  destruct (total_order_T y 0) as [[ylt0 | yeq0]| ygt0].
  + destruct (total_order_T x 0) as [xle0o| xgt0].
    ++ assert (x <= 0) as xle0; try (destruct xle0o; lra); clear xle0o.
       specialize (root_ordering_Q3 _ _ _ rp ylt0 xle0 phase) as [t1t2o [t2r [t1lb t1ub]]];
         clear t1t2o t2r.
       rewrite <- tcd in *.

       assert (cos θc < 1) as ctlt1. {
         rewrite <- cos_2PI.
         apply cos_increasing_1; lra. }
  
       assert (-1 < cos θc) as n1ltct. {
         rewrite <- cos_PI.
         apply cos_increasing_1; lra. }

       specialize (dist_linear_wave x y _ ctlt1 n1ltct) as dstid.
       rewrite <- rd in dstid.
       rewrite dstid in dd.
       rewrite sqrt_Rsqr_abs in dd.
       assumption.
    ++ assert (0 <= x) as zlex; try lra.
       specialize (root_ordering_Q4 _ _ _ rp ylt0 zlex phase) as [t1t2o [t2r [t1lb t1ub]]];
         clear t1t2o t2r.
       rewrite <- tcd in *.

       assert (cos θc < 1) as ctlt1. {
         rewrite <- cos_2PI.
         apply cos_increasing_1; lra. }
  
       assert (-1 < cos θc) as n1ltct. {
         rewrite <- cos_PI.
         apply cos_increasing_1; lra. }

       specialize (dist_linear_wave x y _ ctlt1 n1ltct) as dstid.
       rewrite <- rd in dstid.
       rewrite dstid in dd.
       rewrite sqrt_Rsqr_abs in dd.
       assumption.

  + destruct (total_order_T x 0) as [[xlt0 | xeq0]| xgt0]; try lra.
    specialize (root_ordering_nxarm _ _ _ rp yeq0 xlt0 phase) as [t1t2o [t2r [t1lb t1ub]]];
         clear t1t2o t2r.
       rewrite <- tcd in *.

       assert (cos θc < 1) as ctlt1. {
         rewrite <- cos_2PI.
         apply cos_increasing_1; lra. }
  
       assert (-1 < cos θc) as n1ltct. {
         rewrite <- cos_PI.
         apply cos_increasing_1; lra. }

       specialize (dist_linear_wave x y _ ctlt1 n1ltct) as dstid.
       rewrite <- rd in dstid.
       rewrite dstid in dd.
       rewrite sqrt_Rsqr_abs in dd.
       assumption.

  + destruct (total_order_T x 0) as [xle0| xgt0].
    ++ destruct (total_order_T (2 * r - y) 0) as [[top | arm]| bot].
       +++ (* top *)
         assert (x <= 0) as xle; try (destruct xle0; lra). clear xle0.
         specialize (root_ordering_Q2top _ _ _ rp top xle phase) as [t1t2o [[t1lb t1ub] t2r]];
           clear t1t2o t2r.
         rewrite <- tcd in *.
         
         assert (cos θc < 1) as ctlt1. {
           rewrite <- cos_0.
           apply cos_decreasing_1; lra. }
         
         assert (-1 < cos θc) as n1ltct. {
           rewrite <- cos_PI.
           apply cos_decreasing_1; lra. }
         
         specialize (dist_linear_wave x y _ ctlt1 n1ltct) as dstid.
         rewrite <- rd in dstid.
         rewrite dstid in dd.
         rewrite sqrt_Rsqr_abs in dd.
         assumption.
       +++ (* arm *)
         destruct xle0 as [xlt0 | xeq0].
         unfold θ1 in *.
         destruct total_order_T as [[z0 | z1] | z2]; try lra; clear z0.
         destruct total_order_T as [[z0 | z1] | z2]; try lra; clear z2.
         destruct total_order_T as [[z0 | z1] | z2]; try lra; clear z0.
         destruct total_order_T as [[z0 | z1] | z2]; try lra; clear z1.
         subst.
         autorewrite with null in *.
         replace (y - - (y * -1) / (1 - -1) * (1 - -1)) with 0 in dd by lra.
         rewrite <- (RmultRinv _ 1).
         autorewrite with null in *.
         rewrite sqrt_Rsqr_abs in dd.
         assumption.
         
         unfold θ1 in *.
         destruct total_order_T as [[z0 | z1] | z2]; try lra; clear z0.
         destruct total_order_T as [[z0 | z1] | z2]; try lra; clear z1.
         destruct total_order_T as [[z0 | z1] | z2]; try lra; clear z0.
         destruct total_order_T as [[z0 | z1] | z2]; try lra; clear z1.
         subst.

         exfalso.
         clear - phase.
         apply straightcond in phase.
         subst.
         autorewrite with null in *.
         replace (2 * (- (y * -1) / (1 - -1)) * y) with (y*y) in phase by lra.
         unfold Rsqr in phase.
         lra.
         
       +++ (* bottom *)
         assert (x <= 0) as xle; try (destruct xle0; lra). clear xle0.
         destruct xle as [xlt |xeq].
         specialize (root_ordering_Q2bot _ _ _ rp bot ygt0 xlt phase) as [t1t2o [[t1lb t1ub] t2r]];
           clear t1t2o t2r.
         rewrite <- tcd in *.
         
         assert (cos θc < 1) as ctlt1. {
           rewrite <- cos_2PI.
           apply cos_increasing_1; lra. }
         
         assert (-1 < cos θc) as n1ltct. {
           rewrite <- cos_PI.
           apply cos_increasing_1; lra. }
         
         specialize (dist_linear_wave x y _ ctlt1 n1ltct) as dstid.
         rewrite <- rd in dstid.
         rewrite dstid in dd.
         rewrite sqrt_Rsqr_abs in dd.
         assumption.

         (* x=0, 0 < y points are inside the turning circle, unreachable *)
         exfalso.
         clear - ygt0 bot xeq phase.
         apply straightcond in phase.
         subst.
         autorewrite with null in *.
         unfold Rsqr in phase.
         apply Rmult_lt_reg_r in phase; try assumption.
         lra.

    ++ destruct (total_order_T (2 * r - y) 0) as [[top | arm]| bot].
       +++ (* top *)
         assert (0 <= x) as xle; try lra. clear xgt0.
         specialize (root_ordering_Q1top _ _ _ rp top xle phase) as [t1t2o [[t1lb t1ub] t2r]];
           clear t1t2o t2r.
         rewrite <- tcd in *.
         
         assert (cos θc < 1) as ctlt1. {
           rewrite <- cos_0.
           apply cos_decreasing_1; lra. }
         
         assert (-1 < cos θc) as n1ltct. {
           rewrite <- cos_PI.
           apply cos_decreasing_1; lra. }
         
         specialize (dist_linear_wave x y _ ctlt1 n1ltct) as dstid.
         rewrite <- rd in dstid.
         rewrite dstid in dd.
         rewrite sqrt_Rsqr_abs in dd.
         assumption.
       +++ (* arm *)
         symmetry in arm.
         specialize (root_ordering_Q1arm _ _ _ rp arm ygt0 xgt0 phase) as [t2r [t1lb t1ub]];
           clear t2r.
         rewrite <- tcd in *.
         
         assert (cos θc < 1) as ctlt1. {
           rewrite <- cos_0.
           apply cos_decreasing_1; lra. }
         
         assert (-1 < cos θc) as n1ltct. {
           rewrite <- cos_PI.
           apply cos_decreasing_1; lra. }
         
         specialize (dist_linear_wave x y _ ctlt1 n1ltct) as dstid.
         rewrite <- rd in dstid.
         rewrite dstid in dd.
         rewrite sqrt_Rsqr_abs in dd.
         assumption.

       +++ (* bottom *)
         specialize (root_ordering_Q1bot _ _ _ rp bot ygt0 xgt0 phase) as [t1t2o [[t1lb t1ub] t2r]];
           clear t1t2o t2r.
         rewrite <- tcd in *.
         
         assert (cos θc < 1) as ctlt1. {
           rewrite <- cos_0.
           apply cos_decreasing_1; lra. }
         
         assert (-1 < cos θc) as n1ltct. {
           rewrite <- cos_PI.
           apply cos_decreasing_1; lra. }
         
         specialize (dist_linear_wave x y _ ctlt1 n1ltct) as dstid.
         rewrite <- rd in dstid.
         rewrite dstid in dd.
         rewrite sqrt_Rsqr_abs in dd.
         assumption.
Qed.


Lemma plane_wave_form_pre :
  forall (D:nonnegreal) (x₀ y₀ x₁ y₁ r θ₀ θc:R) rtp
         (rp : 0 < r)
         (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
         (phase : straight r θ₀ x₀ y₀ x₁ y₁)
         (P : path_segment D (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp) (mkpt x₀ y₀) (mkpt x₁ y₁)),
    let x := (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ in
    let y := - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ in
    nonneg D = r * θc + Rabs (x - y * cos (θc / 2) / sin (θc / 2)).
Proof.
  intros.
  unfold x, y; clear x y.
  apply path_stdR in P.
  apply straight_rot in phase.
  apply (notid_rot θ₀) in no.
  set (x := (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in *.
  set (y := - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in *.
  set (o := {| ptx := 0; pty := 0 |}) in *.
  set (p := {| ptx := x; pty := y |}) in *.
  specialize (not_colinear_s _ _ _ _ rtp D P) as nc.
  specialize (ottb_compute_r_s _ _ _ _ rtp D no P) as [[trn rd] | [str rd]];
    [apply turningcond in trn; apply straightcond in phase; lra| clear str].
  specialize (ottb_compute_straight_t_s _ _ _ _ rtp D phase P) as tcd.
  specialize (ottb_path_distance _ _ _ _ _ _ _ _ rtp P) as [[trn dd] | [str dd]];
    [apply turningcond in trn; apply straightcond in phase; lra| clear str].
  autorewrite with null in dd.
  eapply plane_wave_form_std; try assumption.
  Unshelve.
  assumption.
Qed.


Definition cot t := cos t / sin t.

(* end hide *)

Lemma plane_wave_part :
  forall (D:nonnegreal) (x₀ y₀ x₁ y₁ r θ₀ θc:R) rtp
         (rp : 0 < r)
         (no : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))               
         (phase : straight r θ₀ x₀ y₀ x₁ y₁)
         (P : path_segment D (Hx r θ₀ x₀ θc rtp) (Hy r θ₀ y₀ θc rtp) (mkpt x₀ y₀) (mkpt x₁ y₁)),
    let x := (x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀ in
    let y := - (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ in
    forall (valid : y * cot (θc / 2) > x), 
    nonneg D = r * θc + y * cot (θc / 2) - x.
Proof.
  intros.
  unfold cot in *.
  specialize (plane_wave_form_pre _ _ _ _ _ _ _ _ rtp rp no phase P) as Ddef.
  simpl in *.
  change (nonneg D = r * θc + Rabs (x - y * cos (θc / 2) / sin (θc / 2))) in Ddef.
  rewrite Rabs_left in Ddef; try lra.
Qed.

(* begin hide *)
Lemma product_inequalities : forall al a ah bl b bh,
    0 < al ->
    0 < bl ->
    al <= a <= ah ->
    bl <= b <= bh ->
    al * bl <= a * b <= ah * bh.
Proof.
  intros *.
  intros zltal zltbl arng brng.
  split.
  apply (Rle_trans _ (al * b));
    [apply Rmult_le_compat_l; lra|
     apply Rmult_le_compat_r; lra].
  apply (Rle_trans _ (ah * b));
    [apply Rmult_le_compat_r; lra|
     apply Rmult_le_compat_l; lra].
Qed.

(* end hide *)

Lemma bounded_turning_part_std :
  forall ra rb θc θd Du Da Db ru θu tup tap tbp
         (ragt : 0 < ra),
  forall (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd),
    let o := (mkpt 0 0) in
    let x := ra * sin θu in
    let y := ra * (1 - cos θu) in
      turning ru 0 0 0 x y -> 
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o (mkpt x y) -> 
    let xl := ra * sin θc in
    let yl := ra * (1 - cos θc) in
      turning ra 0 0 0 xl yl -> 
      path_segment Da (Hx ra 0 0 θc tap) (Hy ra 0 0 θc tap) o (mkpt xl yl) -> 
    let xh := rb * sin θd in
    let yh := rb * (1 - cos θd) in
      turning rb 0 0 0 xh yh -> 
      path_segment Db (Hx rb 0 0 θd tbp) (Hy rb 0 0 θd tbp) o (mkpt xh yh) -> 
      Da <= Du <= Db.
Proof.
  intros * zltra rur tur * tU U * tA A * tB B.

  assert (0 < ru) as rugt0; try lra.
  assert (0 < ra) as ragt0; try lra.
  assert (0 < rb) as rbgt0; try lra.

  assert (0 < θu < 2 * PI) as turng. {
    split.
    apply (Rmult_lt_reg_l ru); try lra.
    apply (Rmult_lt_reg_l ru); try lra.
    rewrite <- (Rabs_right ru) at 2; lra. }

  assert (0 < θc < 2 * PI) as tcrng. {
    split.
    apply (Rmult_lt_reg_l ra); try lra.
    apply (Rmult_lt_reg_l ra); try lra.
    rewrite <- (Rabs_right ra) at 2; lra. }

  assert (0 < θd < 2 * PI) as tdrng. {
    split.
    apply (Rmult_lt_reg_l rb); try lra.
    apply (Rmult_lt_reg_l rb); try lra.
    rewrite <- (Rabs_right rb) at 2; lra. }

  specialize (ottb_path_distance _ _ _ _ _ _ _ _ tup U) as [[tu Dud] |[sp rest]];
    [clear tu|clear - sp tU;
     apply straightcond in sp;
     apply turningcond in tU;
     lra].
  assert (~ (x = 0 /\ y = 0)) as no. {
    unfold x.
    unfold y.
    intros [lseq0 rseq0].
    apply Rmult_integral in lseq0; destruct lseq0 as [poof|seq0]; try lra.
    apply Rmult_integral in rseq0; destruct rseq0 as [poof|omceq0]; try lra.
    apply sin_eq_O_2PI_0 in seq0; try lra.
    destruct seq0 as [seq0 | [seq0 | seq0 ]] ; try lra.
    rewrite seq0, cos_PI in omceq0.
    lra. }
  rewrite <- eqv_calcs in Dud;
    [|arn; assumption|assumption].
  rewrite thms in Dud.
  assert (θu = 2 * atan2 y x) as tud. {
    symmetry.
    unfold x, y.
    apply chord_property; lra. }
  rewrite <- tud in Dud.
  rewrite Dud.

  specialize (ottb_path_distance _ _ _ _ _ _ _ _ tap A) as [[ta Dad] |[sp rest]];
    [clear ta|clear - sp tA;
     apply straightcond in sp;
     apply turningcond in tA;
     lra].
  assert (~ (xl = 0 /\ yl = 0)) as nol. {
    unfold xl.
    unfold yl.
    intros [lseq0 rseq0].
    apply Rmult_integral in lseq0; destruct lseq0 as [poof|seq0]; try lra.
    apply Rmult_integral in rseq0; destruct rseq0 as [poof|omceq0]; try lra.
    apply sin_eq_O_2PI_0 in seq0; try lra.
    destruct seq0 as [seq0 | [seq0 | seq0 ]] ; try lra.
    rewrite seq0, cos_PI in omceq0.
    lra. }
  rewrite <- eqv_calcs in Dad;
    [|arn; assumption|assumption].
  rewrite thms in Dad.
  assert (θc = 2 * atan2 yl xl) as tcd. {
    symmetry.
    unfold xl, yl.
    apply chord_property; lra. }
  rewrite <- tcd in Dad.
  rewrite Dad.

  specialize (ottb_path_distance _ _ _ _ _ _ _ _ tbp B) as [[tb Dbd] |[sp rest]];
    [clear tb|clear - sp tB;
     apply straightcond in sp;
     apply turningcond in tB;
     lra].
  assert (~ (xh = 0 /\ yh = 0)) as noh. {
    unfold xh.
    unfold yh.
    intros [lseq0 rseq0].
    apply Rmult_integral in lseq0; destruct lseq0 as [poof|seq0]; try lra.
    apply Rmult_integral in rseq0; destruct rseq0 as [poof|omceq0]; try lra.
    apply sin_eq_O_2PI_0 in seq0; try lra.
    destruct seq0 as [seq0 | [seq0 | seq0 ]] ; try lra.
    rewrite seq0, cos_PI in omceq0.
    lra. }
  rewrite <- eqv_calcs in Dbd;
    [|arn;assumption|assumption].
  rewrite thms in Dbd.
  assert (θd = 2 * atan2 yh xh) as tdd. {
    symmetry.
    unfold xh, yh.
    apply chord_property; lra. }
  rewrite <- tdd in Dbd.
  rewrite Dbd.

  apply product_inequalities ; lra.
Qed.
