(* begin hide *)
Require Import Reals.
Require Import Ranalysis5.
Require Import FunctionalExtensionality.
Require Import Coquelicot.Coquelicot.
Require Import Omega.
Require Import Lia.
Require Import Lra.
(*Require Import Field.  do we need this?*)
(* Require Import Ring.  do we need this?*)
Require Import atan2.
Require Import ttyp.
Require Import tdyn.
Require Import util.
Require Import strt.
Require Import strt2.
Require Import tlens.
Require Import incr_function_le_ep.
Require Import dtlen.

Open Scope R_scope.
Set Bullet Behavior "Strict Subproofs".

Axiom path_length_lower_bound : forall pathx pathy s0 s1 d,
    is_RInt (magnitude (Derive pathx) (Derive pathy)) s0 s1 d ->
    sqrt ((pathx s0 - pathx s1)² + (pathy s0 - pathy s1)²) <= d.

(* could have different parameterizations; not all unit velocity *)
Axiom path_length_straight_line : forall pathx pathy s0 s1,
    is_RInt (magnitude (Derive pathx) (Derive pathy)) s0 s1
            (sqrt ((pathx s0 - pathx s1)² + (pathy s0 - pathy s1)²)) ->
    (exists v,
        forall s, s0 < s < s1 ->
                  0 <= v s /\
                  (Derive pathx s = (pathx s1 - pathx s0) * v s /\
                   Derive pathy s = (pathy s1 - pathy s0) * v s)).

(* infinite hat *)

Lemma straight_neg1 x y r :
  r < 0 ->
  y > 0 ->
  straight r 0 0 0 x y. 
Proof.
  intros.
  apply condstraight.
  eapply Rlt_trans with (r2 := 0).
  - replace 0 with (2 * 0 * y) by ring.
    apply Rmult_lt_compat_r; lra.
  - apply posss; intro Q; destruct Q; subst; lra.
Qed.

Lemma straight_neg2 x y r :
  r > 0 ->
  y < 0 ->
  straight r 0 0 0 x y. 
Proof.
  intros.
  apply condstraight.
  eapply Rlt_trans with (r2 := 0).
  - replace 0 with (2 * r * 0) by ring.
    apply Rmult_lt_compat_l; lra.
  - apply posss; intro Q; destruct Q; subst; lra.
Qed.

Lemma full_path_dist_increasing_req0_s :
  forall (x y s : R)
         (not_forward : (~ (0 <= x /\ y = 0)))
         (phase : straight s 0 0 0 x y)
         (sgtr : 0 < s),
    let d := (fun t : R =>
                (if Rbar_le_dec 0 t
                 then t * θ1 x y t
                 else 0) +
                (sqrt (x² - (2 * t - y) * y))) in
    d 0 < d s.
Proof.
  intros.
  set (r := 1).
  assert (forall z,
             continuous (fun t => (sqrt (x² - (2 * t - y) * y))) z)
    as Q.
  { intros.
    apply continuous_sqrt_comp.
    apply (continuous_minus
             (fun t => x²)
             (fun t => (2 * t - y) * y)).
    - apply continuous_const.
    - apply (continuous_scal_l (fun t => (2 * t - y)) y).
      apply (continuous_minus
               (fun t => 2 * t)
               (fun t => y)).
      + apply (continuous_scal_r 2 (fun t => t) z).
        apply continuous_id.
      + apply continuous_const.
  }

  assert (continuous (fun t: R =>
                        if Rbar_le_dec 0 t
                        then t * (θ1 x y) t
                        else 0
                     ) 0).
  { rewrite reasonable_continuity; intros.
    assert (0 < Rmin (eps * /(2 * PI)) s).
    { apply Rmin_glb_lt; auto.
      apply Rmult_lt_0_compat; try lra.
      - apply cond_pos.
      - apply Rinv_0_lt_compat.
        apply Rgt_2PI_0.
    }
    exists (mkposreal _ H); intros; cbn in *.
    repeat destruct Rbar_le_dec; cbn in *.
    - replace (y0 * θ1 x y y0 - 0 * θ1 x y 0) with
          (y0 * θ1 x y y0) by lra.
      replace (y0 - 0) with y0 in H0 by lra.
      destruct r0.
      + apply Rmin_def in H0; destruct H0.
        apply Rabs_def2 in H0; destruct H0.
        apply Rabs_def2 in H2; destruct H2.
        assert (straight y0 0 0 0 x y) as Q0.
        { destruct (total_order_T 0 y) as [[P|EQ]|N].
          - eapply straight_r_dom1_std; eauto.
          - eapply straight_r_dom3_std; eauto.
          - apply straight_neg2; auto.
        }
        assert (Rabs (θ1 x y y0) < 2 * PI).
        { specialize (theta1_rng x y y0 ltac:(lra) Q0) as Q1.
          apply Rabs_def1; lra.
        }
        rewrite Rabs_mult.
        destruct eps; cbn in *.
        replace pos with ((pos * / (2 * PI)) * (2 * PI)).
        * eapply Rlt_trans with
              (r2 := (pos * / (2 * PI)) * Rabs (θ1 x y y0)).
          -- apply Rmult_lt_compat_r.
             ++ apply Rabs_pos_lt.
                apply nposx_t1ne0; auto; try lra.
                apply straightcond; assumption.
             ++ apply Rabs_def1; auto.
          -- apply Rmult_lt_compat_l; lra.
        * rewrite Rmult_assoc, Rinv_l; try ring.
          specialize Rgt_2PI_0 as TMP; lra.
      + subst.
        replace (0 * θ1 x y 0) with 0 by ring.
        rewrite Rabs_R0; apply cond_pos.
    - exfalso; apply n; lra.
    - replace (0 - 0 * θ1 x y 0) with 0 by ring.
      rewrite Rabs_R0.
      apply cond_pos.
    - replace (0 - 0) with 0 by ring.
      rewrite Rabs_R0.
      apply cond_pos.
  }
  
  assert (continuous d 0).
  { unfold d.
    apply (continuous_plus
             (fun t : R =>
                (if Rbar_le_dec 0 t
                 then t * θ1 x y t
                 else 0))); eauto.
  }
  assert (forall x0 : R,
             Rbar_le 0 x0 ->
             Rbar_le x0 s ->
             continuous d x0) as Q0.
  { cbn; intros.
    destruct H1, H2.
    - unfold d.
      apply (continuous_ext_loc
               _ (fun t => t * (θ1 x y) t +
                           (sqrt ((x - t * sin (θ1 x y t))² +
                                  (y - t * (1 - cos (θ1 x y t)))²)))).
      + unfold locally.
        assert (0 < Rmin x0 (s - x0)) as Q0.
        { apply Rmin_glb_lt; lra. }
        exists (mkposreal _ Q0); intros.
        destruct Rbar_le_dec; cbn in *.
        * destruct r0.
          -- rewrite <- (Darm_Q_straight_std x y y0); try lra.
             unfold AbsRing_ball, abs, minus, plus, opp in H3;
               cbn in H3.
             destruct (total_order_T 0 y) as [[P|EQ]|N].
             ++ eapply straight_r_dom1_std; eauto.
                apply Rmin_def in H3; destruct H3.
                apply Rabs_def2 in H5; destruct H5.
                lra.
             ++ eapply straight_r_dom3_std; eauto.
             ++ apply straight_neg2; auto.
          -- subst.
             replace (x - 0 * sin (θ1 x y 0)) with x by ring.
             replace (y - 0 * (1 - cos (θ1 x y 0))) with y by ring.
             unfold Rsqr.
             replace (x * x - (2 * 0 - y) * y)
               with (x * x + y * y) by ring.
             reflexivity.
        * exfalso.
          unfold AbsRing_ball, abs, minus, plus, opp in H3;
            cbn in H3.
          apply Rmin_def in H3; destruct H3.
          apply Rabs_def2 in H3; destruct H3.
          lra.
      + assert (straight x0 0 0 0 x y).
        { destruct (total_order_T 0 y) as [[P|EQ]|N].
          - eapply straight_r_dom1_std; eauto.
          - eapply straight_r_dom3_std; eauto.
          - apply straight_neg2; auto.
        }
        specialize (full_path_dist_ex_derive_s x y x0 H3 H1) as Q0.
        apply ex_derive_continuous in Q0.
        apply Q0.
    - subst.
      unfold d.
      apply (continuous_plus
               (fun t : R =>
                  (if Rbar_le_dec 0 t
                   then t * θ1 x y t
                   else 0))).
      + apply (continuous_ext_loc
                 _ (fun t => t * θ1 x y t)).
        * exists (mkposreal _ H1); intros.
          destruct Rbar_le_dec; cbn in *; auto.
          exfalso.
          unfold AbsRing_ball, abs, minus, plus, opp in H2;
            cbn in H2.
          apply Rabs_def2 in H2; destruct H2.
          lra.
        * apply (continuous_mult
                   (fun t => t) (fun t => θ1 x y t)).
          -- apply continuous_id.
          -- specialize (theta1_ex_derive_posr s x y phase H1) as Q0.
             apply ex_derive_continuous in Q0; auto.
      + apply Q.
    - subst; auto.
    - exfalso; lra.
  }
  assert (forall x0 : R,
             Rbar_lt 0 x0 ->
             Rbar_lt x0 s ->
             is_derive d x0
            ((fun t : R => θ1 x y t - sin (θ1 x y t)) x0)) as Q1.
  { intros.
    specialize (full_path_dist_is_derive_s x y s phase sgtr) as Q1.
    apply (is_derive_ext_loc
             (fun z : R_AbsRing =>
                z * θ1 x y z +
                sqrt
                  ((x - z * sin (θ1 x y z))² +
                   (y - z * (1 - cos (θ1 x y z)))²))
             d x0).
    - assert (0 < Rmin x0 (s - x0)).
      apply def_Rmin; split; cbn in *; lra.
      exists (mkposreal _ H3); intros; cbn in *.
      unfold d.
      destruct Rbar_le_dec; cbn in *.
      + destruct r0.
        * unfold AbsRing_ball, abs, minus, plus, opp in H4;
            cbn in H4.
          apply Rmin_def in H4; destruct H4.
          apply Rabs_def2 in H6; destruct H6.
          rewrite <- (Darm_Q_straight_std x y y0); try lra.
          destruct (total_order_T 0 y) as [[P|EQ]|N].
          -- eapply straight_r_dom1_std; eauto.
             lra.
          -- eapply straight_r_dom3_std; eauto.
          -- apply straight_neg2; auto.
        * exfalso; subst.
          unfold AbsRing_ball, abs, minus, plus, opp in H4;
            cbn in H4.
          apply Rmin_def in H4; destruct H4.
          apply Rabs_def2 in H4; destruct H4.
          lra.
      +  unfold AbsRing_ball, abs, minus, plus, opp in H4;
           cbn in H4.
         apply Rmin_def in H4; destruct H4.
         apply Rabs_def2 in H4; destruct H4.
         lra.
    - apply full_path_dist_is_derive_s; auto.
      destruct (total_order_T 0 y) as [[P|EQ]|N].
      + eapply straight_r_dom1_std; eauto.
      + eapply straight_r_dom3_std; eauto.
      + apply straight_neg2; auto.
  }

  assert (forall x0 : R,
             Rbar_lt 0 x0 ->
             Rbar_lt x0 s ->
             (fun t : R => θ1 x y t - sin (θ1 x y t)) x0 > 0).
  { intros.
    apply Rgt_lt.
    apply x_minus_sin_x_pos.
    cbn in *.
    specialize (theta1_rsgn_lim x y x0 ltac:(lra)) as [A B].
    destruct (total_order_T 0 y) as [[P|EQ]|N].
    - eapply straight_r_dom1_std; eauto.
    - eapply straight_r_dom3_std; eauto.
    - apply straight_neg2; auto.
    - destruct (A H1); auto.
      exfalso.
      apply (nposx_t1ne0 x y x0); auto; try lra.
      apply straightcond.
      destruct (total_order_T 0 y) as [[P|EQ]|N].
      + eapply straight_r_dom1_std; eauto.
      + eapply straight_r_dom3_std; eauto.
      + apply straight_neg2; auto.
  }
  apply (@incr_function_le_cont_ep
                d 0 s
                (fun t => (((θ1 x y t) - sin (θ1 x y t))))
                Q0 Q1 H1 0 s); cbn; try lra.
Qed.


(* Lemma full_path_dist_increasing_turn_s : *)
(*     forall (x y r s : R) *)
(*            (nO : ~ (x = 0 /\ y = 0)) *)
(*            (phase : turning s 0 0 0 x y \/ straight s 0 0 0 x y) *)
(*            (rgt0 : 0 <= r) *)
(*            (sgtr : r < s), *)
(*       let arclen := (fun r => if Rbar_le_dec 0 r (* for the epsilor ball *) *)
(*                               then r * θ1 x y r *)
(*                               else 0) in *)
(*       let armlen := (fun r => sqrt (x² - (2 * r - y) * y)) in *)
(*       let d := (fun r => arclen r + armlen r) in *)
(*       d r < d s. *)
(* Proof. *)
(*   intros. *)

(*   destruct phase as [trn|str]. *)
(*   + destruct rgt0 as [zltr | zeqr]. *)
(*     specialize full_path_dist_increasing_turn_s. *)
(*     specialize full_path_dist_increasing. *)
(*     specialize full_path_dist_increasing_req0_s. *)



Definition L x y θ r := r*θ + sqrt ((x-r*sin θ)² + (y-r*(1-cos θ))²).

(* in progress *)
Lemma underapprox_minlength_path_outer_tangent_infinite_hat_tile_turning_std :
  forall r x y φ₂
         (p1p2 : 0 < φ₂)
         (p2ub : φ₂ <= 2 * PI)
         (lt : 0 < r)
         (oc : 2 * r * y = x² + y²),
    let θmax := calcθ₁ 0 0 0 x y in
    let wx := r*sin φ₂ in
    let wy := r*(1 - cos φ₂) in
    (y >= 0 /\ wx * y <= wy * x) -> 
    sqrt (x² + y²) <= r * θmax.
Proof.
  intros until 4.
  intros * [rb lb].
  unfold L.
  arn.

  apply le_epsilon.
  intros.

  apply (Rle_trans
  specialize (full_path_dist_increasing_turn_s x y _ r) as foo.

  assert ()
  assert (forall e, e > 0 -> sqrt (x² + y²) <= r * θmax + e) as ng.
  
  admit.
  apply (Rle_trans _ r * θmax + 
(* 

|- sqrt (x^2 + y^2) <= r * tm

|- forall e>0, sqrt (x^2 + y^2) <= r * tm + e

exists d>0, |rm-r|<d -> sqrt ((x- r * sin th)^2 + (y - r*(1-cos th))^2) < e |- 
sqrt (x^2 + y^2) <= r * th + sqrt ((x- r * sin th)^2 + (y - r*(1-cos th))^2) |- 

*)  
  
Admitted.

Lemma underapprox_minlength_path_outer_tangent_infinite_hat_tile_straight_std :
  forall r x y φ₂
         (p1p2 : 0 < φ₂)
         (p2ub : φ₂ <= 2 * PI)
         (lt : 0 < r)
         (oc : 2 * r * y < x² + y²),
    let wx := r*sin φ₂ in
    let wy := r*(1 - cos φ₂) in
    (y >= 0 /\ wx * y <= wy * x) -> 
    sqrt (x² + y²) <= L x y (θ1 x y r) r.
Proof.
  intros until 4.
  intros * [rb lb].

  unfold L.
  assert (sqrt (x² + y²) = L x y 0 r) as id. {
    unfold L.
    arn.
    reflexivity. }
  rewrite id; clear id.

  destruct (total_order_T 0 x) as [[zltx|zeq0]|zgtx].
  + destruct rb as [ygt0 |yeq0].
    unfold L.
    arn.
    apply condstraight in oc.
    specialize (Darm_Q_gen 0 0 0 x y r oc ltac:(lra)) as daqg.
    simpl in daqg.
    autorewrite with null in daqg.
    rewrite daqg.
    fieldrewrite (x² + y²) (x² - (2 * 0 - y) * y).
    setl (0 + sqrt (x² - (2 * 0 - y) * y)).
    left.
    specialize (full_path_dist_increasing_req0_s x y r ltac:(lra) oc lt) as zr.
    simpl in zr.
    destruct Rbar_le_dec; simpl in *; try lra.
    destruct Rbar_le_dec; simpl in *; try lra.
    (* y=0 case *)
    unfold L, θ1.
    destruct total_order_T as [[zltr|zeqr] | zgtr];
    try destruct total_order_T as [[zltx2|zeqx] | zgtx];
    try destruct total_order_T as [[zlty|zeqy] | zgty];
    try destruct total_order_T as [[zltA|zeqA] | zgtA]; try lra.
  + destruct rb as [ygt0|yeq0];
      [|rewrite <- zeq0, yeq0 in oc;
        autorewrite with null in oc;
        lra].
    unfold L.
    arn.
    apply condstraight in oc.
    specialize (Darm_Q_gen 0 0 0 x y r oc ltac:(lra)) as daqg.
    simpl in daqg.
    autorewrite with null in daqg.
    rewrite daqg.
    fieldrewrite (x² + y²) (x² - (2 * 0 - y) * y).
    setl (0 + sqrt (x² - (2 * 0 - y) * y)).
    left.
    specialize (full_path_dist_increasing_req0_s x y r ltac:(lra) oc lt) as zr.
    simpl in zr.
    destruct Rbar_le_dec; simpl in *; try lra.
    destruct Rbar_le_dec; simpl in *; try lra.

  + unfold L.
    arn.
    apply condstraight in oc.
    specialize (Darm_Q_gen 0 0 0 x y r oc ltac:(lra)) as daqg.
    simpl in daqg.
    autorewrite with null in daqg.
    rewrite daqg.
    fieldrewrite (x² + y²) (x² - (2 * 0 - y) * y).
    setl (0 + sqrt (x² - (2 * 0 - y) * y)).
    left.
    specialize (full_path_dist_increasing_req0_s x y r ltac:(lra) oc lt) as zr.
    simpl in zr.
    destruct Rbar_le_dec; simpl in *; try lra.
    destruct Rbar_le_dec; simpl in *; try lra.
Qed.

Lemma sliding_triangle :
  forall h b1 b2 h' b1' b2'
         (zlth : 0 < h)
         (zltb1 : 0 < b1)
         (zltb2 : 0 < b2)
         (zlth' : 0 < h')
         (zltb1': 0 < b1')
         (zltb2' : 0 < b2')
         (bp1ltb1 : b1' < b1)
         (hrat : h' = h * b1' * / b1)
         (sumb : b1' + b2' = b1 + b2),
    sqrt(b1'² + h'²) + sqrt(b2'² + h'²) <=
    sqrt(b1² + h²) + sqrt(b2² + h²).
Proof.
  intros.
  (* can try to fix this later, if desired to make goal < 
  assert (sqrt (b1'² + h'²) + sqrt (b2'² + h'²) = sqrt (b1² + h²) + sqrt (b2² + h²)) as ctr. admit.
  exfalso. *)
  specialize (triangle (b1+b2) 0 b1' h' b1 h) as tri.
  unfold dist_euc in tri.
  autorewrite with null in tri.
  rewrite <- sumb in tri at 1.
  replace (b1' + b2' - b1') with b2' in tri by field.
  replace (b1 + b2 - b1) with b2 in tri by field.
  repeat rewrite <- Rsqr_neg in tri.
  set (p1 := sqrt (b1'² + h'²)) in *.
  set (q1 := sqrt (b2² + h²)) in *.
  set (q2 := sqrt (b2'² + h'²)) in *.
  set (p1p2 := sqrt (b1² + h²)) in *.
  set (p2 := sqrt ((b1 - b1')² + (h - h')²)) in *.
  assert (p1p2 = p1 + p2) as id. {
    unfold p1p2, p1, p2.
    replace (b1'² + h'²) with ((b1' * / b1)² * (b1² + h²)). {
      rewrite hrat.
      replace b1' with (b1 * (b1' * / b1)) at 2 by (field; try lra).
      assert ((b1² + h²) * (1 - (b1' * / b1))² =
              (b1 - b1 * (b1' * / b1))² + (h - h * b1' * / b1)²) as id. {
        unfold Rsqr.
        field.
        lra. }
      rewrite <- id; clear id.
      repeat rewrite sqrt_mult_alt.
      rewrite Rmult_comm at 1.
      rewrite <- Rmult_plus_distr_l.
      repeat rewrite sqrt_Rsqr.
      field.
      lra.
      apply (Rmult_le_reg_r b1); try lra;
        arn;
        setr (b1 - b1'); lra.
      apply (Rmult_le_reg_r b1); try lra;
        arn;
        setr (b1'); lra.
      left. apply posss; lra.
      apply Rle_0_sqr. }
    rewrite hrat.
    unfold Rsqr; field; lra. }
  rewrite id.
  lra.
Qed.

Lemma squatting_triangle :
  forall h b1 b2 h' 
         (zlth : 0 < h)
         (zltb1 : 0 < b1)
         (zltb2 : 0 < b2)
         (zlth' : 0 < h' < h),
    sqrt(b1² + h'²) + sqrt(b2² + h'²) <
    sqrt(b1² + h²) + sqrt(b2² + h²).
Proof.
  intros.
  apply Rplus_lt_compat.
  apply sqrt_lt_1_alt.
  split.
  left; apply posss; lra.
  apply Rplus_le_lt_compat; try lra.
  apply Rsqr_incrst_1; lra.
  apply sqrt_lt_1_alt.
  split.
  left; apply posss; lra.
  apply Rplus_le_lt_compat; try lra.
  apply Rsqr_incrst_1; lra.
Qed.

Lemma smaller_interior_path_triangle :
  forall h b1 b2 h' b1' b2'
         (zlth : 0 < h)
         (zltb1 : 0 < b1)
         (zltb2 : 0 < b2)
         (zlth' : 0 < h')
         (zltb1': 0 < b1')
         (zltb2' : 0 < b2')
         (sumb : b1 + b2 = b1' + b2')
         (lb : h' * b1 < h * b1')
         (rb : h' * b2 < h * b2'),
    sqrt(b1'² + h'²) + sqrt(b2'² + h'²) <
    sqrt(b1² + h²) + sqrt(b2² + h²). (* interior triangle smaller *)
Proof.
  intros.
  assert (h' < h) as hplth. {
    apply (Rmult_lt_reg_r (b1 + b2)); try lra.
    rewrite sumb at 2.
    repeat rewrite Rmult_plus_distr_l.
    lra. }

  (* h,b1,b2 is outer triangle, h',b1',b2' is a triangle that is sliding down one arm, 
     h'',b1',b2' is a triangle construced from the slid triangle that is also squatting *)
  rename h' into h''.
  destruct (total_order_T b1' b1); [destruct s|].
  + set (h' :=  h * b1' * / b1).
    apply (Rlt_le_trans _ (sqrt (b1'² + h'²) + sqrt (b2'² + h'²))).
    apply squatting_triangle; try lra.
    unfold h'.
    zltab.
    split.
    lra.
    unfold h'.
    apply (Rmult_lt_reg_r b1); try lra.
    lrag lb.

    apply sliding_triangle; try lra.
    unfold h'.
    apply (Rmult_lt_reg_r b1); try lra.
    setl 0.
    setr (h * b1').
    lra.
    zltab.
    unfold h'.
    reflexivity.
  + apply (Rlt_le_trans _ (sqrt (b1'² + h²) + sqrt (b2'² + h²))).
    apply squatting_triangle; try lra.
    assert (b2' = b2) as f; try lra.
    rewrite e, f.
    right; reflexivity.
  + set (h' :=  h * b2' * / b2).
    apply (Rlt_le_trans _ (sqrt (b2'² + h'²) + sqrt (b1'² + h'²))).
    rewrite Rplus_comm.

    apply squatting_triangle; try lra.
    unfold h'.
    zltab.
    split.
    lra.
    unfold h'.
    apply (Rmult_lt_reg_r b2); try lra.
    lrag rb.

    rewrite (Rplus_comm (sqrt (b1² + h²))).
    apply sliding_triangle; try lra.
    unfold h'.
    apply (Rmult_lt_reg_r b2); try lra.
    setl 0.
    setr (h * b2').
    lra.
    zltab.
    unfold h'.
    reflexivity.
Qed.



Lemma underapprox_minlength_path_inner_tangent_infinite_hat_tile_std :
  forall r x y φ₂
         (p1p2 : 0 < φ₂)
         (p2ub : φ₂ <= 2 * PI)
         (lt : 0 < r)
         (oc : 2 * r * y < x² + y²),
    let nx := cos φ₂ in
    let ny := sin φ₂ in
    let wx := r*sin φ₂ in
    let wy := r*(1 - cos φ₂) in
    (nx * (y - wy) <= ny * (x - wx) /\ wx * y >= wy * x) -> 
    sqrt (wx² + wy²) + sqrt ((x - wx)² + (y - wy)²) <= L x y (θ1 x y r) r.
Proof.
  intros until 4.
  intros * [rb lb].
  unfold L, wx, wy.
  
   


Theorem underapprox_minlength_path_outer_tangent_infinite_hat_tile :
  forall r x y φ₁ φ₂
         (p1lb : 0 <= φ₁)
         (p1p2 : φ₁ < φ₂)
         (p2ub : φ₂ <= 2 * PI )
         (lt : 0 < r)
         (oc : 2 * r * y <= x² + y²),
    let mx := cos φ₁ in
    let my := sin φ₁ in
    let vx := r*sin φ₁ in
    let vy := r*(1 - cos φ₁) in
    let wx := r*sin φ₂ in
    let wy := r*(1 - cos φ₂) in
    (mx*(y - vy) >= my*(x - vx) /\
     (wx - vx)*(y - vy) <= (wy - vy)*(x - vx)) -> 
      L x y φ₁ r  <= L x y (θ1 x y r) r.
Proof.
  intros until 5.
  intros * [rb lb].

  destruct oc as [phase|phase].
  destruct rb as [gt |eq].
  + assert (sign (κ' x y r φ₁) = 1) as incr_k. {
      unfold κ', my, mx, vx, vy in *.
      apply (Rmult_gt_compat_l _ _ _ lt) in gt.
      assert (0 < - r * sin φ₁ * (x - r * sin φ₁) -
                  r * cos φ₁ * (- y + r * (1 - cos φ₁)))
        as P by lra.
      apply sign_eq_1 in P.
      rewrite sign_eq_pos_den; auto.
      apply posss; intros [P0 P1].
      apply Rminus_diag_uniq in P0;
        apply Rminus_diag_uniq in P1; subst; clear - phase.
      unfold Rsqr in phase.
      replace (r * sin φ₁ * (r * sin φ₁) +
               r * (1 - cos φ₁) * (r * (1 - cos φ₁))) with
          (r * r * (1 - 2 * cos φ₁ + ((sin φ₁)² + (cos φ₁)²)))
        in phase.
      { rewrite sin2_cos2 in phase; lra. }
      unfold Rsqr; ring.
    }

    
    phi1 <= k(x,y,phi1) <= (phi1+phi2)/2
    
    assert (φ₁ < θ1 x y r) as p1ltt1. {

Theorem underapprox_minlength_path_inner_tangent_infinite_hat_tile :
  forall r x y φ₁ φ₂ (p1p2 : φ₁ < φ₂ ) (lt : 0 < r),
    let nx := cos φ₂ in
    let ny := sin φ₂ in
    let vx := r*sin φ₁ in
    let vy := r*(1 - cos φ₁) in
    let wx := r*sin φ₂ in
    let wy := r*(1 - cos φ₂) in
    (nx*(y - wy) <= ny*(x - wx) /\ (wx - vx)*(y - vy) >= (wy - vy)*(x - vx)) -> 
      L x y φ₂ r  <= L x y (θ1 x y r) r.
Proof.
  intros until 2.
  intros * [lb rb].
Admitted.





Definition colinear (a b c: pt) : Prop :=
  let ax := ptx a in
  let ay := pty a in
  let bx := ptx b in
  let bY := pty b in
  let cx := ptx c in
  let cy := pty c in
  let mx := bx - ax in
  let my := bY - ay in
  (my * (cx - ax) = mx * (cy - ay)).

Inductive tri (a b c : pt) : Set :=
  | mktri : ~ colinear a b c -> tri a b c.

Definition edglen (a b : pt) : R := sqrt (((ptx a) - (ptx b))² + ((pty a) - (pty b))²).

Definition angle (a b c : pt) : R :=
  let θ₀ := atan2 ((pty a) - (pty b)) ((ptx a) - (ptx b)) in
  let x := ((ptx c - ptx b) * cos (- θ₀) + (pty c - pty b) * sin (- θ₀)) in
  let y := (- (ptx c - ptx b) * sin (- θ₀) + (pty c - pty b) * cos (- θ₀)) in
  Rabs (atan2  y x).


(* forall x₁ y₁ x₂ y₂ x₃ y₃ *)
Axiom lawofcos : forall A B C (T : tri A B C),
    let α := angle C A B in
    let β := angle A B C in
    let γ := angle B C A in
    let ab := edglen A B in
    let bc := edglen B C in
    let ac := edglen A C in
    ab² = ac² + bc² - 2 * ac * bc * cos γ.

Axiom lawofsin : forall A B C (T : tri A B C),
    let α := angle C A B in
    let β := angle A B C in
    let γ := angle B C A in
    let ab := edglen A B in
    let bc := edglen B C in
    let ac := edglen A C in
    ab / sin γ  = ac / sin β.


Axiom trisum180 : forall A B C (T : tri A B C),
    let α := angle C A B in
    let β := angle A B C in
    let γ := angle B C A in
    α + β + γ = PI.


