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


Lemma Darm_continuous : 
  forall x y z, continuous (fun t => (sqrt (x² - (2 * t - y) * y))) z.
Proof.
  intros.
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
  specialize (Darm_continuous x y) as Q.

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


Definition L x y θ r := r*θ + sqrt ((x-r*sin θ)² + (y-r*(1-cos θ))²).


(*

Let 0 < s < rmax
we know that d 0 < d s from above
that means sqrt (x² + y²) < s * θ1 x y s + sqrt (x² - (2 * s - y) * y)

since sqrt (x² - (2 * s - y) * y) is continuous in s, and

sqrt (x² - (2 * rmax - y) * y) = 0 then

for all 0 < epsilon we may choose an 0 < s'< rmax s.t. 
sqrt (x² - (2 * s' - y) * y) < epsilon.

Then 
sqrt (x² + y²) < s' * θ1 x y s + sqrt (x² - (2 * s' - y) * y)
               < s' * θ1 x y s + epsilon
               < rmax * θmax + epsilon

This implies 
sqrt (x² + y²) <= rmax * θmax
by le_epsilon.

 *)

Lemma underapprox_turning_std :
  forall r x y
         (lt : 0 < r)
         (oc : 2 * r * y = x² + y²),
    let θmax := calcθ₁ 0 0 0 x y in
    forall (rb : y > 0),
    sqrt (x² + y²) <= r * θmax.
Proof.
  intros.
  unfold L.
  arn.

  apply le_epsilon.
  intros eps zlte.

  specialize (Darm_continuous x y) as cnt.
  simpl in *.

  assert (sqrt (x² - (2 * r - y) * y) = 0) as noarm. {
    (* destruct rb as [ygt0 |yeq0]. *)
    assert (r = (x² + y²) / (2 * y)) as rd. {
      apply (Rmult_eq_reg_r (2 * y)).
      lrag oc.
      lra. }
    rewrite rd.
    fieldrewrite (x² - (2 * ((x² + y²) / (2 * y)) - y) * y) 0; try lra.
    apply sqrt_0.
    (* rewrite yeq0 in *.
    autorewrite with null in *.
    symmetry in oc.
    rewrite oc.
    apply sqrt_0. *) }

  set (f := (fun t : R => sqrt (x² - (2 * t - y) * y))) in *.
  setoid_rewrite reasonable_continuity in cnt.
  specialize (cnt r (mkposreal _ zlte)).
  simpl in *.
  destruct cnt as [del ba].

  set (s := Rmax (r - del * / 2) (r * / 2)) in *.
  specialize (ba s).

  assert (0 < s) as zlts. {
    unfold s, Rmax.
    destruct Rle_dec ; try lra. }
  assert (s < r) as sltr. {
    unfold s, Rmax.
    destruct Rle_dec ; try lra.
    destruct del.
    simpl in *.
    lra. }

  assert (straight s 0 0 0 x y) as sstr. {
    apply condstraight.
    rewrite <- oc.
    apply Rmult_lt_compat_r; try lra. }

  assert (s - r < 0) as srlt0. {
    unfold s.
    unfold s, Rmax.
    destruct Rle_dec ; try lra.
    destruct del.
    simpl in *.
    lra. }
  
  assert (Rabs (s - r) < del) as cnd. {
    rewrite Rabs_left; try assumption.
    setl (r - s).
    unfold s.
    specialize (Rmax_l (r - del * / 2) (r * / 2)) as foo.
    destruct del; simpl in *.
    apply (Rle_lt_trans _ (r - (r - pos * / 2))); try lra. }

  specialize (ba cnd).
  change (f r = 0) in noarm.
  rewrite noarm in ba.
  autorewrite with null in ba.
  assert (forall z, 0 <= f z) as nns. {
    intros.
    unfold f.
    apply sqrt_pos. }
  
  specialize (nns s).
  apply Rle_ge in nns.
  rewrite Rabs_right in ba; try assumption.

  set (d := (fun t : R =>
               (if Rbar_le_dec 0 t
                then t * θ1 x y t
                else 0) +
               (sqrt (x² - (2 * t - y) * y)))).

  apply (Rle_trans _ (r * θmax + f s)); try lra.
  apply (Rle_trans _ ((if Rbar_le_dec 0 s then s * θ1 x y s else 0) + f s)).
  unfold f.
  change (sqrt (x² + y²) <= d s).
  + replace (sqrt (x² + y²)) with (d 0).
    left.
    apply full_path_dist_increasing_req0_s; [lra | auto | lra].
    unfold d.
    destruct Rbar_le_dec; try lra.
    arn.
    replace (x² - - y * y) with (x² + y²) by (unfold Rsqr; lra).
    reflexivity.

    exfalso.
    apply n.
    simpl.
    lra.

  + destruct Rbar_le_dec; simpl in *; try lra.
    clear r0.
    apply (Rplus_le_reg_r (- f s)).
    setl (s * θ1 x y s).
    setr (r * θmax).
    apply Rmult_le_compat; try lra.
    apply theta1_rsgn_lim; try lra.
    assumption.
    specialize (root_ordering_rpos_left x y s zlts ltac:(lra) sstr) as [tlb tub].
    unfold θmax.
    left.
    apply tlb.
Qed.

(* 

|- sqrt (x^2 + y^2) <= r * tm

|- forall e>0, sqrt (x^2 + y^2) <= r * tm + e

exists d>0, |rm-r|<d -> sqrt ((x- r * sin th)^2 + (y - r*(1-cos th))^2) < e |- 
sqrt (x^2 + y^2) <= r * th + sqrt ((x- r * sin th)^2 + (y - r*(1-cos th))^2) |- 

*)  

Lemma minlength_outer_infinite_hat_straight_std :
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

Print dist_euc.
Definition dist_R2 a b := dist_euc (ptx a) (pty a) (ptx b) (pty b).

Lemma dist_R2_pos : forall a b : pt, dist_R2 a b >= 0.
Proof.
  intros;
  destruct a, b; unfold dist_R2; simpl.
  apply Rle_ge; apply sqrt_pos.
Qed.

Lemma dist_R2_sym : forall a b : pt, dist_R2 a b = dist_R2 b a.
Proof.
  intros;
    destruct a, b; unfold dist_R2, dist_euc; simpl.
  rewrite Rsqr_neg_minus.
  rewrite (Rsqr_neg_minus pty pty0).
  reflexivity.
Qed.

Lemma dist_R2_refl : forall a b : pt, dist_R2 a b = 0 <-> a = b.
Proof.
  intros;
    destruct a, b; unfold dist_R2, dist_euc; simpl.
  split.
  intros.
  specialize (Rle_0_sqr (ptx - ptx0)) as xdnn.
  specialize (Rle_0_sqr (pty - pty0)) as ydnn.
  apply sqrt_eq_0 in H; try lra.
  destruct xdnn as [xdlt | xdeq].
  exfalso.
  generalize H.
  change ((ptx - ptx0)² + (pty - pty0)² <> 0).
  clear H.
  lra.
  destruct ydnn as [ydlt | ydeq].
  exfalso.
  generalize H.
  change ((ptx - ptx0)² + (pty - pty0)² <> 0).
  clear H.
  lra.
  clear H.
  assert (ptx = ptx0) as xeq. {
    symmetry in xdeq.
    unfold Rsqr in xdeq.
    apply Rmult_integral in xdeq.
    lra. }
  assert (pty = pty0) as yeq. {
    symmetry in ydeq.
    unfold Rsqr in ydeq.
    apply Rmult_integral in ydeq.
    lra. }
  subst.
  reflexivity.

  intros.
  inversion H.
  subst.
  arn.
  reflexivity.
Qed.
  
Print Build_Metric_Space.

Check triangle.
Print dist_euc.

Lemma dist_R2_tri : forall a b c : pt, dist_R2 a b <= dist_R2 a c + dist_R2 c b.
Proof.
  intros.
  intros;
    destruct a, b, c; unfold dist_R2; simpl.
  apply triangle.
Qed.

Definition R2_met := (Build_Metric_Space pt dist_R2 dist_R2_pos dist_R2_sym dist_R2_refl dist_R2_tri).

Lemma eqv_R2_dist_expr : forall a b,
    dist R2_met a b = dist_R2 a b.
Proof.
  intros.
  unfold dist; simpl; reflexivity.
Qed.

(*
  analysis of alternatives:
  a1: keeping design in-house
  a2: selling kansas plant
*)                                        

Search Metric_Space.
Print Metric_Space.

Lemma rot_pt_eq_len : forall x y η, 
    let x' := x * cos η + y * sin η in
    let y' := - x * sin η + y * cos η in
    sqrt (x² + y²) = sqrt (x'² + y'²).
Proof.
  intros.
  unfold x', y'.
  repeat rewrite Rsqr_plus.
  fieldrewrite ((x * cos η)² + (y * sin η)² + 2 * (x * cos η) * (y * sin η) +
                ((- x * sin η)² + (y * cos η)² + 2 * (- x * sin η) * (y * cos η)))
               (x² * ((sin η)² + (cos η)²) + y² * ((sin η)² + (cos η)²)).
  rewrite sin2_cos2.
  arn.
  reflexivity.
Qed.

Lemma minlength_inner_infinite_hat_straight_std :
  forall r x y φ₂
         (p1p2 : 0 < φ₂)
         (p2ub : φ₂ < 2 * PI)
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

  set (xi := r * sin (θ1 x y r)).
  set (yi := r * (1 - cos (θ1 x y r))).
  assert (2 * r * yi = xi² + yi²) as rturn. {
    unfold xi, yi.
    fieldrewrite ((r * sin (θ1 x y r))² + (r * (1 - cos (θ1 x y r)))²)
                 (r² * (((sin (θ1 x y r))²  + (cos (θ1 x y r))²)
                  + (1 - 2 * cos (θ1 x y r)))).
    rewrite sin2_cos2.
    unfold Rsqr.
    field. }
  set (θmaxi := calcθ₁ 0 0 0 xi yi).

  apply condstraight in oc.
  specialize (theta1_rsgn_bnd x y r ltac:(lra) oc) as [rgt rlt].
  clear rlt.
  specialize (rgt lt).
  destruct rgt as [[t1lb | t1eq] t1ub].
  
  + assert (θmaxi = θ1 x y r) as tmidef. {
      unfold θmaxi.
      rewrite thms.
      unfold yi, xi.
      rewrite chord_property; try assumption.
      reflexivity.
      lra. }

    assert (yi > 0) as yigt0. {
      unfold yi.
      apply Rlt_gt.
      zltab.
      specialize (COS_bound (θ1 x y r)) as [cl [cu |ce]].
      lra.
      exfalso.
      apply cosθeq1 in ce; lra. }

    
    specialize (underapprox_turning_std _ _ _ lt rturn yigt0) as li.
    unfold θmaxi in tmidef.
    rewrite tmidef in li.
    apply (Rle_trans _ (sqrt (xi² + yi²) + sqrt ((x - xi)² + (y - yi)²)));
      [| apply (Rplus_le_reg_r (- sqrt ((x - xi)² + (y - yi)²))); lrag li].

    (* From wikipedia: R = [cosθ -sinθ ; 
                            sinθ cosθ] is for active
       rotations of vectors counterclockwise in a right-handed
       coordinate system (y counterclockwise from x) by
       pre-multiplication (R on the left). If any one of these is
       changed (such as rotating axes instead of vectors, a passive
       transformation), then the inverse of the example matrix should
       be used, which coincides with its transpose. *)
    set (η := atan2 y x).
    set (ax' := xi * cos η + yi * sin η).
    set (ay' := - xi * sin η + yi * cos η).
    set (aix' := wx * cos η + wy * sin η).
    set (aiy' := - wx * sin η + wy * cos η).
    set (x' := x * cos η + y * sin η).
    set (y' := - x * sin η + y * cos η).
    change (sqrt (wx² + wy²) + sqrt ((x - wx)² + (y - wy)²) <=
            sqrt (xi² + yi²) + sqrt ((x - xi)² + (y - yi)²)).

    rewrite (rot_pt_eq_len _ _ η).
    rewrite (rot_pt_eq_len (x-wx) _ η).

    fieldrewrite (((x - wx) * cos η + (y - wy) * sin η)² + (- (x - wx) * sin η + (y - wy) * cos η)²)
                 (((x * cos η + y * sin η) - (wx * cos η + wy * sin η))² +
                  ((- x * sin η + y * cos η) - (- wx * sin η + wy * cos η))²).

    change (sqrt (aix'² + aiy'²) +
            sqrt ((x' - aix')² + (y' - aiy')²) <=
            sqrt (xi² + yi²) + sqrt ((x - xi)² + (y - yi)²)).

    rewrite (rot_pt_eq_len (xi) _ η).
    rewrite (rot_pt_eq_len (x-xi) _ η).

    change (sqrt (aix'² + aiy'²) + sqrt ((x' - aix')² + (y' - aiy')²) <=
            sqrt (ax'² + ay'²) +
            sqrt (((x - xi) * cos η + (y - yi) * sin η)² + (- (x - xi) * sin η + (y - yi) * cos η)²)).

    fieldrewrite (((x - xi) * cos η + (y - yi) * sin η)² + (- (x - xi) * sin η + (y - yi) * cos η)²)
                 (((x * cos η + y * sin η) - (xi * cos η + yi * sin η))² +
                  ((- x * sin η + y * cos η) - (- xi * sin η + yi * cos η))²).

    change (sqrt (aix'² + aiy'²) + sqrt ((x' - aix')² + (y' - aiy')²) <=
            sqrt (ax'² + ay'²) + sqrt ((x' - ax')² + (y' - ay')²)).

    assert (~ (x = 0 /\ y = 0)) as no. {
      apply straight_not_stationary2 in oc.
      lra. }

    assert (0 <= x² + y²) as x2y2 by zltab.

    assert (y' = 0) as y'eq0. {
      unfold y', η.
      rewrite atan2_sin_id, atan2_cos_id; try assumption.
      repeat rewrite <- Rsqr_pow2.
      field.
      intro seq0.
      apply sqrt_eq_0 in seq0; try assumption.
      apply posss in no.
      lra. }

    rewrite y'eq0 in *.
    arn.

    rewrite (Rsqr_neg aiy'), (Rsqr_neg ay').

    set (h := -ay') in *.
    set (h' := -aiy') in *.
    set (b1' := aix') in *.
    set (b2' := x' - b1') in *.
    set (b1 := ax') in *.
    set (b2 := x' - b1) in *.
    left.
    apply smaller_interior_path_triangle.
    7 : {
      unfold b2, b2', b1, b1'.
      field. }

    ++ unfold h, ay'.
       setr (xi * sin η - yi * cos η).

       rewrite thms in tmidef.
       unfold atan2 in tmidef.
       destruct pre_atan2 as [θ [trng [yid xid]]].
       set (θmax := calcθ₁ 0 0 0 x y).
       assert (η = θmax / 2) as ed. {
         unfold η, θmax.
         rewrite thms. lra. }
       unfold η, atan2 in *.
       destruct pre_atan2 as [e [erng [yd xd]]].
       clear η.
       rewrite xid.
       rewrite yid at 2.
       set (M := sqrt (yi² + xi²)) in *.
       assert (0 < M) as zltm. admit.
       apply (Rmult_lt_reg_r (/ M)).
       zltab.
       setl 0; try lra.
       setr (sin e * cos θ - cos e * sin θ); try lra.
       rewrite <- sin_minus.
       assert (θ = θ1 x y r / 2) as tdef. lra.
       destruct (total_order_T 0 y); [destruct s|].
       +++ rewrite tdef.
           rewrite ed.
           specialize (root_ordering_rpos_left _ _ _ lt r0 oc) as [rorl roru].
           change (θ1 x y r < θmax) in rorl.
           clear roru.
           assert (0 < e - θ1 x y r / 2 < PI) as [arglb argub]; try (split; lra).
           apply sin_gt_0; lra.
           
       +++ assert (x < 0) as xlt0. {
             clear - xd yd rb lb e0 lt p1p2 p2ub no.
             rewrite <- e0 in lb.
             autorewrite with null in lb.
             assert (0 < wy) as zlewy. {
               unfold wy.
               apply Rmult_lt_0_compat.
               assumption.
               specialize (COS_bound φ₂) as [clb cub].
               destruct cub.
               lra.
               apply cosθeq1 in H; try lra. }
             destruct lb as [wyxgt0 |wyxeq0].
             apply Rgt_lt in wyxgt0.
             apply (Rmult_lt_reg_l wy); try assumption.
             arn.
             assumption.
             assert (x = 0) as xeq0. {
               apply (Rmult_eq_reg_l wy).
               arn.
               symmetry.
               assumption.
               lra. }
             exfalso.
             lra. }

           symmetry in e0.
           specialize (root_ordering_rpos_back x _ _ lt e0 ltac:(lra) oc) as [t1d tmd].
           change (θ1 x y r < θmax) in t1d.
           change (θmax = 2 * PI) in tmd.
           assert (0 < e - θ1 x y r / 2 < PI) as [arglb argub]; try (split; lra).
           apply sin_gt_0; lra.
           
       +++ specialize (root_ordering_rpos_right _ _ _ lt r0 oc) as [tml tmu].
           clear tml.
           change (θmax / 2 + 2 * PI < θ1 x y r) in tmu.
           rewrite <- ed in tmu.
           rewrite tdef.
           assert (- 2 * PI < e - θ1 x y r / 2) as lab. lra.
           assert (e - θ1 x y r / 2 < - PI) as uab. {
             apply (Rlt_trans _ (θ1 x y r / 2 - 2 * PI));
               lra. }
           rewrite <- (sin_period1 _ 1).
           apply sin_gt_0;
             lra.
    ++ admit.
    ++ admit.
    ++ admit.
    ++ admit.
    ++ admit.
    ++ admit.
    ++ admit.
  + symmetry in t1eq.
    admit.
Admitted.
       
       


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


