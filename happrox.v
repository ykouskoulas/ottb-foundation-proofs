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

(* end hide *)
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

(* d1 is the distance from vertex 1 to the x coordinate of "center" vertex
   d2 is the distance from x coordinate of the "center" vertex to vertex 2
   vertex 1 and 2 are at the origin and the + x axis, respectively *)

Lemma colinear_dist : forall d1 d2 h,
    0 <= d1 -> 0 <= d2 -> 
    sqrt (d1 + d2)² = sqrt (d1² + h²) + sqrt (d2² + h²) -> h = 0.
Proof.
  intros.
  rewrite sqrt_Rsqr in H1; try lra.
  destruct (Req_dec h 0) as [heq0 | hne0]; try assumption.

  exfalso.
  assert (d1 < sqrt (d1² + h²)) as d1lt. {
    rewrite <- (sqrt_Rsqr d1) at 1; try lra.
    apply sqrt_lt_1; try lra.
    apply Rle_0_sqr.
    left.
    apply posss; lra.
    apply (Rplus_lt_reg_r (- d1²)).
    setl 0.
    setr (h²).
    unfold Rsqr.
    destruct (Rlt_dec 0 h) as [zlth | zgeh].
    zltab.
    apply Rnot_lt_le in zgeh as [hlt0 | heq0]; try lra.
    setr ((- h)*(- h)).
    zltab. }
  
  assert (d2 < sqrt (d2² + h²)) as d2lt. {
    rewrite <- (sqrt_Rsqr d2) at 1; try lra.
    apply sqrt_lt_1; try lra.
    apply Rle_0_sqr.
    left.
    apply posss; lra.
    apply (Rplus_lt_reg_r (- d2²)).
    setl 0.
    setr (h²).
    unfold Rsqr.
    destruct (Rlt_dec 0 h) as [zlth | zgeh].
    zltab.
    apply Rnot_lt_le in zgeh as [hlt0 | heq0]; try lra.
    setr ((- h)*(- h)).
    zltab. }
  specialize (Rplus_lt_compat _ _ _ _ d1lt d2lt) as lt.
  rewrite <- H1 in lt.
  lra.
Qed.


Lemma line_segment_trans : forall tx ty x0 x1 y0 y1,
    (x0 - x1)² + (y0 - y1)² = ((x0+tx) - (x1+tx))² + ((y0+ty) - (y1+ty))².
Proof.
  intros.
  replace (x0 + tx - (x1 + tx)) with (x0 - x1) by lra.
  replace (y0 + ty - (y1 + ty)) with (y0 - y1) by lra.
  reflexivity.
Qed.



Lemma line_segment_rot : forall a x0 x1 y0 y1,
    let x0' := x0 * cos a - y0 * sin a in
    let y0' := x0 * sin a + y0 * cos a in
    let x1' := x1 * cos a - y1 * sin a in
    let y1' := x1 * sin a + y1 * cos a in
    (x0 - x1)² + (y0 - y1)² = (x0' - x1')² + (y0' - y1')².
Proof.
  intros.
  set (L := (x0 - x1)² + (y0 - y1)²).
  unfold x0', x1', y0', y1'.
  setr (x0² * ((sin a)² + (cos a)²)
        + y0² * ((sin a)² + (cos a)²)
        + x1² * ((sin a)² +  (cos a)²)
        + y1² * ((sin a)² +  (cos a)²)
          - 2 * x0 * x1 * ((sin a)² +  (cos a)²)
          - 2 * y0 * y1 * ((sin a)² +  (cos a)²)).
  rewrite sin2_cos2.
  arn.
  unfold L.
  repeat rewrite Rsqr_minus.
  field.
Qed.


Lemma line_segment_trans_rot : forall a tx ty x0 y0 x1 y1,
    let x0' := (x0 + tx) * cos a - (y0 + ty) * sin a in
    let y0' := (x0 + tx) * sin a + (y0 + ty) * cos a in
    let x1' := (x1 + tx) * cos a - (y1 + ty) * sin a in
    let y1' := (x1 + tx) * sin a + (y1 + ty) * cos a in
    (x0 - x1)² + (y0 - y1)² = (x0' - x1')² + (y0' - y1')².
Proof.
  intros.
  rewrite (line_segment_trans tx ty x0 x1).
  rewrite (line_segment_rot a (x0 + tx) (x1 + tx)).
  unfold x0', x1', y0', y1'.
  reflexivity.
Qed.

    
Lemma colinear_coord : forall x0 y0 x1 y1 x2 y2,
    ~ (x2 - x0 = 0 /\ y2 - y0 = 0) -> 
    sqrt ((x0 - x2)² + (y0 - y2)²) =
    sqrt ((x0 - x1)² + (y0 - y1)²) + sqrt ((x1 - x2)² + (y1 - y2)²) ->
    let a := atan2 (y2 - y0) (x2 - x0) in
    - (x1 - x0) * sin a + (y1 - y0) * cos a = 0.
Proof.
  intros * no cl *.
  unfold atan2 in *.
  destruct pre_atan2 as [q [qrng [defy defx]]].
  unfold a in *; clear a.
  set (M := sqrt ((y2 - y0)² + (x2 - x0)²)) in *.

  assert (0 < (y2 - y0)² + (x2 - x0)²) as ss. { apply posss; lra. }
         
  assert (0 < M) as zleM. {
    unfold M.
    rewrite <- sqrt_0.
    apply sqrt_lt_1; try lra. }

  
  repeat rewrite (line_segment_trans_rot (-q) (-x0) (-y0) x0 y0) in cl.
  rewrite (line_segment_trans_rot (-q) (-x0) (-y0) x1 y1) in cl.

  set (x2' := ((x2 - x0) * cos q + (y2 - y0) * sin q)) in *.  
  
  replace ((x0 + - x0) * cos (- q) - (y0 + - y0) * sin (- q) -
           ((x2 + - x0) * cos (- q) - (y2 + - y0) * sin (- q))) with
      (0 - x2') in cl.
  2 : { unfold x2'; rewrite sin_neg, cos_neg; field. }

  set (y2' := (- (x2 - x0) * sin q + (y2 - y0) * cos q)) in *.

  replace ((x0 + - x0) * sin (- q) + (y0 + - y0) * cos (- q) -
           ((x2 + - x0) * sin (- q) + (y2 + - y0) * cos (- q))) with
      (0 - y2') in cl.
  2 : { unfold y2'; rewrite sin_neg, cos_neg; field. }

  set (x1' := ((x1 - x0) * cos q + (y1 - y0) * sin q)) in *.
  replace ((x0 + - x0) * cos (- q) - (y0 + - y0) * sin (- q) -
           ((x1 + - x0) * cos (- q) - (y1 + - y0) * sin (- q))) with
      (0 - x1') in cl.
  2 : { unfold x1'; rewrite sin_neg, cos_neg; field. }

  set (y1' := (- (x1 - x0) * sin q + (y1 - y0) * cos q)) in *.
  replace ((x0 + - x0) * sin (- q) + (y0 + - y0) * cos (- q) -
           ((x1 + - x0) * sin (- q) + (y1 + - y0) * cos (- q))) with
      (0 - y1') in cl.
  2 : { unfold y1'; rewrite sin_neg, cos_neg; field. }

  replace ((x1 + - x0) * cos (- q) - (y1 + - y0) * sin (- q) -
           ((x2 + - x0) * cos (- q) - (y2 + - y0) * sin (- q))) with
      (x1' - x2') in cl.
  2 : { unfold x1', x2'; rewrite sin_neg, cos_neg; field. }

  replace ((x1 + - x0) * sin (- q) + (y1 + - y0) * cos (- q) -
           ((x2 + - x0) * sin (- q) + (y2 + - y0) * cos (- q))) with
      (y1' - y2') in cl.
  2 : { unfold y1', y2'; rewrite sin_neg, cos_neg; field. }

  assert (y2' = 0) as y2'eq0. {
    unfold y2'.
    rewrite defx, defy.
    field. }

  assert (0 < x2') as zltx2'. {
    unfold x2'.
    rewrite defx, defy.
    setr (M * ((sin q)² + (cos q)²)).
    rewrite sin2_cos2.
    lra. }

  rewrite y2'eq0 in *.
  autorewrite with null in cl.
  repeat rewrite <- Rsqr_neg in cl.
  destruct (total_order_T x1' 0) as [[x1'lt0 |x1'eq0]|x1'gt0];
  destruct (total_order_T x1' x2') as [[x1'ltx2' |x1'eqx2']|x1'gtx2']; try lra.
  + exfalso.
    rewrite (Rsqr_neg (x1' - x2')) in cl;
      replace (- (x1' - x2')) with (x2' - x1') in cl by lra.
    assert (sqrt x2'² < sqrt (x1'² + y1'²) + sqrt ((x2' - x1')² + y1'²)) as ctr. {
      rewrite <- (Rplus_0_l (sqrt x2'²)).
      apply Rplus_le_lt_compat.
      apply sqrt_pos.
      apply sqrt_lt_1;
        [apply Rle_0_sqr|
         apply Rplus_le_le_0_compat; apply Rle_0_sqr|].
      rewrite <- (Rplus_0_r x2'²).
      apply Rplus_lt_le_compat.
      apply Rsqr_incrst_1; try lra.
      apply Rle_0_sqr. }
    lra.

  + rewrite (Rsqr_neg (x1' - x2')) in cl;
      replace (- (x1' - x2')) with (x2' - x1') in cl by lra.
    replace x2' with (x1' + (x2' - x1')) in cl at 1 by lra.
    apply colinear_dist in cl; lra.

  + rewrite (Rsqr_neg (x1' - x2')) in cl;
      replace (- (x1' - x2')) with (x2' - x1') in cl by lra.
    replace x2' with (x1' + (x2' - x1')) in cl at 1 by lra.
    apply colinear_dist in cl; lra.

  + rewrite (Rsqr_neg (x1' - x2')) in cl;
      replace (- (x1' - x2')) with (x2' - x1') in cl by lra.
    replace x2' with (x1' + (x2' - x1')) in cl at 1 by lra.
    apply colinear_dist in cl; lra.

  + rewrite sqrt_Rsqr in cl; [|left; assumption].
    assert (x2' < sqrt (x1'² + y1'²) + sqrt ((x1' - x2')² + y1'²)) as ctr. {
      apply (Rlt_le_trans _ (sqrt (x1'²) + sqrt ((x1' - x2')²))).
      apply (Rlt_le_trans _ (x1' + (x1' - x2'))).
      lra.
      repeat rewrite sqrt_Rsqr; try lra.
      apply Rplus_le_compat.
      apply sqrt_le_1;
        [apply Rle_0_sqr|
         apply Rplus_le_le_0_compat; apply Rle_0_sqr|
         apply (Rplus_le_reg_r (- x1'²));
         setl 0;
         setr (y1'²);
         apply Rle_0_sqr].
      apply sqrt_le_1;
        [apply Rle_0_sqr|
         apply Rplus_le_le_0_compat; apply Rle_0_sqr|
         apply (Rplus_le_reg_r (-(x1' - x2')²));
         setl 0;
         setr (y1'²);
         apply Rle_0_sqr]. }
    lra.
Qed.
      
Lemma sliding_triangle_acute :
  forall h b1 b2 h' b1' b2'
         (zlth : 0 < h)
         (zltb1 : 0 < b1)
         (zltb2 : 0 <= b2)
         (zlth' : 0 < h')
         (zltb1': 0 < b1')
         (zltb2' : 0 < b2')
         (bp1ltb1 : b1' < b1)
         (hrat : h' = h * b1' * / b1)
         (sumb : b1' + b2' = b1 + b2),
    sqrt(b1'² + h'²) + sqrt(b2'² + h'²) <
    sqrt(b1² + h²) + sqrt(b2² + h²).
Proof.
  intros.

  specialize (triangle (b1+b2) 0 b1' h' b1 h) as [tri | etri].
  2 : { exfalso.
        unfold dist_euc in *.
        apply colinear_coord in etri; try lra.
        replace (- (b1 - (b1 + b2))) with b2 in etri by lra.
        autorewrite with null in etri.
        rewrite atan2_cos_id, atan2_sin_id in etri; try lra.
        repeat rewrite <- Rsqr_pow2 in etri.

        assert (b2 * h' + h * (- b2') = 0) as etr2. {
          replace (- b2') with (b1' - (b1 + b2)).
          2 : { rewrite <- sumb; lra. }
          assert (0 < / sqrt ((b1' - (b1 + b2))² + h'²)) as dgt0. {
            zltab.
            apply sqrt_lt_R0.
            apply Rplus_le_lt_0_compat; try (apply Rle_0_sqr).
            unfold Rsqr.
            apply Rmult_lt_0_compat; lra. }
          
          apply (Rmult_eq_reg_r (/ sqrt ((b1' - (b1 + b2))² + h'²))); try lra. }

        assert (b2' = b1 + b2 - b1') as b2d; try lra.
        assert ((b1 + b2) * (b1 - b1') = 0) as ctr. {
          setl (b1 * (b1 + b2 - b1') - b2 * b1').
          rewrite <- b2d.
          apply (Rplus_eq_reg_r (b2 * b1')).
          apply (Rmult_eq_reg_r (/ (b2' * b1')));
            [| zltab; apply Rmult_integral_contrapositive_currified; try zltab].
          setl (b1 / b1'); try lra.
          setr (b2 / b2'); try lra.

          assert (h / h' = b1 / b1') as hhd1. {
            apply (Rmult_eq_reg_r (h' * b1' / b1)).
            symmetry; lrag hrat; lra.
            rewrite <- RmultRinv.
            apply Rmult_integral_contrapositive_currified; try zltab.
            apply Rmult_integral_contrapositive_currified; try zltab. }

          assert (h / h' = b2 / b2') as hhd2. {
            apply (Rmult_eq_reg_r (h' * b2')).
            apply (Rplus_eq_reg_r (- (b2 / b2' * (h' * b2')))).
            setr (-0); try lra.
            setl (- (- h / h' * (h' * b2') + (b2 / b2' * (h' * b2')))); try lra.
            apply Ropp_eq_compat.
            lrag etr2; try lra.
            apply Rmult_integral_contrapositive_currified; try zltab. }

          lrag hrat. }

        apply Rmult_integral in ctr.
        destruct ctr; lra. }
        
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

Lemma sliding_triangle_obtuse :
  forall h b1 b2 h' b2'
         (zlth : 0 < h)
         (zltb1 : 0 < b1)
         (zltb2 : 0 < b2)
         (zlth' : 0 < h')
         (zltb2' : 0 <= b2')
         (b2o : b2' < b2)
         (hrat : h' = h * (b1 + b2') * / (b1 + b2)),
    sqrt((b1+b2')² + h'²) + sqrt(b2'² + h'²) <
    sqrt((b1+b2)² + h²) + sqrt(b2² + h²).
Proof.
  intros.

  specialize (triangle b1 0 (b1+b2') h' (b1+b2) h) as [tri|etri].
  2 : { exfalso.
        unfold dist_euc in *.
        apply colinear_coord in etri; try lra.
        replace (- (b1 + b2 - b1)) with (-b2) in etri by lra.
        replace (b1 + b2' - b1) with (b2') in etri by lra.
        autorewrite with null in etri.
        rewrite atan2_cos_id, atan2_sin_id in etri; try lra.
        repeat rewrite <- Rsqr_pow2 in etri.

        assert (- b2 * h' + h * b2' = 0) as etr2. {
          assert (0 < / sqrt (b2'² + h'²)) as dgt0. {
            zltab.
            apply sqrt_lt_R0.
            apply Rplus_le_lt_0_compat; try (apply Rle_0_sqr).
            unfold Rsqr.
            apply Rmult_lt_0_compat; lra. }
          
          apply (Rmult_eq_reg_r (/ sqrt (b2'² + h'²))); try lra. }

        assert (b2 = b2') as ctr. {
          apply (Rmult_eq_reg_r b1); try lra.
          apply (Rplus_eq_reg_r (b2' * b2)).
          setl ((b1 + b2') * b2).
          setr (b2' * (b1 + b2)).
             
          assert (h' / h = (b1 + b2') * / (b1 + b2)) as hhd1. {
            apply (Rmult_eq_reg_r h); try lra.
            lrag hrat; lra. }

          assert (h' / h = b2' / b2) as hhd2. {
            apply (Rmult_eq_reg_r (h * b2)).
            apply (Rplus_eq_reg_r (- (b2 * h'))).
            symmetry.
            lrag etr2.
            apply Rmult_integral_contrapositive_currified; try zltab. }

          apply (Rmult_eq_reg_r (/ ((b1 + b2)* b2)));
             [| zltab; apply Rmult_integral_contrapositive_currified; try zltab].
          rewrite hhd2 in hhd1.
          symmetry.
          lrag hhd1. }
        lra. }

  unfold dist_euc in tri.
  autorewrite with null in tri.
  assert (forall x, (b1 - (b1 + x))= (- x)) as id; try (intros; lra).
  repeat rewrite id in *; clear id.
  assert ((b1 + b2 - (b1 + b2')) = (b2 - b2')) as id; try lra.
  rewrite id in *; clear id.
  repeat rewrite <- Rsqr_neg in tri.

  set (p1 := sqrt ((b1+b2')² + h'²)) in *.
  set (q1 := sqrt (b2² + h²)) in *.
  set (q2 := sqrt (b2'² + h'²)) in *.
  set (p1p2 := sqrt ((b1+b2)² + h²)) in *.
  set (p2 := sqrt ((b2 - b2')² + (h - h')²)) in *.
  assert (p1p2 = p1 + p2) as id. {
    unfold p1p2, p1, p2.
    replace ((b1+b2')² + h'²) with (((b1+b2') * / (b1+b2))² * ((b1+b2)² + h²)). {
      rewrite hrat.
      replace (b2-b2') with ((b1+b2) * (1 - (b1+b2') * / (b1+b2))) by (field; try lra).
      assert (((b1+b2)² + h²) * (1 - ((b1+b2') * / (b1+b2)))² =
              ((b1 + b2) * (1 - (b1 + b2') * / (b1 + b2)))² + (h - h * (b1 + b2') * / (b1 + b2))²)
        as id. {
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
      apply (Rmult_le_reg_r (b1+b2)); try lra;
        arn;
        setr (b2 - b2'); lra.
      apply (Rmult_le_reg_r (b1+b2)); try lra;
        arn;
        setr (b1+b2'); lra.
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
  
Lemma smaller_interior_path_triangle_obtuse :
  forall h b1 b2 b2' h' 
         (zlth : 0 < h' < h)
         (zltb1 : 0 < b1)
         (zltb2' : 0 < b2' < b2)
         (wtn : h / b2 < h' / b2')
         (wto : h' / (b1+b2') < h / (b1+b2)),
    sqrt((b1+b2')² + h'²) + sqrt(b2'² + h'²) <
    sqrt((b1+b2)² + h²) + sqrt(b2² + h²).
Proof.
  intros.
  set (h'' := (b1+b2') * h / (b1+b2)).
  apply (Rlt_le_trans _ (sqrt((b1+b2')² + h''²) + sqrt(b2'² + h''²))).
  + apply squatting_triangle; try lra; unfold h''.
    zltab.
    lra.
    split; try lra.
    apply (Rmult_lt_reg_r (/ (b1 + b2'))).
    zltab; try lra.
    lrag wto.
  + left; apply sliding_triangle_obtuse; try lra.
    unfold h''.
    zltab; try lra.
    unfold h''.
    field; try lra.
Qed.


Lemma smaller_interior_path_triangle_acute :
  forall h b1 b2 h' b1' b2'
         (zlth : 0 < h)
         (zltb1 : 0 < b1)
         (zltb2 : 0 < b2)
         (zlth' : 0 <= h')
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

  destruct zlth' as [zlth' | zlth'eq].
  (* h,b1,b2 is outer triangle, h',b1',b2' is a triangle that is sliding down one arm, 
     h'',b1',b2' is a triangle construced from the slid triangle that is also squatting *)
  - rename h' into h''.
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
      
      left; apply sliding_triangle_acute; try lra.
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
      left; apply sliding_triangle_acute; try lra.
      unfold h'.
      apply (Rmult_lt_reg_r b2); try lra.
      setl 0.
      setr (h * b2').
      lra.
      zltab.
      unfold h'.
      reflexivity.

  - rewrite <- zlth'eq in *; clear zlth'eq.
    autorewrite with null in *.
    repeat rewrite sqrt_Rsqr; try (left; lra).
    rewrite <- sumb.
    rewrite <- (sqrt_Rsqr b1) at 1; try lra.
    rewrite <- (sqrt_Rsqr b2) at 1; try lra.
    apply Rplus_lt_compat.

    apply sqrt_lt_1.
    apply Rle_0_sqr.
    left; apply posss.
    lra.
    apply (Rplus_lt_reg_r (-(b1)²)).
    setl 0.
    setr (h²).
    apply Rlt_0_sqr; try lra.
    
    apply sqrt_lt_1.
    apply Rle_0_sqr.
    left; apply posss.
    lra.
    apply (Rplus_lt_reg_r (-(b2)²)).
    setl 0.
    setr (h²).
    apply Rlt_0_sqr; try lra.
Qed.

(* Relative length between a path created by
   two lines intersecting the origin,
   and another created by two lines intersecting 
   the point (x,0). *)

(*
  outer triangle   y = m * x
                   y = n * (x - k)
  inner triangle   y = m1 * x
                   y = n1 * (x - k)
*)

Lemma shorter_two_step_linear_path :
  forall m n m1 n1 k
         (ziso : 0 < m1 < m) (* origin intercept slopes *)
         (kiso : n < n1 < 0 \/ 0 < n < n1 \/ n1 < 0 < n) (* k x-intercept slope order *)
         (kpos : 0 < k)
         (int : (m < n /\ n > 0) \/ ( n < 0)),
    let Px :=  k * n / (n - m) in
    let Py :=  m * Px in
    let Qx :=  k * n1 / (n1 - m1) in
    let Qy :=  m1 * Qx in
    sqrt (Qx² + Qy²) + sqrt ((Qx - k)² + Qy²) <
    sqrt (Px² + Py²) + sqrt ((Px - k)² + Py²).
Proof.
  intros.
  
  destruct (total_order_T n 0) as [[nlt0 |neq0] |ngt0];
    destruct (total_order_T n1 0) as [[n1lt0 |n1eq0] |n1gt0];
    destruct int as [int |int];
    try lra.
  + assert (0 < Px) as pxgt0. {
      unfold Px, Py.
      setr (k * (-n) / (-n + m)); try lra.
      zltab; lra. }
    assert (0 < Py) as pygt0. {
      unfold Py; zltab. }
    assert (0 < Qx) as qxgt0. {
      unfold Qx, Qy.
      setr (k * (-n1) / (-n1 + m1)); try lra.
      zltab; lra. }
    assert (0 < Qy) as qygt0. {
      unfold Qy; zltab. }

    rewrite (Rsqr_neg (Px - k)).
    rewrite (Rsqr_neg (Qx - k)).
    apply smaller_interior_path_triangle_acute; try lra.
    
    unfold Px, Py.
    setr (k * (1 - (-n) / (- n + m))); try lra.
    zltab.
    apply (Rmult_lt_reg_r (- n + m)); try lra.
    setl 0.
    setr (m); lra.

    unfold Qx, Qy.
    setr (k * (1 - (-n1) / (- n1 + m1))); try lra.
    zltab.
    apply (Rmult_lt_reg_r (- n1 + m1)); try lra.
    setl 0.
    setr (m1); lra.

    unfold Qy, Py.
    apply (Rmult_lt_reg_r (/ (Px * Qx))); try zltab.
    setl m1; try lra.
    setr m; lra.

    unfold Py, Qy, Px, Qx.
    replace (k * n / (n - m) - k) with (k * (m / (n-m))).
    replace (k * n1 / (n1 - m1) - k) with (k * (m1 / (n1-m1))).
    setl (m1 * (k * (-n1) / (- n1 + m1)) * (k * (m / (- n + m)))); try lra.
    setr (m * (k * (-n) / (- n + m)) * (k * (m1 / (- n1 + m1)))); try lra.
    apply (Rmult_lt_reg_r (/ (m1 * (k * / (- n1 + m1)) * (k * (m / (- n + m)))))).
    zltab; try lra.
    setl (-n1); try lra.
    setr (-n); lra.

    field_simplify; lra.
    field_simplify; lra.

  + assert (0 < Px) as pxgt0. {
      unfold Px, Py.
      zltab; lra. }
    assert (0 < Py) as pygt0. {
      unfold Py; zltab. }
    assert (0 < Qx) as qxgt0. {
      unfold Qx, Qy.
      setr (k * (-n1) / (- n1 + m1)); try lra.
      zltab; lra. }
    assert (0 < Qy) as qygt0. {
      unfold Qy; zltab. }

    rewrite (Rsqr_neg (Qx - k)).
    set (Qy' := m * Qx).

    apply (Rlt_trans _ (sqrt (Qx² + Qy'²) + sqrt ((- (Qx - k))² + Qy'²))).
    apply squatting_triangle; try lra.
    unfold Qy'; zltab.
    unfold Qx.
    setr (k * (1 - (-n1) / (- n1 + m1))); try lra.
    zltab.
    apply (Rplus_lt_reg_r (- n1 / (- n1 + m1))).
    apply (Rmult_lt_reg_r (-n1 + m1)); try lra.
    setl (-n1); lra.
    unfold Qy, Qy'.
    split; try lra.
    zltab.
    apply (Rmult_lt_reg_r (/ Qx)); [zltab|].
    setl m1; try lra.
    setr m; lra.
    
    set (Qy'' := m * k).
    assert (Qx < k) as qxltk. {
      unfold Qx.
      setl (k * ((-n1) / (m1 - n1))); try lra.
      rewrite <- (Rmult_1_r k) at 2.
      apply Rmult_lt_compat_l; try assumption.
      apply (Rmult_lt_reg_r (m1 - n1)); try lra.
      setl (-n1); lra. }

    apply (Rlt_trans _ (sqrt (k² + Qy''²) + sqrt (0² + Qy''²))).
    ++ apply sliding_triangle_acute; try lra.
       unfold Qy''; apply Rmult_lt_0_compat; lra.
       unfold Qy'; apply Rmult_lt_0_compat; lra.
       unfold Qy'', Qy'; field; lra.

    ++ assert (0 < Px - k) as pxkgt0. {
         unfold Px.
         apply (Rplus_lt_reg_r k).
         apply (Rmult_lt_reg_r ((n - m) * / k)); try zltab.
         setl (n - m); try lra.
         setr (n); lra. }

       replace k with (k + 0) at 1 by lra.
       replace Px with (k + (Px - k)) at 1 by lra.
       apply sliding_triangle_obtuse; try lra.
       unfold Qy''; apply Rmult_lt_0_compat; lra.
       unfold Qy'', Py, Px; field.
       split; try lra.
       replace (k * (n - m) + (k * n - k * (n - m))) with (k * n); try lra.
       apply Rmult_integral_contrapositive_currified; try zltab.

  + assert (0 < Px) as pxgt0. {
      unfold Px, Py.
      zltab; lra. }
    assert (0 < Py) as pygt0. {
      unfold Py; zltab. }
    assert (0 < Qx) as qxgt0. {
      unfold Qx, Qy.
      zltab; lra. }
    assert (0 < Qy) as qygt0. {
      unfold Qy; zltab. }

    assert (Qy < Py) as qyltpy. {
      unfold Qy, Py, Qx, Px.
      apply Rmult_gt_0_lt_compat; try lra.
      apply Rlt_gt.
      zltab; lra.
      
      setl (k * (n1 / (n1 - m1))); try lra.
      setr (k * (n / (n - m))); try lra.
      apply Rmult_lt_compat_l; try lra.
      apply (Rmult_lt_reg_r ((n1-m1)*(n-m))); try zltab.
      apply (Rplus_lt_reg_r (- n1 * n)).
      setl (- (n1 * m)); try lra.
      setr (- (n * m1)); try lra.
      apply Ropp_lt_contravar.
      apply Rmult_gt_0_lt_compat; try lra. }

    assert (k < Qx) as kltqx. {
      unfold Qx.
      rewrite <- (Rmult_1_r k) at 1.
      setr (k * (n1 / (n1 - m1))); try lra.
      apply Rmult_lt_compat_l; try lra.
      apply (Rmult_lt_reg_r (n1 - m1)); try lra.
      setl (n1 - m1).
      setr (n1); lra. }

    destruct kiso as [kiso | kiso]; try lra.
    destruct kiso as [kiso | kiso]; try lra.

    assert (Qx < Px) as qxltpx. {
      unfold Qx, Px.
      apply (Rmult_lt_reg_r (/ k * (n1 - m1) * (n -m ))); try zltab.
      apply (Rplus_lt_reg_r (- n1 * n)).
      setl (- (n1 * m)); try lra.
      setr (- (m1 * n)); try lra.
      apply Ropp_lt_contravar.
      rewrite Rmult_comm.
      apply Rmult_gt_0_lt_compat; try lra. }

    replace (Qx² + Qy²) with ((k + (Qx - k))² + Qy²).
    replace (Px² + Py²) with ((k + (Px - k))² + Py²).
    destruct int as [mltn zltn].
    apply smaller_interior_path_triangle_obtuse; try lra.

    (* n < n1 *)
    unfold Py, Qy, Px, Qx.
    setl (n).
    split; try lra.
    replace (k * n - k * (n - m)) with (k * m) by try lra.
    apply Rmult_integral_contrapositive_currified; try lra.
    setr n1.
    split; try lra.
    replace (k * n1 - k * (n1 - m1)) with (k * m1) by try lra.
    apply Rmult_integral_contrapositive_currified; try lra.
    lra.

    replace (k + (Qx - k)) with Qx by lra.
    replace (k + (Px - k)) with Px by lra.

    (* m1 < m *)
    unfold Qy, Py, Qx, Px.
    setl m1; try lra.
    setr m; lra.

    replace (k + (Px - k)) with Px by lra; reflexivity.
    replace (k + (Qx - k)) with Qx by lra; reflexivity.
Qed.

    
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


(*  pri : (x - xi) * cos η + (y - yi) * sin η = 0
  prj : (x - r * sin (θ1 x y r)) * sin (θ1 x y r) = (y - r * (1 - cos (θ1 x y r))) * cos (θ1 x y r)
  ============================
  cos η * cos (θ1 x y r) + sin η * sin (θ1 x y r) = 0
*)
(*
Lemma pattern : forall a b b' c d d',
    a <> 0  -> c <> 0 ->
    a * b + c * d = 0 ->
    a * b' + c * d' = 0 ->
    b = b' /\ d = d'.
Proof.
  intros * anz cnz c1 c2.
  apply Rplus_opp_r_uniq in c1.
  apply Rplus_opp_r_uniq in c2.
  assert (d * b' = d' * b ) as id. admit.

  apply (Rmult_

  destruct 
  SearchPattern (_ + _ = 0 -> _).
                       
*)

(* Choosing y>0 because this is the second component of an
approximation that is intended to tile the area around the turning
circle. This constraint does not limit us in a significant way, only
that a single "tile" cannot take up more that PI of angular extent
around the circle, so we need to tile the circumference with at least
two. *)
Lemma minlength_inner_infinite_hat_straight_std :
  forall r x y φ₂
         (p1p2 : 0 < φ₂)
         (p2ub : φ₂ < 2 * PI)
         (lt : 0 < r)
         (zlty : 0 < y)
         (oc : 2 * r * y < x² + y²),
    let nx := cos φ₂ in
    let ny := sin φ₂ in
    let wx := r*sin φ₂ in
    let wy := r*(1 - cos φ₂) in
    (nx * (y - wy) <= ny * (x - wx) /\ wx * y >= wy * x) -> 
    sqrt (wx² + wy²) + sqrt ((x - wx)² + (y - wy)²) <= L x y (θ1 x y r) r.
Proof.
  intros until 5.
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
    rewrite <- (Rsqr_neg aiy'), <- (Rsqr_neg ay').
    
    rewrite (Rsqr_neg (x' - aix')).
    rewrite (Rsqr_neg (x' - ax')).
    replace (- (x' - aix')) with (aix' - x') by lra.
    replace (- (x' - ax')) with (ax' - x') by lra.
    left.
    set (k := x') in *.

    specialize (posss _ _ no) as zltx2y2. 
    assert (0 < sqrt (x² + y²)) as zltrx2y2. {
      apply sqrt_lt_R0.
      assumption. }
    
    assert (0 < k) as zltk. {
      unfold k, x'.
      unfold η.
      rewrite atan2_cos_id; try lra.
      rewrite atan2_sin_id; try lra.
      repeat rewrite <- Rsqr_pow2.
      apply (Rmult_lt_reg_r (sqrt (x² + y²))); try lra.
      arn.
      setr (x² + y²); try lra.
      unfold Rsqr in zltrx2y2.
      lra. }


    (* Here are the things we need below:
       ax' <> 0 /\ k - ax' <> 0 /\ ay' * ax' - - ay' * (k - ax') <> 0 /\
       ay' <> 0 *)
    assert (ax' <> 0) as nl_ax'ne0. {
      unfold ax'.

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
      assert (0 < M) as zltm. {
        unfold M.
        apply sqrt_lt_R0.
        apply posss.
        lra. }
      intro ctr.
      apply (Rmult_eq_compat_r (/ M)) in ctr.
      assert (cos e * cos θ + sin e * sin θ = 0) as ctr2; try lrag ctr.
      rewrite <- cos_minus in ctr2.
      assert (θ = θ1 x y r / 2) as tdef. lra.

      
      destruct (total_order_T 0 y); [destruct s|].
      +++ rewrite tdef in ctr2.
           specialize (root_ordering_rpos_left _ _ _ lt r0 oc) as [rorl roru].
           change (θ1 x y r < θmax) in rorl.
           clear roru.

           apply cosθeq0 in ctr2.

           destruct (Rlt_dec 0 x) as [zltx | zgex].
          ++++ assert (0 < e <= PI/2) as [elb eub]. {
                  rewrite ed.
                  unfold θmax.
                  rewrite thms.
                  fieldrewrite (2 * atan2 y x / 2) (atan2 y x).
                  specialize (atan2Q1 _ _ zltx r0) as at2b.
                  lra. }
                lra.
          ++++ apply Rnot_lt_le in zgex.
               destruct zgex as [xlt0 |xeq0].
               assert (PI / 2 < e < PI) as [el eu]. {
                 rewrite ed.
                 unfold θmax.
                 rewrite thms.
                 fieldrewrite (2 * atan2 y x / 2) (atan2 y x).
                 apply (atan2Q2 _ _ xlt0 r0).
               }
               (* x < 0 part *)
               specialize (tinrng _ _ _ _ _ _ oc) as t1rng.
               autorewrite with null in t1rng.
               simpl in t1rng.
               change (0 < r * θ1 x y r < Rabs r * 2 * PI ->
                       0 < θmax /\
                       (θmax / 2 < θ1 x y r < θmax \/
                        -2 * PI < θ1 x y r < θmax / 2 - 2 * PI) \/
                       θmax < 0 /\
                       (θmax < θ1 x y r < θmax / 2 \/
                        θmax / 2 + 2 * PI < θ1 x y r < 2 * PI)) in t1rng.
               rewrite <- ed in *.
               assert (0 < r * θ1 x y r < Rabs r * 2 * PI) as cond. {
                 split.
                 zltab.
                 apply (Rmult_lt_reg_r (/r)); try zltab.
                 setl (θ1 x y r); try lra.
                 rewrite Rabs_right; try lra.
                 setr (2 * PI); lra. }
               specialize (t1rng cond).
               assert (0 < θmax) as zlttm. {
                 unfold θmax.
                 rewrite thms.
                 apply (Rmult_lt_reg_r (/2)); try lra. }
               destruct t1rng as [t1rng|t1rng]; lra.
               
                (* x = 0 part *)
                assert (e = PI / 2) as epi2. {
                  rewrite ed.
                  unfold θmax.
                  rewrite thms, xeq0, atan2_PI2;
                    lra. }
                rewrite epi2 in ctr2.
                lra.

          ++++ lra.
      +++ destruct (Rlt_dec 0 x) as [zltx | zgex].
          ++++ clear - lb zltx e0 lt p1p2 p2ub.
               rewrite <- e0 in *.
               autorewrite with null in lb.
               assert (0 < wy) as zlewy. {
                 unfold wy.
                 apply Rmult_lt_0_compat.
                 assumption.
                 specialize (COS_bound φ₂) as [clb cub].
                  destruct cub.
                  lra.
                  apply cosθeq1 in H; try lra. }
               exfalso.
               generalize lb.
               change (~ 0 >= wy * x).
               apply Rlt_not_ge.
               zltab.
          ++++ apply Rnot_lt_le in zgex.
                destruct zgex as [xlt |xeq].
                symmetry in e0.
                specialize (root_ordering_nxarm _ _ _ lt e0 xlt oc) as [t1tm [tmt2 [t1l t1u]]].
                change (θ1 x y r < θmax) in t1tm.
                clear tmt2.
                change (PI < θ1 x y r) in t1l.
                apply cosθeq0 in ctr2; try lra.
                lra.
                
      +++ lra. }
    
    assert (ay' <> 0) as nl_ay'ne0. {
      unfold ay'.

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
      assert (0 < M) as zltm. {
        unfold M.
        apply sqrt_lt_R0.
        apply posss.
        lra. }
      intro ctr.
      apply (Rmult_eq_compat_r (/ M)) in ctr.
      assert (sin θ * cos e - cos θ * sin e  = 0) as ctr2; try lrag ctr.

      rewrite <- sin_minus in ctr2.
      assert (θ = θ1 x y r / 2) as tdef. lra.

      
      destruct (total_order_T 0 y); [destruct s|].
      +++ rewrite tdef in ctr2.
           specialize (root_ordering_rpos_left _ _ _ lt r0 oc) as [rorl roru].
           change (θ1 x y r < θmax) in rorl.
           clear roru.

           apply sinθeq0 in ctr2.
           rewrite ed in ctr2.

           destruct ctr2; lra.
           lra.
           
      +++ destruct (Rlt_dec 0 x) as [zltx | zgex]; try lra.
      +++ lra. }


    destruct (Req_dec k ax') as [keqax' | kneax']. {
      admit. }
      
(********** marked ***************)
(*
  outer triangle   y = m * x
                   y = n * (x - k)
  inner triangle   y = m1 * x
                   y = n1 * (x - k)
*)
    
    set (m := - ay' / ax').
    set (m1 := - aiy'/ aix').
    set (n := ay' / (k - ax')).
    set (n1 := aiy' / (k - aix')).
    set (Qx := k * n1 / (n1 - m1)).
    set (Qy := m1 * Qx).
    set (Px := k * n / (n - m)).
    set (Py := m * Px).

    
    (* aix' <> 0 /\ k - aix' <> 0 /\ aiy' * aix' - - aiy' * (k - aix') <> 0 *)
    assert (Qx² + Qy² = aix'² + aiy'²) as lhs1. {
      unfold Qy, Qx, n1, m1.
      setl (aix'² + aiy'²); try lra.
      admit. }
    assert ((Qx - k)² + Qy² = (aix' - k)² + aiy'²) as lhs2. {
      unfold Qy, Qx, n1, m1.
      setl ((aix' - k)² + aiy'²); try lra.
      admit. }
    assert (Px² + Py² = ax'² + ay'²) as rhs1. {
      unfold Py, Px, n, m.
      setl (ax'² + ay'²); try lra.
      admit. }
    assert ((Px - k)² + Py² = (ax' - k)² + ay'²) as rhs2. {
      unfold Py, Px, n, m.
      setl ((ax' - k)² + ay'²); try lra.
      admit. }

    rewrite <- lhs1, <- lhs2, <- rhs1, <- rhs2.
    apply shorter_two_step_linear_path; try assumption.
    admit.
    admit.
    admit.
  + admit.
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


