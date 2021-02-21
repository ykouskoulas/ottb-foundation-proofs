(* begin hide *)
Require Import Reals.
Require Import Ranalysis5.
Require Import FunctionalExtensionality.
Require Import Coquelicot.Coquelicot.
Require Import Omega.
Require Import Lia.
Require Import Lra.
Require Import ssrsearch.

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



Lemma maxlength_outer_infinite_hat_straight_std :
  forall r x y φ₂
         (p1p2 : 0 < φ₂)
         (p2ub : φ₂ < 2 * PI)
         (lt : 0 < r)
         (oc : 2 * r * y < x² + y²),
    let wx := r*sin φ₂ in
    let wy := r*(1 - cos φ₂) in
    y >= 0 /\ wx * y <= wy * x -> 
    L x y (θ1 x y r) r <= r * φ₂ + sqrt ((x - wx)² + (y - wy)²).
Proof.
  intros * p2lb p2ub rgt0 oc * [ygt0 ld].

         
  destruct (total_order_T 0 x) as [[zltx|zeq0]|zgtx].
  + unfold L.
    apply condstraight in oc.
    apply (Rplus_le_reg_r (- r * θ1 x y r)).
    (* setl (sqrt (x² - (2 * r - y) * y)). *)
    setl (sqrt ((x - r * sin (θ1 x y r))² + (y - r * (1 - cos (θ1 x y r)))²)).
    setr (r * (φ₂  - θ1 x y r) + sqrt ((x - wx)² + (y - wy)²)).
    apply (Rle_trans _ (sqrt ((x - wx)² + (y - wy)²) +
                        sqrt ((wx - r * sin (θ1 x y r))² + (wy - r * (1 - cos (θ1 x y r)) )²))).
    ++ apply triangle.
    ++ apply (Rplus_le_reg_r (- sqrt ((x - wx)² + (y - wy)²))).
       setl (sqrt ((wx - r * sin (θ1 x y r))² + (wy - r * (1 - cos (θ1 x y r)))²)).
       setr (r * (φ₂ - θ1 x y r)).
       
       apply (Rle_trans _ (sqrt ((r * sin (φ₂ - θ1 x y r))² + (r * (1 - cos (φ₂ - θ1 x y r)))²))).
       +++ unfold wx, wy.
           apply sqrt_le_1_alt.
           repeat rewrite Rsqr_minus.
           setl (r² * ((sin φ₂)² + (sin (θ1 x y r))² - 2 * sin φ₂ * sin (θ1 x y r) +
                       (1 - cos φ₂)² + (1 - cos (θ1 x y r))² -
                                       2 * (1 - cos φ₂) * (1 - cos (θ1 x y r)))).
           setr (r² * ((sin (φ₂ - θ1 x y r))² + (1 - cos (φ₂ - θ1 x y r))²)).
           repeat rewrite Rsqr_minus.
           replace ((sin φ₂)² + (sin (θ1 x y r))² - 2 * sin φ₂ * sin (θ1 x y r)
                    + (1² + (cos φ₂)² - 2 * 1 * cos φ₂) + (1² + (cos (θ1 x y r))²
                    - 2 * 1 * cos (θ1 x y r)) - 2 * (1 - cos φ₂) * (1 - cos (θ1 x y r))) with
               (((sin φ₂)² + (cos φ₂)²) + ((sin (θ1 x y r))² + (cos (θ1 x y r))²)
              - 2 * sin φ₂ * sin (θ1 x y r) + 1 - 2 * cos φ₂ + 1 
             - 2 * 1 * cos (θ1 x y r) - 2 * (1 - cos φ₂) * (1 - cos (θ1 x y r)))
           by (unfold Rsqr; lra).
         replace ((sin (φ₂ - θ1 x y r))² + (1² + (cos (φ₂ - θ1 x y r))²
                  - 2 * 1 * cos (φ₂ - θ1 x y r))) with
             (((sin (φ₂ - θ1 x y r))² + (cos (φ₂ - θ1 x y r))²)
              + 1 - 2 * cos (φ₂ - θ1 x y r))
           by (unfold Rsqr; lra).
         repeat rewrite sin2_cos2.
         rewrite cos_minus.
         lra.
     +++ assert (2 * r * (r * (1 - cos (φ₂ - θ1 x y r))) =
                 (r * sin (φ₂ - θ1 x y r))² + (r * (1 - cos (φ₂ - θ1 x y r)))²) as id. {
           repeat rewrite Rsqr_mult.
           rewrite Rsqr_minus.
           setr (r² * (((sin (φ₂ - θ1 x y r))² + (cos (φ₂ - θ1 x y r))²)
                       + 1 - 2 * cos (φ₂ - θ1 x y r))).
           rewrite sin2_cos2.
           unfold Rsqr.
           field. }

           destruct ygt0 as [ygt0 | yeq0].
           2 : {
             rewrite <- id.
             replace (φ₂ - θ1 x y r) with φ₂.
             apply Rsqr_incr_0; [|apply sqrt_pos| zltab].
             rewrite Rsqr_sqrt; [| zltab ;specialize (COS_bound φ₂) as [lb ub]; try lra].
             apply (Rmult_le_reg_l (/ (4 * r * r))); try zltab.
             setl ((1 - cos φ₂) / 2); try lra.
             setr ((φ₂ / 2)²); try lra.
             rewrite <- sint22.
             apply Rsqr_incr_1; try lra.
             left.
             apply (Rplus_lt_reg_r (- sin (φ₂ / 2))).
             setl 0.
             setr (φ₂ / 2  - sin (φ₂ / 2)).
             apply x_minus_sin_x_pos; try lra.
             apply sin_ge_0; try lra.
             rewrite yeq0.
             
             unfold θ1.
             destruct total_order_T as [[ltr|eqr]|gtr]; try lra.
             destruct total_order_T as [[ltx|eqx]|gtx]; try lra.
             destruct total_order_T as [[lt0|eq0]|gt0]; try lra.
           }
           
           assert (0 < φ₂ - θ1 x y r < 2 * PI) as ab. {
             destruct (total_order_T φ₂ PI) as [[plt|peq]|pgt];
               destruct (total_order_T 0 (2 * r - y)) as [[lt|eq]|gt].
             ++ (* phi2 lt pi *)
               specialize (root_ordering_Q1bot _ _ _ rgt0 lt ygt0 zltx oc)
                 as [[tml tmu] [[t1rl t1ru] t2r]].
               clear tmu t2r.
               split; try lra.
               apply (Rplus_lt_reg_r (θ1 x y r)).
               arn.
               setr φ₂.
               apply (Rlt_le_trans _ (calcθ₁ 0 0 0 x y)); try lra.
               rewrite thms; try lra.
               rewrite <- (chord_property r); try lra.
               apply Rmult_le_compat_l; try lra.
               assert (0 < sin φ₂) as sp2gt0. {
                 apply sin_gt_0; try lra. }

               assert (0 < 1 - cos φ₂) as omcp2gt0. {
                 specialize (COS_bound φ₂) as [cbl [cbu |cbe]].
                 lra.
                 apply cosθeq1 in cbe ;try lra. }

               repeat rewrite atan2_atan_Q1; try lra; try zltab.
                
               destruct ld as [ldlt |ldeq].
               +++ left.
                   apply atan_increasing.
                   change (y / x < wy / wx).
                   apply (Rmult_lt_reg_r (wx * x)).
                   unfold wx.
                   zltab.
                   setl (wx * y); try lra.
                   setr (wy * x); try lra.
                   unfold wx.
                   apply Rmult_integral_contrapositive_currified; lra.
                   
               +++ change (atan (y / x) <= atan (wy / wx)).
                   right; f_equal.
                   apply (Rmult_eq_reg_r (x * wx)).
                   2 : {
                     apply Rmult_integral_contrapositive_currified ; try lra.
                     unfold wx.
                     zltab.
                     apply Rmult_integral_contrapositive_currified; lra. }

                   setl (wx * y); try lra.
                   setr (wy * x); try lra.
                   unfold wx.
                   zltab.
                   apply Rmult_integral_contrapositive_currified; lra.
             ++ (* phi2 lt pi *)
               specialize (root_ordering_Q1arm _ _ _ rgt0 eq ygt0 zltx oc)
                 as [[tml tmu] [t1rl t1ru]].
               clear tmu.
               split; try lra.
               apply (Rplus_lt_reg_r (θ1 x y r)).
               arn.
               setr φ₂.
               apply (Rlt_le_trans _ (calcθ₁ 0 0 0 x y)); try lra.
               rewrite thms; try lra.
               rewrite <- (chord_property r); try lra.
               apply Rmult_le_compat_l; try lra.
               assert (0 < sin φ₂) as sp2gt0. {
                 apply sin_gt_0; try lra. }

               assert (0 < 1 - cos φ₂) as omcp2gt0. {
                 specialize (COS_bound φ₂) as [cbl [cbu |cbe]].
                 lra.
                 apply cosθeq1 in cbe ;try lra. }

               repeat rewrite atan2_atan_Q1; try lra; try zltab.
                
               destruct ld as [ldlt |ldeq].
               +++ left.
                   apply atan_increasing.
                   change (y / x < wy / wx).
                   apply (Rmult_lt_reg_r (wx * x)).
                   unfold wx.
                   zltab.
                   setl (wx * y); try lra.
                   setr (wy * x); try lra.
                   unfold wx.
                   apply Rmult_integral_contrapositive_currified; lra.
                   
               +++ change (atan (y / x) <= atan (wy / wx)).
                   right; f_equal.
                   apply (Rmult_eq_reg_r (x * wx)).
                   2 : {
                     apply Rmult_integral_contrapositive_currified ; try lra.
                     unfold wx.
                     zltab.
                     apply Rmult_integral_contrapositive_currified; lra. }

                   setl (wx * y); try lra.
                   setr (wy * x); try lra.
                   unfold wx.
                   zltab.
                   apply Rmult_integral_contrapositive_currified; lra.
             ++ (* phi2 lt pi *)
               specialize (root_ordering_Q1top x y r rgt0 gt ltac:(lra) oc)
                 as [[tml tmu] [[t1rl t1ru] t2r]].
               clear tmu t2r.
               split; try lra.
               apply (Rplus_lt_reg_r (θ1 x y r)).
               arn.
               setr φ₂.
               apply (Rlt_le_trans _ (calcθ₁ 0 0 0 x y)); try lra.
               rewrite thms; try lra.
               rewrite <- (chord_property r); try lra.
               apply Rmult_le_compat_l; try lra.
               assert (0 < sin φ₂) as sp2gt0. {
                 apply sin_gt_0; try lra. }

               assert (0 < 1 - cos φ₂) as omcp2gt0. {
                 specialize (COS_bound φ₂) as [cbl [cbu |cbe]].
                 lra.
                 apply cosθeq1 in cbe ;try lra. }

               repeat rewrite atan2_atan_Q1; try lra; try zltab.
                
               destruct ld as [ldlt |ldeq].
               +++ left.
                   apply atan_increasing.
                   change (y / x < wy / wx).
                   apply (Rmult_lt_reg_r (wx * x)).
                   unfold wx.
                   zltab.
                   setl (wx * y); try lra.
                   setr (wy * x); try lra.
                   unfold wx.
                   apply Rmult_integral_contrapositive_currified; lra.
                   
               +++ change (atan (y / x) <= atan (wy / wx)).
                   right; f_equal.
                   apply (Rmult_eq_reg_r (x * wx)).
                   2 : {
                     apply Rmult_integral_contrapositive_currified ; try lra.
                     unfold wx.
                     zltab.
                     apply Rmult_integral_contrapositive_currified; lra. }

                   setl (wx * y); try lra.
                   setr (wy * x); try lra.
                   unfold wx.
                   zltab.
                   apply Rmult_integral_contrapositive_currified; lra.

             ++ specialize (root_ordering_Q1bot _ _ _ rgt0 lt ygt0 zltx oc)
                 as [[tml tmu] [[t1rl t1ru] t2r]].
                split; lra.

             ++ specialize (root_ordering_Q1arm _ _ _ rgt0 eq ygt0 zltx oc)
                 as [[tml tmu] [t1rl t1ru]].
                split; lra.

             ++ specialize (root_ordering_Q1top x y r rgt0 gt ltac:(lra) oc)
                 as [[tml tmu] [[t1rl t1ru] t2r]].
                split; lra.

             ++ specialize (root_ordering_Q1bot _ _ _ rgt0 lt ygt0 zltx oc)
                 as [[tml tmu] [[t1rl t1ru] t2r]].
                split; lra.

             ++ specialize (root_ordering_Q1arm _ _ _ rgt0 eq ygt0 zltx oc)
                 as [[tml tmu] [t1rl t1ru]].
                split; lra.

             ++ specialize (root_ordering_Q1top x y r rgt0 gt ltac:(lra) oc)
                 as [[tml tmu] [[t1rl t1ru] t2r]].
                split; lra. }

           assert (r * (1 - cos (φ₂ - θ1 x y r)) > 0) as id2. {
             apply Rlt_gt.
             zltab.
             specialize (COS_bound (φ₂ - θ1 x y r)) as [cl [cu |ce]]; try lra.
             apply cosθeq1 in ce; lra. }

           assert (calcθ₁ 0 0 0 (r * sin (φ₂ - θ1 x y r)) (r * (1 - cos (φ₂ - θ1 x y r))) =
                   (φ₂ - θ1 x y r)) as id3. {
             unfold calcθ₁.
             arn.
             apply chord_property; lra. }
           rewrite <- id3 at 3.
           apply (underapprox_turning_std _ _ _ rgt0 id id2).

  + (* template inserted here *)
    apply condstraight in oc.
    specialize (theta1_rsgn_bnd _ _ r ltac:(lra) oc) as [ls rs].
    specialize (ls rgt0).
    unfold L.

    apply (Rplus_le_reg_r (- r * θ1 x y r)).
    (* setl (sqrt (x² - (2 * r - y) * y)). *)
    setl (sqrt ((x - r * sin (θ1 x y r))² + (y - r * (1 - cos (θ1 x y r)))²)).
    setr (r * (φ₂  - θ1 x y r) + sqrt ((x - wx)² + (y - wy)²)).
    apply (Rle_trans _ (sqrt ((x - wx)² + (y - wy)²) +
                        sqrt ((wx - r * sin (θ1 x y r))² + (wy - r * (1 - cos (θ1 x y r)) )²))).
    ++ apply triangle.
    ++ apply (Rplus_le_reg_r (- sqrt ((x - wx)² + (y - wy)²))).
       setl (sqrt ((wx - r * sin (θ1 x y r))² + (wy - r * (1 - cos (θ1 x y r)))²)).
       setr (r * (φ₂ - θ1 x y r)).

       apply (Rle_trans _ (sqrt ((r * sin (φ₂ - θ1 x y r))² + (r * (1 - cos (φ₂ - θ1 x y r)))²))).
       +++ unfold wx, wy.
           apply sqrt_le_1_alt.
           repeat rewrite Rsqr_minus.
           setl (r² * ((sin φ₂)² + (sin (θ1 x y r))² - 2 * sin φ₂ * sin (θ1 x y r) +
                       (1 - cos φ₂)² + (1 - cos (θ1 x y r))² -
                                       2 * (1 - cos φ₂) * (1 - cos (θ1 x y r)))).
           setr (r² * ((sin (φ₂ - θ1 x y r))² + (1 - cos (φ₂ - θ1 x y r))²)).
           repeat rewrite Rsqr_minus.
           replace ((sin φ₂)² + (sin (θ1 x y r))² - 2 * sin φ₂ * sin (θ1 x y r)
                    + (1² + (cos φ₂)² - 2 * 1 * cos φ₂) + (1² + (cos (θ1 x y r))²
                    - 2 * 1 * cos (θ1 x y r)) - 2 * (1 - cos φ₂) * (1 - cos (θ1 x y r))) with
               (((sin φ₂)² + (cos φ₂)²) + ((sin (θ1 x y r))² + (cos (θ1 x y r))²)
                - 2 * sin φ₂ * sin (θ1 x y r) + 1 - 2 * cos φ₂ + 1 
                - 2 * 1 * cos (θ1 x y r) - 2 * (1 - cos φ₂) * (1 - cos (θ1 x y r)))
             by (unfold Rsqr; lra).
           replace ((sin (φ₂ - θ1 x y r))² + (1² + (cos (φ₂ - θ1 x y r))²
                    - 2 * 1 * cos (φ₂ - θ1 x y r))) with
               (((sin (φ₂ - θ1 x y r))² + (cos (φ₂ - θ1 x y r))²) + 1 - 2 * cos (φ₂ - θ1 x y r))
             by (unfold Rsqr; lra).
           repeat rewrite sin2_cos2.
           rewrite cos_minus.
           lra.
       +++ assert (2 * r * (r * (1 - cos (φ₂ - θ1 x y r))) =
                   (r * sin (φ₂ - θ1 x y r))² + (r * (1 - cos (φ₂ - θ1 x y r)))²) as id. {
             repeat rewrite Rsqr_mult.
             rewrite Rsqr_minus.
             setr (r² * (((sin (φ₂ - θ1 x y r))² + (cos (φ₂ - θ1 x y r))²)
                         + 1 - 2 * cos (φ₂ - θ1 x y r))).
             rewrite sin2_cos2.
             unfold Rsqr.
             field. }

           
           assert (0 < 1 - cos φ₂) as omcp2gt0. {
             specialize (COS_bound φ₂) as [cbl [cbu |cbe]].
             lra.
             apply cosθeq1 in cbe ;try lra. }

           destruct ygt0 as [ygt0 | yeq0].
           2 : {
             exfalso.
             apply straightcond in oc.
             rewrite yeq0, <- zeq0 in *.
             autorewrite with null in *.
             lra. }
           
           assert (0 < φ₂ - θ1 x y r < 2 * PI) as ab. {
             destruct (total_order_T φ₂ PI) as [[plt|peq]|pgt].
             ++ exfalso.
               assert (0 < sin φ₂) as sp2gt0. {
                 apply sin_gt_0; try lra. }
               apply (Rmult_lt_compat_l r) in sp2gt0; try lra.
               autorewrite with null in sp2gt0.
               change (0 < wx) in sp2gt0.
               apply Rle_not_lt in ld.
               apply ld.
               rewrite <- zeq0.
               arn.
               zltab.
               
             ++ assert (2 * r < y) as ygt2r. {
                  apply (Rmult_lt_reg_r y); try lra.
                  setr (0² + y²).
                  rewrite zeq0.
                  apply straightcond in oc.
                  assumption. }
                assert (wx = 0) as wxeq0. {
                  unfold wx.
                  rewrite peq.
                  arn.
                  reflexivity. }
                assert (wy = 2 * r) as wyeq2r. {
                  unfold wy.
                  rewrite Rmult_comm.
                  apply Rmult_eq_compat_r; try lra.
                  rewrite peq.
                  arn.
                  lra. }
                rewrite wxeq0, wyeq2r in *.
                autorewrite with null in ld.
                

                split; try lra.

                specialize (root_ordering_Q1top x y r rgt0  ltac:(lra) ltac:(lra) oc)
                  as [[tml tmu] [[t1rl t1ru] t2r]].
                clear tmu t2r.
                apply (Rplus_lt_reg_r (θ1 x y r)).
                arn.
                setr φ₂.
                apply (Rlt_le_trans _ (calcθ₁ 0 0 0 x y)); try lra.
                rewrite thms; try lra.
                rewrite <- (chord_property r); try lra.
                apply Rmult_le_compat_l; try lra.

                rewrite peq, <- zeq0.
                arn.
                replace (r * (1 - -1)) with (2 * r) by lra.
                repeat rewrite atan2_PI2; lra.

             ++ destruct (total_order_T 0 (2 * r - y)) as [[lt|eq]|gt].
                +++ exfalso.
                    apply straightcond in oc.

                    rewrite <- zeq0 in oc.
                    autorewrite with null in *.
                    unfold Rsqr in oc.
                    apply (Rmult_lt_reg_r) in oc; lra.

                +++ exfalso.
                    apply straightcond in oc.

                    rewrite <- zeq0 in oc.
                    autorewrite with null in *.
                    unfold Rsqr in oc.
                    apply (Rmult_lt_reg_r) in oc; lra.

             +++ specialize (root_ordering_Q2top x y r rgt0 gt ltac:(lra) oc)
                 as [[tml tmu] [[t1rl t1ru] t2r]].
                 split; lra. }

           assert (r * (1 - cos (φ₂ - θ1 x y r)) > 0) as id2. {
             apply Rlt_gt.
             zltab.
             specialize (COS_bound (φ₂ - θ1 x y r)) as [cl [cu |ce]]; try lra.
             apply cosθeq1 in ce; lra. }

           assert (calcθ₁ 0 0 0 (r * sin (φ₂ - θ1 x y r)) (r * (1 - cos (φ₂ - θ1 x y r))) =
                   (φ₂ - θ1 x y r)) as id3. {
             unfold calcθ₁.
             arn.
             apply chord_property; lra. }
           rewrite <- id3 at 3.
           apply (underapprox_turning_std _ _ _ rgt0 id id2).


  + unfold L.
    apply condstraight in oc.

    apply (Rplus_le_reg_r (- r * θ1 x y r)).
    (* setl (sqrt (x² - (2 * r - y) * y)). *)
    setl (sqrt ((x - r * sin (θ1 x y r))² + (y - r * (1 - cos (θ1 x y r)))²)).
    setr (r * (φ₂  - θ1 x y r) + sqrt ((x - wx)² + (y - wy)²)).
    apply (Rle_trans _ (sqrt ((x - wx)² + (y - wy)²) +
                        sqrt ((wx - r * sin (θ1 x y r))² + (wy - r * (1 - cos (θ1 x y r)) )²))).
    ++ apply triangle.
    ++ apply (Rplus_le_reg_r (- sqrt ((x - wx)² + (y - wy)²))).
       setl (sqrt ((wx - r * sin (θ1 x y r))² + (wy - r * (1 - cos (θ1 x y r)))²)).
       setr (r * (φ₂ - θ1 x y r)).

       apply (Rle_trans _ (sqrt ((r * sin (φ₂ - θ1 x y r))² + (r * (1 - cos (φ₂ - θ1 x y r)))²))).
       +++ unfold wx, wy.
           apply sqrt_le_1_alt.
           repeat rewrite Rsqr_minus.
           setl (r² * ((sin φ₂)² + (sin (θ1 x y r))² - 2 * sin φ₂ * sin (θ1 x y r) +
                       (1 - cos φ₂)² + (1 - cos (θ1 x y r))² -
                                       2 * (1 - cos φ₂) * (1 - cos (θ1 x y r)))).
           setr (r² * ((sin (φ₂ - θ1 x y r))² + (1 - cos (φ₂ - θ1 x y r))²)).
           repeat rewrite Rsqr_minus.
           replace ((sin φ₂)² + (sin (θ1 x y r))² - 2 * sin φ₂ * sin (θ1 x y r)
                    + (1² + (cos φ₂)² - 2 * 1 * cos φ₂) + (1² + (cos (θ1 x y r))²
                    - 2 * 1 * cos (θ1 x y r)) - 2 * (1 - cos φ₂) * (1 - cos (θ1 x y r))) with
               (((sin φ₂)² + (cos φ₂)²) + ((sin (θ1 x y r))² + (cos (θ1 x y r))²)
                - 2 * sin φ₂ * sin (θ1 x y r) + 1 - 2 * cos φ₂ + 1 
                - 2 * 1 * cos (θ1 x y r) - 2 * (1 - cos φ₂) * (1 - cos (θ1 x y r)))
             by (unfold Rsqr; lra).
           replace ((sin (φ₂ - θ1 x y r))² + (1² + (cos (φ₂ - θ1 x y r))²
                    - 2 * 1 * cos (φ₂ - θ1 x y r))) with
               (((sin (φ₂ - θ1 x y r))² + (cos (φ₂ - θ1 x y r))²) + 1 - 2 * cos (φ₂ - θ1 x y r))
             by (unfold Rsqr; lra).
           repeat rewrite sin2_cos2.
           rewrite cos_minus.
           lra.
       +++ assert (2 * r * (r * (1 - cos (φ₂ - θ1 x y r))) =
                   (r * sin (φ₂ - θ1 x y r))² + (r * (1 - cos (φ₂ - θ1 x y r)))²) as id. {
             repeat rewrite Rsqr_mult.
             rewrite Rsqr_minus.
             setr (r² * (((sin (φ₂ - θ1 x y r))² + (cos (φ₂ - θ1 x y r))²)
                         + 1 - 2 * cos (φ₂ - θ1 x y r))).
             rewrite sin2_cos2.
             unfold Rsqr.
             field. }

           
           assert (0 < 1 - cos φ₂) as omcp2gt0. {
             specialize (COS_bound φ₂) as [cbl [cbu |cbe]].
             lra.
             apply cosθeq1 in cbe ;try lra. }

           destruct ygt0 as [ygt0 | yeq0].
           2 : {
             exfalso.
             rewrite yeq0 in *.
             assert (0 < wy) as wygt0. {
               unfold wy.
               zltab. }
             clear - wygt0 ld zgtx.
             autorewrite with null in ld.
             apply Rle_not_lt in ld.
             apply ld.
             setl (- (wy * (- x))).
             setr (- 0).
             apply Ropp_lt_contravar.
             zltab. }
           
           assert (0 < φ₂ - θ1 x y r < 2 * PI) as ab. {
             destruct (total_order_T φ₂ PI) as [[plt|peq]|pgt].
             ++ exfalso.
               assert (0 < sin φ₂) as sp2gt0. {
                 apply sin_gt_0; try lra. }
               apply (Rmult_lt_compat_l r) in sp2gt0.
               autorewrite with null in sp2gt0.
               change (0 < wx) in sp2gt0.
               apply Rle_not_lt in ld.
               apply ld.
               apply (Rlt_trans _ 0 ).
               setl (- (wy * (- x))).
               setr (- 0).
               apply Ropp_lt_contravar.
               zltab.
               unfold wy.
               zltab.
               zltab.
               assumption.
             ++ exfalso.
                assert (wx = 0) as wxeq0. {
                  unfold wx.
                  rewrite peq.
                  arn.
                  reflexivity. }
                assert (wy = 2 * r) as wyeq2r. {
                  unfold wy.
                  rewrite Rmult_comm.
                  apply Rmult_eq_compat_r; try lra.
                  rewrite peq.
                  arn.
                  lra. }
                rewrite wxeq0, wyeq2r in *.
                autorewrite with null in ld.
                clear - ld zgtx rgt0.
                apply Rle_not_lt in ld.
                apply ld.
                setl (- ((2 * r) * (- x))).
                setr (- 0).
                apply Ropp_lt_contravar.
                zltab.

             ++ destruct (total_order_T 0 (2 * r - y)) as [[lt|eq]|gt].
                +++ specialize (root_ordering_Q2bot _ _ _ rgt0 lt ygt0 zgtx oc)
                    as [[tml tmu] [[t1rl t1ru] t2r]].
                    split; try lra.

                    clear tmu t2r.
                    apply (Rplus_lt_reg_r (θ1 x y r)).
                    arn.
                    setr φ₂.
                    apply (Rlt_le_trans _ (calcθ₁ 0 0 0 x y)); try lra.
                    rewrite thms; try lra.
                    rewrite <- (chord_property r); try lra.
                    apply Rmult_le_compat_l; try lra.

                    assert (sin φ₂ < 0) as splt0. {
                      setl (- (- sin φ₂)).
                      setr (- 0).
                      apply Ropp_lt_contravar.
                      setl (- 0).
                      apply Ropp_lt_contravar.
                      apply sin_lt_0; lra. }

                    assert (r * sin φ₂ < 0) as rsplt0. {
                      setl (- (r * (- sin φ₂))).
                      setr (- 0).
                      apply Ropp_lt_contravar.
                      zltab. }

                    repeat rewrite atan2_atan_Q2; try lra; try zltab.
                    apply Rplus_le_compat_r.
                    
                    destruct ld as [ldlt |ldeq].
                    ++++ left.
                         apply atan_increasing.
                         change (y / x < wy / wx).
                         apply (Rmult_lt_reg_r ((- wx) * (- x))).
                         unfold wx.
                         zltab.
                         setl (wx * y); try lra.
                         setr (wy * x); try lra.
                         unfold wx.
                         apply Rmult_integral_contrapositive_currified; lra.
                   
                    ++++ change (atan (y / x) <= atan (wy / wx)).
                         right; f_equal.
                         apply (Rmult_eq_reg_r (x * wx)).
                         2 : {
                           apply Rmult_integral_contrapositive_currified ; try lra.
                           unfold wx.
                           zltab. }

                         setl (wx * y); try lra.
                         setr (wy * x); try lra.
                         unfold wx.
                         zltab.
                         
                +++ symmetry in eq.
                    specialize (root_ordering_Q2arm _ _ _ rgt0 eq zgtx oc)
                      as [[tml tmu] t1r].

                    specialize (theta1_rsgn_bnd _ _ r ltac:(lra) oc) as [ls rs].
                    specialize (ls rgt0).

                    split; try lra.
                    clear tmu t1r.
                    apply (Rplus_lt_reg_r (θ1 x y r)).
                    arn.
                    setr φ₂.
                    apply (Rlt_le_trans _ (calcθ₁ 0 0 0 x y)); try lra.
                    rewrite thms; try lra.
                    rewrite <- (chord_property r); try lra.
                    apply Rmult_le_compat_l; try lra.

                    assert (sin φ₂ < 0) as splt0. {
                      setl (- (- sin φ₂)).
                      setr (- 0).
                      apply Ropp_lt_contravar.
                      setl (- 0).
                      apply Ropp_lt_contravar.
                      apply sin_lt_0; lra. }

                    assert (r * sin φ₂ < 0) as rsplt0. {
                      setl (- (r * (- sin φ₂))).
                      setr (- 0).
                      apply Ropp_lt_contravar.
                      zltab. }

                    repeat rewrite atan2_atan_Q2; try lra; try zltab.
                    apply Rplus_le_compat_r.
                    
                    destruct ld as [ldlt |ldeq].
                    ++++ left.
                         apply atan_increasing.
                         change (y / x < wy / wx).
                         apply (Rmult_lt_reg_r ((- wx) * (- x))).
                         unfold wx.
                         zltab.
                         setl (wx * y); try lra.
                         setr (wy * x); try lra.
                         unfold wx.
                         apply Rmult_integral_contrapositive_currified; lra.
                   
                    ++++ change (atan (y / x) <= atan (wy / wx)).
                         right; f_equal.
                         apply (Rmult_eq_reg_r (x * wx)).
                         2 : {
                           apply Rmult_integral_contrapositive_currified ; try lra.
                           unfold wx.
                           zltab. }

                         setl (wx * y); try lra.
                         setr (wy * x); try lra.
                         unfold wx.
                         zltab.

             +++ specialize (root_ordering_Q2top x y r rgt0 gt ltac:(lra) oc)
                 as [[tml tmu] [[t1rl t1ru] t2r]].
                 split; lra. }

           assert (r * (1 - cos (φ₂ - θ1 x y r)) > 0) as id2. {
             apply Rlt_gt.
             zltab.
             specialize (COS_bound (φ₂ - θ1 x y r)) as [cl [cu |ce]]; try lra.
             apply cosθeq1 in ce; lra. }

           assert (calcθ₁ 0 0 0 (r * sin (φ₂ - θ1 x y r)) (r * (1 - cos (φ₂ - θ1 x y r))) =
                   (φ₂ - θ1 x y r)) as id3. {
             unfold calcθ₁.
             arn.
             apply chord_property; lra. }
           rewrite <- id3 at 3.
           apply (underapprox_turning_std _ _ _ rgt0 id id2).
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
         (zltb2 : 0 <= b2)
         (zlth' : 0 <= h' < h),
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
  destruct zlth' as [[zlth' |zeqh'] h'lth].
  left; apply posss; lra.
  zltab.

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
         (zltb2 : 0 <= b2)
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
    + destruct zltb2 as [zltb2 | zeqb2].
      set (h' :=  h * b2' * / b2).
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

      lra.

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
    left.
    
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
    left.
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



(* The library can be applied to tighten the approximation of path
length/collision timing so that it tiles the cartesian plane using
this lemma. *)

(*
  outer triangle   y = m * x
                   x = k
  inner triangle   y = m1 * x
                   y = n1 * (x - k) or x = k
*)

Lemma shorter_two_step_linear_path_right :
  forall m m1 n1 k
         (ziso : 0 < m1 < m) (* origin intercept slopes *)
         (kiso : n1 < 0) (* k x-intercept slope order *)
         (kpos : 0 < k),
    let Px :=  k in
    let Py :=  m * Px in
    let Qx :=  k * n1 / (n1 - m1) in
    let Qy :=  m1 * Qx in
    sqrt (Qx² + Qy²) + sqrt ((Qx - k)² + Qy²) <
    sqrt (Px² + Py²) + sqrt ((Px - k)² + Py²).
Proof.
  intros.
  
  assert (0 < Px) as pxgt0. {
    unfold Px, Py. lra. }
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
    lra.

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
    setl 0; try lra.
    replace (k * n1 / (n1 - m1) - k) with (k * (m1 / (n1-m1))).
    setr (m * k * (k * (m1 / (- n1 + m1)))); try lra.
    apply (Rmult_lt_reg_r (/ (m1 * (k * / (- n1 + m1)) * k))).
    zltab; try lra.
    setl 0; try lra.
    setr m; lra.

    field_simplify; lra.
Qed.

  
  
Lemma spreading_circle_matches_fixed_orientation_rt:
  forall θ r s t
         (zlts : 0 < s)
         (zlts : 0 < θ)
         (tm : s * t = r * θ),
    let x := r * sin(θ) in
    let y := r * (1-cos(θ)) in
    let v := s * sqrt(2 * (1 - cos(θ))) / θ in
    x² + y² = (v * t)².
Proof.
  intros.
  unfold x, y, v.
  assert (t = r * θ / s) as tdef. {
    apply (Rmult_eq_reg_r s); try lra.
    lrag tm. }
  rewrite tdef.
  repeat rewrite <- RmultRinv.
  repeat rewrite Rsqr_mult.
  rewrite Rsqr_minus.
  setl (r² * (((sin θ)² + (cos θ)²) + 1 - 2 * cos θ)).
  rewrite sin2_cos2.
  rewrite Rsqr_inv; try lra.
  rewrite Rsqr_sqrt.
  setr (r² * (1 + 1 - 2 * cos θ)); lra.
  zltab; specialize (COS_bound θ) as [lb ub]; lra.
Qed.

(*
chord length = 2 * r * sin (θ / 2) = sqrt (x² + y²)
circumference length = r * θ

θ is constant

sqrt (x² + y²) * K = r * θ
express K in terms of only theta
sqrt (x² + y²) * r * θ / (2 * r * sin (θ / 2)) = r * θ
sqrt (x² + y²) * θ / (2 * sin (θ / 2)) = r * θ
*)

(* don't know if we need this *)
(*
Lemma is_lim_form0 : is_lim  (fun x => cos x / x - sin x / x²) 0 0.
Proof.
  unfold is_lim, filterlim, filter_le, Rbar_locally, locally,
  filtermap, Rbar_locally', locally', within, locally.
  simpl.
  intros P [e yball].
  Check is_lim_sinc_0.
Admitted.
 *)

Lemma spreading_circle_matches_fixed_orientation_xy:
  forall x y (zley : 0 < y),
    let r := (x² + y²)/(2*y) in
    let θ := 2 * atan2 y x in
    sqrt (x² + y²) * θ / (2 * sin (θ / 2)) = r * θ.
Proof.
  intros.

  assert (0 < θ < 2 * PI) as trng. {
    unfold θ.
    assert (0 < atan2 y x < PI) as at2r. {
      destruct (total_order_T x 0) as [[lt|eq]|gt].
      apply (atan2Q2 _ y) in lt; try assumption.
      split; try lra.
      subst.
      specialize (atan2_PI2 _ zley) as p; try assumption.
      rewrite p.
      specialize PI_RGT_0 as pigt0.
      split; try lra.
      apply (atan2Q1 _ y) in gt; try assumption.
      split; try lra. }
    split; try lra. }

  assert (~ (x = 0 /\ y = 0)) as no. {
    intros [xeq0 yeq0].
    rewrite yeq0 in zley.
    lra. }

  assert (0 < x² + y²) as x2y2gt0. {
    apply posss; assumption. }

  assert (r * (2 * sin (θ / 2)) = sqrt (x² + y²)) as id. {
    unfold θ.
    replace (2 * atan2 y x / 2) with (atan2 y x) by lra.
    rewrite atan2_sin_id; try assumption.
    repeat rewrite <- Rsqr_pow2.
    unfold r.
    rewrite <- (Rsqr_sqrt (x² + y²)) at 1; try lra.
    setl (sqrt (x² + y²)).
    apply sqrt_lt_R0 in x2y2gt0.
    unfold Rsqr in x2y2gt0.
    split; try lra.
    reflexivity. }

  rewrite <- id.
  setl (r * θ).
  intro sint2eq0.

  assert (0 < θ / 2 < PI) as t2r. {
    split; try lra. }

  apply sin_eq_O_2PI_0 in sint2eq0; lra.
  reflexivity.
Qed.

Definition sinc x := sin x / x.


Lemma is_deriv_sinc : forall x, x<>0 ->
    is_derive sinc x (cos x / x - sin x / x²).
Proof.
  intros.
  simpl in *.
  unfold sinc.
  auto_derive; try assumption.
  unfold Rsqr; field; assumption.
Qed.

Lemma sinc_deriv_lt0 : forall x,
    0 < x < PI ->
    cos x / x - sin x / x² < 0.
Proof.
  intros.
  specialize PI_RGT_0 as pigt0.
  apply (Rmult_lt_reg_r (x²)); try (unfold Rsqr; zltab).
  setr 0.
  setl (x * cos x - sin x); try lra.
  apply (Rplus_lt_reg_r (sin x)).
  setl (x * cos x).
  arn.

  destruct (Req_dec x (PI/2)) as [pi2 |npi2].
  + rewrite pi2.
    arn.
    lra.
  + assert (cos x <> 0) as cxne0. {
    intro cxeq0.
    apply cos_eq_0_2PI_0 in cxeq0; lra. }

    specialize (is_derive_tan _ cxne0) as dtan.
    rewrite <- Rsqr_pow2 in dtan.

    set (f := (fun x => tan x - x)).

    assert (is_derive f x (tan x)²) as df. {
      unfold f.
      auto_derive.
      change (ex_derive tan x).
      unfold ex_derive.
      exists (((tan x)² + 1)).
      assumption.
      apply is_derive_unique in dtan.
      change (1 * Derive tan x + - (1) = (tan x)²).
      rewrite dtan.
      field. }

    assert (0 < (tan x)²) as t2gt0. {
      specialize (Rle_0_sqr (tan x)) as zletx2.
      destruct zletx2 as [lt | eq]; try assumption.
      exfalso.
      symmetry in eq.
      apply Rsqr_eq_0 in eq.
      unfold tan in eq.
      rewrite <- RmultRinv in eq.
      apply Rmult_integral in eq.
      destruct eq as [s0 |c0].
      apply sin_eq_O_2PI_0 in s0; lra.
      generalize c0.
      change (/ cos x <> 0).
      apply Rinv_neq_0_compat.
      assumption. }

    destruct (total_order_T x (PI/2)) as [[lt|eq]|gt]; try lra.
    ++ assert (0 < cos x) as zltc. {
         apply cos_gt_0; try lra. }
       apply (Rmult_lt_reg_r (/ cos x)).
       apply Rinv_0_lt_compat.
       assumption.
       setl x; try lra.
       rewrite RmultRinv.
       change (x < tan x).
       apply (Rplus_lt_reg_r (- x)).
       setl 0.
       setr (tan x - x).
       change (0 < f x).
       
       
       (*  apply incr_function? *)
       admit.
    ++ apply (Rmult_lt_reg_r (/ - (cos x))).
       apply Rinv_0_lt_compat.
       setl (- 0).
       apply Ropp_lt_contravar.
       apply cos_lt_0; lra.
       setl (- x); try lra.
       rewrite <- Ropp_inv_permute; try assumption.
       apply (Rplus_lt_reg_r (tan x + x)).
       setl (tan x).
       replace (sin x * - / cos x + (tan x + x)) with x by
           (unfold tan; field; assumption).
       apply (Rlt_trans _ 0); try lra.
       rewrite <- (tan_period _ (-1)%Z); try lra.
       apply tan_lt_0; lra.
Admitted.
  
(*
Lemma spreading_circle_matches_fixed_orientation2:
  forall r1 r2 θ1 θ2 θ r s t
         (zlts : 0 < s)
         (zltt : 0 < θ1)
         (tbnd : θ1 <= θ <= θ2)
         (t2ltpi2 : θ2 < PI / 2)
         (zler1 : 0 < r1)
         (rbnd : r1 <= r <= r2)
         (tm : s * t = r * θ),
    let x := r * sin(θ) in
    let y := r * (1-cos(θ)) in
    let v1 := s * sqrt(2 * (1 - cos(θ1))) / θ1 in
    let v2 := s * sqrt(2 * (1 - cos(θ2))) / θ2 in
    (v2 * t)² <= x² + y² <= (v1 * t)².
Proof.
  intros.
  unfold v1, v2.
  clear v1 v2.

  unfold x, y.
  rewrite (spreading_circle_matches_fixed_orientation_rt _ _ s t); try lra.

  repeat rewrite <- RmultRinv.
  repeat rewrite Rsqr_mult.
  rewrite Rsqr_sqrt; [|  zltab; specialize (COS_bound θ2) as [lb ub]; lra].
  rewrite Rsqr_sqrt; [|  zltab; specialize (COS_bound θ) as [lb ub]; lra].
  rewrite Rsqr_sqrt; [|  zltab; specialize (COS_bound θ1) as [lb ub]; lra].
  assert (forall θ, (1 - cos θ) = 2 * (sin (θ/2))²) as id. {
    intros.
    apply (Rmult_eq_reg_r (/ 2)).
    rewrite RmultRinv.
    rewrite <- sint22.
    field.
    intro; lra. }
  repeat rewrite id.

  assert (t = r * θ / s) as tdef. {
    apply (Rmult_eq_reg_r s); try lra.
    lrag tm. }
  assert (0 < t) as zltt0. {
    rewrite tdef, <- RmultRinv.
    zltab. }
  
  split.
  + apply (Rmult_le_reg_r ((/ s²) * (/ t²))); [ unfold Rsqr; zltab |].
    setl ((sin (θ2 / 2)/ (θ2 / 2))²); try lra.
    setr ((sin (θ / 2)/ (θ / 2))²); try lra.
    change ((sinc (θ2 / 2))² <= (sinc (θ / 2))²).
    destruct tbnd as [ls [rs| rse]].
    ++ left. (* derive_decreasing_interv *)
       admit.
    ++ subst; right; reflexivity.
  + apply (Rmult_le_reg_r ((/ s²) * (/ t²))); [ unfold Rsqr; zltab |].
    setr ( (sin (θ1 / 2)/ (θ1 / 2))²); try lra.
    setl ((sin (θ / 2)/ (θ / 2))²); try lra.
    change ((sinc (θ / 2))² <= (sinc (θ1 / 2))²).
    destruct tbnd as [[lsl |lse] rs].
    ++ left.
       (* apply Rsqr_incrst_1
          eapply incr_function; try lra; *)
       admit.
    ++ subst; right; reflexivity.
Admitted.
*)


Lemma circular_waves_approximate_turn :
  forall x y r1 r2 θ1 θ2 (zley : 0 < y),
    let r := (x² + y²)/(2*y) in
    let θ := 2 * atan2 y x in
    forall (r1gt0 : 0 < r1)
           (rbnd : r1 <= r <= r2)
           (tlb : 0 < θ1)
           (tub : θ2 < 2 * PI)
           (tbnd : θ1 <= θ <= θ2),
      sqrt (x² + y²) * θ1 / (2 * sin (θ1 / 2)) <=
      r * θ <= sqrt (x² + y²) * θ2 / (2 * sin (θ2 / 2)).
Proof.
  intros.
  unfold r, θ.

  assert (~ (x = 0 /\ y = 0)) as no. {
    intros [xeq0 yeq0].
    rewrite yeq0 in zley.
    lra. }

  assert (0 < x² + y²) as x2y2gt0. {
    apply posss; assumption. }
  
  rewrite <- (spreading_circle_matches_fixed_orientation_xy x y zley).
  change (sqrt (x² + y²) * θ1 / (2 * sin (θ1 / 2)) <=
          sqrt (x² + y²) * θ / (2 * sin (θ / 2)) <=
          sqrt (x² + y²) * θ2 / (2 * sin (θ2 / 2))).

  assert (0 < sin (θ / 2)) as zltst. {
    apply sin_gt_0; lra. }
  assert (0 < sin (θ1 / 2)) as zltst1. {
    apply sin_gt_0; lra. }
  assert (0 < sin (θ2 / 2)) as zltst2. {
    apply sin_gt_0; lra. }

  apply sqrt_lt_R0 in x2y2gt0.

  assert (0 < θ / 2 < PI) as t2r. {
    split; try lra. }
  assert (0 < θ1 / 2 < PI) as t12r. {
    split; try lra. }
  assert (0 < θ2 / 2 < PI) as t22r. {
    split; try lra. }

  split.
  + apply (Rmult_le_reg_r (/ sqrt (x² + y²) * sinc (θ1 / 2) * sinc (θ / 2))).
    unfold sinc.
    zltab.
    replace (sqrt (x² + y²) * θ1 / (2 * sin (θ1 / 2)) *
             (/ sqrt (x² + y²) * sinc (θ1 / 2) * sinc (θ / 2)))
      with (sinc (θ/2)) by (unfold sinc; field; lra).
    replace (sqrt (x² + y²) * θ / (2 * sin (θ / 2)) *
             (/ sqrt (x² + y²) * sinc (θ1 / 2) * sinc (θ / 2)))
      with (sinc (θ1/2)) by (unfold sinc; field; lra).

    destruct tbnd as [[tl |teq] tu].
    left.
    apply Ropp_lt_cancel.
    change ((fun k => opp (sinc k)) (θ1 / 2) <
            (fun k => opp (sinc k)) (θ / 2)).
    apply (incr_function _ 0 PI (fun x => opp (cos x / x - sin x / x²)));
      try (simpl; intros; lra).
    simpl; intros.
    apply (is_derive_opp sinc).
    apply is_deriv_sinc; lra.
    simpl; intros; unfold opp; simpl.
    setr (- 0).
    apply Ropp_lt_gt_contravar.
    apply sinc_deriv_lt0; try lra.

    right.
    subst.
    reflexivity.

  + apply (Rmult_le_reg_r (/ sqrt (x² + y²) * sinc (θ2 / 2) * sinc (θ / 2))).
    unfold sinc.
    zltab.
    replace (sqrt (x² + y²) * θ2 / (2 * sin (θ2 / 2)) *
             (/ sqrt (x² + y²) * sinc (θ2 / 2) * sinc (θ / 2)))
      with (sinc (θ/2)) by (unfold sinc; field; lra).
    replace (sqrt (x² + y²) * θ / (2 * sin (θ / 2)) *
             (/ sqrt (x² + y²) * sinc (θ2 / 2) * sinc (θ / 2)))
      with (sinc (θ2/2)) by (unfold sinc; field; lra).

    destruct tbnd as [tl [tu |teq]].
    left.
    apply Ropp_lt_cancel.
    change ((fun k => opp (sinc k)) (θ / 2) <
            (fun k => opp (sinc k)) (θ2 / 2)).
    apply (incr_function _ 0 PI (fun x => opp (cos x / x - sin x / x²)));
      try (simpl; intros; lra).
    simpl; intros.
    apply (is_derive_opp sinc).
    apply is_deriv_sinc; lra.
    simpl; intros; unfold opp; simpl.
    setr (- 0).
    apply Ropp_lt_gt_contravar.
    apply sinc_deriv_lt0; try lra.

    right.
    subst.
    reflexivity.
Qed.



    
      lra.
is_derive_opp
     : forall (f : ?K -> ?V) (x1 : ?K) (l : ?V),
       is_derive f x1 l -> is_derive (fun x2 : ?K => opp (f x2)) x1 (opp l)
    Check is_deriv_sinc.
    
    evar (1).
    Check is_derive_opp.
    ; apply is_deriv_sinc; lra.
    specialize is_deriv_sinc.
    Search is_derive.
    simpl; intros.
    forall x0 : R, x0 <> 0 -> is_derive sinc x0 (cos x0 / x0 - sin x0 / x0²))
    specialize is_deriv_sinc.
    specialize sinc_deriv_lt0.

    admit.
    
  apply sin_eq_O_2PI_0 in sint2eq0; lra.
  reflexivity.

  
  assert (forall θ, (1 - cos θ) = 2 * (sin (θ/2))²) as id. {
    intros.
    apply (Rmult_eq_reg_r (/ 2)).
    rewrite RmultRinv.
    rewrite <- sint22.
    field.
    intro; lra. }
  repeat rewrite id.
  replace (2 * (2 * (sin (θ1 / 2))²)) with ((2 * sin (θ1 / 2))²);
    [|unfold Rsqr; field].
  replace (2 * (2 * (sin (θ2 / 2))²)) with ((2 * sin (θ2 / 2))²);
    [|unfold Rsqr; field].
  repeat rewrite sqrt_Rsqr.
  split.
  admit.

  unfold θ.
  replace (2 * atan2 y x / 2) with (atan2 y x) by lra.
  SearchPattern (sqrt (_)² = _).
  admit.
  

  Check sint22.

Search tan.
derive_pt_tan
