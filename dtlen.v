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

(* Standard form of Theorem 5 (Maximum bearing-constrained
     path length) *)
Theorem maxlength_path_std :
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
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx rb 0 0 θv tvp) (Hy rb 0 0 θv tvp) o p
           /\ Du <= Dv)) \/
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θd twp) (Hy rw 0 0 θd twp) o p /\
           Du <= Dw)) \/
      (exists Dw rw twp,
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
          ~ straight rb 0 0 0 x y) as [stt | nstt]. {
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
          left.
          exists Du, (θ1 x y ru), tup'.
          repeat (split; auto);
          right; reflexivity. }

    (* ru < rb (reminder: θd and (θ1 x y rb) are not related) *)
    destruct (Rle_dec (θ1 x y rb) θd) as [t1rbletd| t1rbgttd].
    ++ left.
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
                    _ _ _ _ Du Db nc2 phaseu stt zltru tup' rult rtp u v).
           
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
           left.
           exists Dd, rd, trd.
           split; try lra.
           split; try assumption.
           left.
           eapply ottb_bigger_r_longer_path_std.
           apply nc2.
           apply phaseu.
           apply srd.
           assumption.
           assumption.
           assumption.
           dependent rewrite tc1 in d.
           assumption.
           
           Unshelve.
           assumption.
           assumption.
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
           left.
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
    specialize (intro_turning_path_std _ _ _ phasez yne0) as [rtp pt].
    change (0 < rz * θmax < Rabs rz * 2 * PI) in rtp.
    change (path_segment {| nonneg := rz * θmax; cond_nonneg := nna rz θmax rtp |}
                         (Hx rz 0 0 θmax rtp) (Hy rz 0 0 θmax rtp)
                         o p) in pt.
    set (Dz := {| nonneg := rz * θmax; cond_nonneg := nna rz θmax rtp |}) in *.

    destruct (Rle_dec θmax θd) as [tmletd | tmgttd].
    ++ right.
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
             rewrite (Darm_Q _ _ _ rstr r0ne0).
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
           rewrite Darm_Q; try (lra||assumption).
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
       left.
       
       (*****)
       
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

                  exists Du, ru, rdp'.
                  split; try lra. }
                

                
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
                exists Dd, rd, trd.
                split; try lra.
                split; try assumption.
                left.
                eapply ottb_bigger_r_longer_path_std.
                apply nc2.
                apply phaseu.
                apply srd.
                assumption.
                assumption.
                assumption.
                dependent rewrite tc1 in d.
                assumption.
                
                Unshelve.
                assumption.
                assumption.
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
           exists Du, ru, tup''.
           split; try lra.
           split; try assumption.
           right; reflexivity.
Qed.



Corollary maxlength_path_std_part1 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0))
           (t1rbletd : θ1 x y rb <= θd)
           (stt: straight rb 0 0 0 x y),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx rb 0 0 θv tvp) (Hy rb 0 0 θv tvp) o p
           /\ Du <= Dv)).
Proof.
  intros until 8.
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
    change ((0 < θmax /\ (θmax / 2 < θ1 x y rb < θmax \/
                          -2 * PI < θ1 x y rb < θmax / 2 - 2 * PI)) \/
            (θmax < 0 /\ (θmax < θ1 x y rb < θmax / 2 \/
                          θmax / 2 + 2 * PI < θ1 x y rb < 2 * PI))) in t1vrng.

    destruct rur as [rulb [rult |rueq]].
    2 : { rewrite <- rueq in *;
          exists Du, (θ1 x y ru), tup';
          repeat (split; auto);
          right; reflexivity. }

    (* ru < rb (reminder: θd and (θ1 x y rb) are not related) *)
    ++ exists Db, (θ1 x y rb), rtp.
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
                    _ _ _ _ Du Db nc2 phaseu stt zltru tup' rult rtp u v).
           
Qed.


Corollary maxlength_path_std_part2 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru < rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0))
           (t1rbgttd : θ1 x y rb > θd)
           (stt: straight rb 0 0 0 x y),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θd twp) (Hy rw 0 0 θd twp) o p /\
           Du <= Dw)).
Proof.
  intros until 8.
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

    destruct rur as [rulb rult].

    (* ru < rb (reminder: θd and (θ1 x y rb) are not related) *)
    ++ change (θd < θb) in t1rbgttd.

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
           exists Dd, rd, trd.
           split; try lra.
           split; try assumption.
           left.
           eapply ottb_bigger_r_longer_path_std.
           apply nc2.
           apply phaseu.
           apply srd.
           assumption.
           assumption.
           assumption.
           dependent rewrite tc1 in d.
           assumption.
           
           Unshelve.
           assumption.
           assumption.
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
           exists Du, ru, tup''.
           split; try lra.
           split; try assumption.
           right; reflexivity.
Qed.

Corollary maxlength_path_std_part3 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rulb : ra <= ru)
         (rueq : ru = rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0))
           (t1rbgttd : θ1 x y rb > θd)
           (stt: straight rb 0 0 0 x y),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx rb 0 0 θv tvp) (Hy rb 0 0 θv tvp) o p
           /\ Du <= Dv)).
Proof.
  intros until 9.
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

    rewrite <- rueq in *;
      exists Du, (θ1 x y ru), tup';
      repeat (split; auto);
      right; reflexivity.
Qed.


Corollary maxlength_path_std_part4 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0))
           (tmletd : θmax <= θd)
           (rbt: turning rb 0 0 0 x y),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θmax twp) (Hy rw 0 0 θmax twp) o p /\
           Du <= Dw)).
Proof.
  intros until 7.
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

  + assert (~ straight rb 0 0 0 x y) as nstt. {
      intros stt.
      apply straightcond in stt.
      apply turningcond in rbt.
      rewrite <- rbt in stt.
      lra. }
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
    specialize (intro_turning_path_std _ _ _ phasez yne0) as [rtp pt].
    change (0 < rz * θmax < Rabs rz * 2 * PI) in rtp.
    change (path_segment {| nonneg := rz * θmax; cond_nonneg := nna rz θmax rtp |}
                         (Hx rz 0 0 θmax rtp) (Hy rz 0 0 θmax rtp)
                         o p) in pt.
    set (Dz := {| nonneg := rz * θmax; cond_nonneg := nna rz θmax rtp |}) in *.

    (* destruct (Rle_dec θmax θd) as [tmletd | tmgttd]. *)
    ++ exists Dz, rz, rtp.
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
             rewrite (Darm_Q _ _ _ rstr r0ne0).
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
           rewrite Darm_Q; try (lra||assumption).
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
Qed.


Corollary maxlength_path_std_part5 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0))
           (tmgttd : θd < θmax)
           (rbt: turning rb 0 0 0 x y),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θd twp) (Hy rw 0 0 θd twp) o p /\
           Du <= Dw)).
Proof.
  intros until 7.
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

  (* right. *)
  assert (~ straight rb 0 0 0 x y) as nstt. {
    intro srb.
    apply straightcond in srb.
    apply turningcond in rbt.
    lra. }
  
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
  specialize (intro_turning_path_std _ _ _ phasez yne0) as [rtp pt].
  change (0 < rz * θmax < Rabs rz * 2 * PI) in rtp.
  change (path_segment {| nonneg := rz * θmax; cond_nonneg := nna rz θmax rtp |}
                       (Hx rz 0 0 θmax rtp) (Hy rz 0 0 θmax rtp)
                       o p) in pt.
  set (Dz := {| nonneg := rz * θmax; cond_nonneg := nna rz θmax rtp |}) in *.
  + (*apply Rnot_le_lt in tmgttd. *)
    (* left. *)
    
    (*****)
    
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
       ++ destruct t1urng as [[tordu [upr| unr]]|[tord poof]]; try lra.
           
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
           +++ exfalso.
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
           +++ apply Rnot_lt_le in regtrd.
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

                  exists Du, ru, rdp'.
                  split; try lra. }
                

                
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
                exists Dd, rd, trd.
                split; try lra.
                split; try assumption.
                left.
                eapply ottb_bigger_r_longer_path_std.
                apply nc2.
                apply phaseu.
                apply srd.
                assumption.
                assumption.
                assumption.
                dependent rewrite tc1 in d.
                assumption.
                
                Unshelve.
                assumption.
                assumption.
       ++ assert (0 < ru * θd < Rabs ru * 2 * PI) as tup''. {
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
           exists Du, ru, tup''.
           split; try lra.
           split; try assumption.
           right; reflexivity.
Qed.

(* Third term does not exist because minimum theta value would be thetamax/2, 
disallowed because it would require r=0, ra is the minimum r and 0 < ra *)

Theorem minlength_path_std :
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
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx ra 0 0 θv tvp) (Hy ra 0 0 θv tvp) o p
           /\  Dv <= Du)) \/
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θc twp) (Hy rw 0 0 θc twp) o p /\
           Dw <= Du)).
Proof.
  intros until 6.
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

  (* working here *)
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
           exists Dc, rc, trd.
           split; [lra|].
           split; try assumption.
           left.
           eapply ottb_bigger_r_longer_path_std.
           apply nc2.
           apply srd.
           apply phaseu.
           lra.
           assumption.
           dependent rewrite tc1 in d.
           assumption.
           assumption.
           
           Unshelve.
           assumption.
           assumption.
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
           exists Du, ru, tup''.
           split; try lra.
           split; try assumption.
           right; reflexivity.

    ++ left.
       apply Rnot_lt_le in t1rbgttd.
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
                    _ _ _ _ Da Du nc2 stt phaseu lt rtp ralt tup' v u).
           
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


Corollary minlength_path_std_part4 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0))
           (nstt: ~ straight ra 0 0 0 x y),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      False.
Proof.
  intros until 7.
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

  (* assert (~ straight ra 0 0 0 x y) as nstt. { *)
  (*   intro srb. *)
  (*   apply straightcond in srb. *)
  (*   apply turningcond in rat. *)
  (*   lra. } *)

  + destruct rur as [[rult |rueq] ruub ].
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


Corollary minlength_path_std_part1 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra < ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0))
           (t1rbletd : (θ1 x y ra) < θc),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw 0 0 θc twp) (Hy rw 0 0 θc twp) o p /\
           Dw <= Du)).
Proof.
  intros until 7.
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
  2 : {
    exfalso.
    assert (ra <= ru <= rb) as rbnd; try lra.
    eapply minlength_path_std_part4.
    apply zltrb.
    apply rbnd.
    apply tur.
    apply phaseu.
    apply nc.
    assumption.
    apply u. }

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

    destruct rur as [ralt ruub].

    (* ra < ru (reminder: θc and (θ1 x y ra) are not related) *)
    (* destruct (Rlt_dec (θ1 x y ra) θc) as [t1rbletd| t1rbgttd]. *)
    ++ (* right. *)
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
           exists Dc, rc, trd.
           split; [lra|].
           split; try assumption.
           left.
           eapply ottb_bigger_r_longer_path_std.
           apply nc2.
           apply srd.
           apply phaseu.
           lra.
           assumption.
           dependent rewrite tc1 in d.
           assumption.
           assumption.
           
           Unshelve.
           assumption.
           assumption.
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
           exists Du, ru, tup''.
           split; try lra.
           split; try assumption.
           right; reflexivity.
Qed.

Corollary minlength_path_std_part2 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (raeq : ra = ru)
         (ruub : ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0))
           (t1rbletd : (θ1 x y ra) < θc),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx ra 0 0 θv tvp) (Hy ra 0 0 θv tvp) o p
           /\  Dv <= Du)).
Proof.
  intros until 8.
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
  2 : {
    exfalso.
    assert (ra <= ru <= rb) as rbnd; try lra.
    eapply minlength_path_std_part4.
    apply zltrb.
    apply rbnd.
    apply tur.
    apply phaseu.
    apply nc.
    assumption.
    apply u. }
  
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

    rewrite raeq in *.
    exists Du, (θ1 x y ru), tup'.
    repeat (split; auto).
    right; reflexivity.
Qed.


Corollary minlength_path_std_part3 :
  forall x y ra rb θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru 0 0 0 x y),
    let o := (mkpt 0 0) in
    let p := (mkpt x y) in
    let θmax := calcθ₁ 0 0 0 x y in
    forall (nc : ~ (0 <= x /\ y = 0))
           (t1rbgttd : θc <= θ1 x y ra),
      path_segment Du (Hx ru 0 0 θu tup) (Hy ru 0 0 θu tup) o p ->
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx ra 0 0 θv tvp) (Hy ra 0 0 θv tvp) o p
           /\  Dv <= Du)).
Proof.
  intros until 7.
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
  2 : {
    exfalso.
    assert (ra <= ru <= rb) as rbnd; try lra.
    eapply minlength_path_std_part4.
    apply zltrb.
    apply rbnd.
    apply tur.
    apply phaseu.
    apply nc.
    assumption.
    apply u. }
  
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
          exists Du, (θ1 x y ru), tup'.
          repeat (split; auto).
          right; reflexivity. }

    (* ra < ru (reminder: θc and (θ1 x y ra) are not related) *)
    (* destruct (Rlt_dec (θ1 x y ra) θc) as [t1rbletd| t1rbgttd2]. *)
    (* ++ exfalso. unfold θa in t1rbgttd. lra. *)

    ++ exists Da, (θ1 x y ra), rtp.
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
                    _ _ _ _ Da Du nc2 stt phaseu lt rtp ralt tup' v u).
Qed.



(* end hide *)


(** General version of Theorem 5 (Maximum bearing-constrained path 
    length) of the paper. *)
Theorem maxlength_path :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru θ₀ x₀ y₀ x₁ y₁),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nc : θmax <> 0),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx rb θ₀ x₀ θv tvp) (Hy rb θ₀ y₀ θv tvp) o p
           /\ Du <= Dv)) \/
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw θ₀ x₀ θd twp) (Hy rw θ₀ y₀ θd twp) o p /\
           Du <= Dw)) \/
      (exists Dw rw twp,
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
  apply straight_rot in phaseu.
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
    apply straightcond in phaseu.
    rewrite <- zeqx, yeq0 in phaseu.
    autorewrite with null in phaseu.
    lra. }

  specialize (maxlength_path_std
           _ _ _ _ _ _ Du ru θu tup lt rur tur phaseu npx u)
    as [[Dv [pv [tvp v]]] |[[Dv [pv [tvp v]]] |[Dv [pv [tvp v]]]]].
  left.
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
  right; left.
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
  right; right.
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.

Corollary maxlength_path_part1 :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru θ₀ x₀ y₀ x₁ y₁),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nO : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (nc : θmax <> 0)
           (t1rbletd : θ1 x y rb <= θd)
           (stt: straight rb θ₀ x₀ y₀ x₁ y₁),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx rb θ₀ x₀ θv tvp) (Hy rb θ₀ y₀ θv tvp) o p
           /\ Du <= Dv)).
Proof.
  intros until 8.
  intro u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  apply straight_rot in phaseu.
  apply straight_rot in stt.
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
    apply straightcond in phaseu.
    rewrite <- zeqx, yeq0 in phaseu.
    autorewrite with null in phaseu.
    lra. }

  unfold o, p.
  specialize (maxlength_path_std_part1
                _ _ _ _ _ _ Du ru θu tup lt rur tur phaseu npx t1rbletd stt u)
    as [Dv [pv [tvp v]]].
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.


Corollary maxlength_path_part2 :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru < rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru θ₀ x₀ y₀ x₁ y₁),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nO : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (nc : θmax <> 0)
           (t1rbletd : θ1 x y rb > θd)
           (stt: straight rb θ₀ x₀ y₀ x₁ y₁),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw θ₀ x₀ θd twp) (Hy rw θ₀ y₀ θd twp) o p /\
           Du <= Dw)).
Proof.
  intros until 8.
  intros u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  apply straight_rot in phaseu.
  apply straight_rot in stt.
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
    apply straightcond in phaseu.
    rewrite <- zeqx, yeq0 in phaseu.
    autorewrite with null in phaseu.
    lra. }

  unfold o, p.
  specialize (maxlength_path_std_part2
                _ _ _ _ _ _ Du ru θu tup lt rur tur phaseu npx t1rbletd stt u)
    as [Dv [pv [tvp v]]].
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.


Corollary maxlength_path_part3 :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rulb : ra <= ru)
         (rueq : ru = rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru θ₀ x₀ y₀ x₁ y₁),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nO : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (nc : θmax <> 0)
           (t1rbletd : θ1 x y rb > θd)
           (stt: straight rb θ₀ x₀ y₀ x₁ y₁),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx rb θ₀ x₀ θv tvp) (Hy rb θ₀ y₀ θv tvp) o p
           /\ Du <= Dv)).
Proof.
  intros until 9.
  intro u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  apply straight_rot in phaseu.
  apply straight_rot in stt.
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
    apply straightcond in phaseu.
    rewrite <- zeqx, yeq0 in phaseu.
    autorewrite with null in phaseu.
    lra. }

  unfold o, p.
  specialize (maxlength_path_std_part3
                _ _ _ _ _ _ Du ru θu tup lt rulb rueq tur phaseu npx t1rbletd stt u)
    as [Dv [pv [tvp v]]].
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.

Corollary maxlength_path_part4 :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru θ₀ x₀ y₀ x₁ y₁),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nO : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (nc : θmax <> 0)
           (tmletd : θmax <= θd)
           (stt: turning rb θ₀ x₀ y₀ x₁ y₁),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw θ₀ x₀ θmax twp) (Hy rw θ₀ y₀ θmax twp) o p /\
           Du <= Dw)).
Proof.
  intros until 8.
  intro u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  apply straight_rot in phaseu.
  apply turning_rot in stt.
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
    apply straightcond in phaseu.
    rewrite <- zeqx, yeq0 in phaseu.
    autorewrite with null in phaseu.
    lra. }

  unfold o, p.
  specialize (maxlength_path_std_part4
                _ _ _ _ _ _ Du ru θu tup lt rur tur phaseu npx tmletd stt u)
    as [Dv [pv [tvp v]]].
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.


Corollary maxlength_path_part5 :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru θ₀ x₀ y₀ x₁ y₁),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nO : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (nc : θmax <> 0)
           (tmgttd : θd < θmax)
           (rbt: turning rb θ₀ x₀ y₀ x₁ y₁),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw θ₀ x₀ θd twp) (Hy rw θ₀ y₀ θd twp) o p /\
           Du <= Dw)).
Proof.
  intros until 8.
  intro u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  apply straight_rot in phaseu.
  apply turning_rot in rbt.
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
    apply straightcond in phaseu.
    rewrite <- zeqx, yeq0 in phaseu.
    autorewrite with null in phaseu.
    lra. }

  unfold o, p.
  specialize (maxlength_path_std_part5
                _ _ _ _ _ _ Du ru θu tup lt rur tur phaseu npx tmgttd rbt u)
    as [Dv [pv [tvp v]]].
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.

Theorem minlength_path :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru θ₀ x₀ y₀ x₁ y₁),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nc : θmax <> 0),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx ra θ₀ x₀ θv tvp) (Hy ra θ₀ y₀ θv tvp) o p
           /\  Dv <= Du)) \/
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw θ₀ x₀ θc twp) (Hy rw θ₀ y₀ θc twp) o p /\
           Dw <= Du)).
Proof.
  intros until 5.
  intro u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  apply straight_rot in phaseu.
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
    apply straightcond in phaseu.
    rewrite <- zeqx, yeq0 in phaseu.
    autorewrite with null in phaseu.
    lra. }

  specialize (minlength_path_std
           _ _ _ _ _ _ Du ru θu tup lt rur tur phaseu npx u)
    as [[Dv [pv [tvp v]]] |[Dv [pv [tvp v]]]].
  left.
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
  right.
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.


Corollary minlength_path_part1 :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra < ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru θ₀ x₀ y₀ x₁ y₁),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nO : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (nc : θmax <> 0)
           (t1rbletd : (θ1 x y ra) < θc),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (exists Dw rw twp,
          (ra <= rw <= rb /\
           path_segment Dw (Hx rw θ₀ x₀ θc twp) (Hy rw θ₀ y₀ θc twp) o p /\
           Dw <= Du)).
Proof.
  intros until 7.
  intro u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  apply straight_rot in phaseu.
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
    apply straightcond in phaseu.
    rewrite <- zeqx, yeq0 in phaseu.
    autorewrite with null in phaseu.
    lra. }

  specialize (minlength_path_std_part1
           _ _ _ _ _ _ Du ru θu tup lt rur tur phaseu npx t1rbletd u)
    as [Dv [pv [tvp v]]].
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.

Corollary minlength_path_part2 :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (raeq : ra = ru)
         (ruub : ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru θ₀ x₀ y₀ x₁ y₁),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nO : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (nc : θmax <> 0)
           (t1rbletd : (θ1 x y ra) < θc),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx ra θ₀ x₀ θv tvp) (Hy ra θ₀ y₀ θv tvp) o p
           /\  Dv <= Du)).
Proof.
  intros until 8.
  intro u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  apply straight_rot in phaseu.
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
    apply straightcond in phaseu.
    rewrite <- zeqx, yeq0 in phaseu.
    autorewrite with null in phaseu.
    lra. }

  specialize (minlength_path_std_part2
           _ _ _ _ _ _ Du ru θu tup lt raeq ruub tur phaseu npx t1rbletd u)
    as [Dv [pv [tvp v]]].
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.


Corollary minlength_path_part3 :
  forall θ₀ x₀ y₀ x₁ y₁ ra rb  θc θd Du ru θu tup
         (lt : 0 < ra)
         (rur : ra <= ru <= rb)
         (tur : θc <= θu <= θd)
         (phaseu :straight ru θ₀ x₀ y₀ x₁ y₁),
    let o := (mkpt x₀ y₀) in
    let p := (mkpt x₁ y₁) in
    let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
    let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
    let θmax := calcθ₁ θ₀ x₀ y₀ x₁ y₁ in
    forall (nO : ~ (x₁ - x₀ = 0 /\ y₁ - y₀ = 0))
           (nc : θmax <> 0)
           (t1rbgttd : θc <= θ1 x y ra),
      path_segment Du (Hx ru θ₀ x₀ θu tup) (Hy ru θ₀ y₀ θu tup) o p ->
      (exists Dv θv tvp,
          (θc <= θv <= θd /\
           path_segment Dv (Hx ra θ₀ x₀ θv tvp) (Hy ra θ₀ y₀ θv tvp) o p
           /\  Dv <= Du)).
Proof.
  intros until 7.
  intro u.

  apply path_std in u.
  unfold θmax in *.
  clear θmax.
  rewrite calc_angle_std in *.
  apply straight_rot in phaseu.
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
    apply straightcond in phaseu.
    rewrite <- zeqx, yeq0 in phaseu.
    autorewrite with null in phaseu.
    lra. }

  specialize (minlength_path_std_part3
           _ _ _ _ _ _ Du ru θu tup lt rur tur phaseu npx t1rbgttd u)
    as [Dv [pv [tvp v]]].
  exists Dv, pv, tvp;
    unfold o, p;
    rewrite path_std;
    assumption.
Qed.



(*

nuking a mosqito, i.e. solving a simple-seeming problem with machinery
more

however, it is these simple-seeming problems upon which engineers make
their judgements and build systems;

if we are to apply formal methods to guarantee the correctness of
practical systems, we must be able to formalize and prove properties
about these problems with ease

This is the sort of problems that engineers consider straightforward
in practice, but formalizing it is not. If we expect our tools to be
adopted for wider use, the added difficulty of formalizing the problem
should be commensurate with the difficulty of solving the problem in
the first place.

The tools that we have for the task today are adequate, but a great
deal of infrastructure -- in terms of basic mathematical facts -- is
missing and sometimes needs to be constructed.

The verdict of this paper is that it is not yet possible to widely
adopt tools, there are too many basic mathematical facts that people
take for granted that are missing from the standard library. But we
are almost there. Even during this development some of the decision
procedures for basic arithmetic were upgraded, allowing for
significant speedups in development (i.e. improvements to the fourier
tactic to lra)

This analysis in intended to: provide insight into timing properties
of one-turn-to-bearing motion; analyze timing parameters so that we
can effectively compose these dynamics with others; and find an
efficient strategy for computing one-turn-to-bearing timing
characteristics

quantifies over the reachable geometry in unbounded time

Why spend time formalizing one-turn-to-bearing properties for aircraft
that are translated and rotated?  For full generality when reasoning
about the timing and motion of two vehicles, the timing needs to be We
did this for properties we judged would be useful for

Developed a library about turning, and applied it to a reasoning task,
that of quantifying timing characteristics.

This is just the type of analysis engineers encounter in their daily
work. It helps us understand the details of our system behavier, and
use that understanding to develop architecture and solutions.

This formalization serves as a case sudy for the use of formal methods
in daily workflow, as well as the development of infrastructure (the
library of proofs) to make reasoning about this type of geometric
problem easier in the future.

The library is somewhat disorganized, because developing it was
simultaneously an exploration of the dynamics and an exploration of
how to formalize those ideas in our proof environment.

We did this with a focus on the limited time and resources.

*)                                           

(* require_turn *)

