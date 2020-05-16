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
(* Require Import tdyn. *)
Require Import util.
Require Import strt.

Import Lra.
Open Scope R_scope.
Set Bullet Behavior "Strict Subproofs".



Lemma posroot_odd_Q1_rpos :
  forall x₁ y₁ r θ
         (x1quad :  0 <= x₁)
         (y1quad : 0 < 2*r - y₁)
         (y1pos : 0 < y₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 5. intros k2vale.
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp.
  inversion_clear k2vale as [n k2val].
  exists (2*n+1)%Z. assumption.

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. split. setl (- (2*PI)/2). assumption.
  setr (2*PI/2). assumption.
  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id. field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n + 1) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k) + 1) * PI) as id.
  assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2.
  rewrite mult_IZR. field.
  rewrite id2. clear id2.
  fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k) + 1) * PI)
               (θ + (IZR (2 * k) + IZR (2 * (n - k) + 1)) * PI).
  rewrite <- plus_IZR.
  assert ((2 * k + (2 * (n - k) + 1)) = 2 * n + 1)%Z as id3. omega.
  rewrite id3. clear id3. reflexivity.
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k) + 1) * PI) in k2def.
  clear slb sub.

  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
    rewrite id in phase. clear id.
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def.
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption.
    assert (y₁ = r * (1-cos q)) as y1def.
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption.
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id.
    unfold Rsqr.
    setl (r * r * (sin q * sin q + cos q * cos q - 1)).
    change (r * r * ((sin q)² + (cos q)² - 1) = 0).
    rewrite sin2_cos2. field.
    rewrite id in phase. lra. }
  
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp. {
  exists (2* (n-k) + 1)%Z. assumption. }
  
  assert (r<>0) as rne0. intro. subst. lra.
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  inversion_clear qrng as [qlb qub].
  inversion_clear qub as [qlt0 | qeq0].

  + assert (q <> 0) as qne0.
    intro qeq0. rewrite qeq0 in *.
    unfold κ₂ in k2def.
    rewrite sin_0, cos_0 in k2def.
    
    assert (y₁ - r * (1 - 1) = y₁) as y1def. field.
    assert (x₁ - r * 0 = x₁) as x1def. field.
    rewrite y1def, x1def in k2def.
    rewrite Rplus_0_l in k2def.
    
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO.
    intro. inversion_clear H as [xO yO].
    rewrite xO, yO in *. lra.
    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].
    
    assert (- 1 < 2 * (n - k) + 1)%Z as Zlb.
    apply lt_IZR.
    apply (Rmult_lt_reg_r (PI)). assumption. setl (-PI).
    assumption.
    
    assert (2 * (n - k) + 1 <= 1)%Z as Zub.
    apply le_IZR.
    apply (Rmult_le_reg_r (PI)). assumption. setr (PI).
    assumption.
    
    assert ((n-k)%Z = 0%Z) as nmkeq0. omega.
    rewrite nmkeq0 in k2def. clear nmkeq0.
    assert ((2 * 0 + 1)%Z = 1%Z) as id. omega.
    rewrite id in k2def. clear id.
    assert (1 * PI = PI) as id. field. rewrite id in k2def. clear id.
    clear Zlb Zub at2ub at2lb y1def x1def.
    specialize (atan2_PI_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra.
    
    rename phase into phasec.
    rename phaseb into phase.
    
    assert (- PI < q < PI) as qbnd. split; assumption.
    assert (2 * r - y₁ <> 0) as ntc. intro. lra.
    specialize (k_deriv_sign_quad2 _ _ _ _ qbnd rne0 phase ntc s0) as [sn | sp].
    exfalso.
    
    assert (0 < q) as zltq.
    apply (Rmult_lt_reg_r (/2)). lra. setl 0. setr (q/2).
    rewrite sn.
    rewrite <- (sqrt_Rsqr x₁) at 1; [| assumption].
    
    assert (0 < (2 * r - y₁) * y₁) as id1.
    apply Rmult_lt_0_compat; assumption.
    

    assert (0 < sqrt x₁² - sqrt (x₁² - (2 * r - y₁) * y₁)) as npos.
    apply (Rplus_lt_reg_l (sqrt (x₁² - (2 * r - y₁) * y₁))).
    setr (sqrt x₁²). setl (sqrt (x₁² - (2 * r - y₁) * y₁)).
    apply sqrt_lt_1.
    
    setr (x₁² + y₁ * y₁ - 2 * r * y₁).
    apply (Rplus_le_reg_r r²). setl (r²).
    unfold Rsqr at 3.
    setr (x₁² + (y₁-r)²). left. assumption.
    
    apply Rle_0_sqr.
    
    apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)). setl 0.
    setr ((2 * r - y₁) * y₁). assumption.
    
    
    assert (0 < (sqrt x₁² - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) as argpos.
    apply Rdiv_lt_0_compat. assumption. assumption.
    rewrite <- atan_0.
    apply atan_increasing. assumption.
    
    assert (-PI < κ₂ x₁ y₁ r q <= PI) as k2rng.
    unfold κ₂.
    apply atan2_bound.
    assumption.
    rewrite k2def in k2rng.
    
    destruct (n-k)%Z.
    ++ simpl in k2rng.
       inversion_clear k2rng as [k2lb [k2ub | k2eq]].
       assert (PI < q + 1 * PI) as qgtPI. lra.
       lra. apply qne0. apply (Rplus_eq_reg_r PI).
       rewrite <- k2eq at 2. field.
       
    ++ assert (3 <= IZR (2 * Z.pos p + 1)) as postm.
       rewrite plus_IZR, mult_IZR.
       assert (1 <= IZR (Z.pos p)) as pospos.
       apply IZR_le.
       specialize (Zle_0_pos p) as zleZpos.
       assert (Z.pos p <> 0)%Z.
       discriminate. omega.
       apply (Rle_trans _ (2 * 1 + 1)). 
       lra. lra.
       inversion_clear k2rng as [k2lb [k2ub | k2eq]].
       assert (2 * PI < q + IZR (2 * Z.pos p + 1) * PI) as qgtPI.
       apply (Rlt_le_trans _ (q + 3 * PI)). 
       lra.
       apply (Rplus_le_reg_r (-q)). setl (3 * PI).
       setr (IZR (2 * Z.pos p + 1) * PI).
       apply (Rmult_le_reg_r (/PI)).
       apply Rinv_0_lt_compat. lra.
       setl 3. intro. lra. setr (IZR (2 * Z.pos p + 1)). intro. lra.
       assumption.
       lra.
       assert (3 < 1) as fo.
       apply (Rle_lt_trans _ (IZR (2 * Z.pos p + 1))).
       assumption.
       apply (Rmult_lt_reg_r PI). lra. setr PI.
       rewrite <- k2eq at 2.
       apply (Rplus_lt_reg_r (- IZR (2 * Z.pos p + 1) * PI)).
       setl 0. setr q. assumption. lra.
       
    ++ assert (IZR (2 * Z.neg p + 1) <= -1 ) as negtm.
       rewrite plus_IZR, mult_IZR.
       assert (IZR (Z.neg p) <= -1) as negneg.
       rewrite <- Pos2Z.opp_pos.
       rewrite opp_IZR.
       apply Ropp_le_contravar.
       change (IZR 1 <= IZR (Z.pos p)).
       apply IZR_le.
       specialize (Zle_0_pos p) as zleZpos.
       assert (Z.pos p <> 0)%Z.
       discriminate. omega.
       apply (Rle_trans _ (2 * (- 1) + 1)).
       apply (Rplus_le_reg_r (-1)). setr (2 * -1). setl (2 * IZR (Z.neg p)).
       apply (Rmult_le_reg_r (/2)).
       apply Rinv_0_lt_compat. lra.
       setr (-1). setl (IZR (Z.neg p)). assumption.
       lra.
       inversion_clear k2rng as [k2lb [k2ub | k2eq]].
       +++ inversion_clear negtm as [ltm1 | eqm1].
           ++++ assert (q + IZR (2 * Z.neg p + 1) * PI < - PI) as qgtPI.
                
                assert (2 * Z.neg p + 1 < -1)%Z as Zineq. apply lt_IZR. assumption.
                assert (IZR (2 * Z.neg p + 1) <= -3) as IZRm2.
                apply IZR_le. omega. clear ltm1 Zineq.
                
                apply (Rle_lt_trans _ (q + - 3 * PI)). 
                apply (Rplus_le_reg_r (-q)). setr (- 3 * PI).
                setl (IZR (2 * Z.neg p + 1) * PI).
                apply (Rmult_le_reg_r (/PI)).
                apply Rinv_0_lt_compat. lra.
                setr (-3). intro. lra. setl (IZR (2 * Z.neg p + 1)). intro. lra.
                assumption.
                lra.
                lra.
  
           ++++ rewrite eqm1 in *.
                clear eqm1.
                
                clear k2lb k2ub qlb.
                (* unfold κ₂ in k2def. *)
                assert (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁) < x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) as numord.
                apply (Rplus_lt_reg_l (-x₁)).
                setl (- sqrt (x₁² - (2 * r - y₁) * y₁)).
                setr (sqrt (x₁² - (2 * r - y₁) * y₁)).
                apply pos_opp_lt.
                apply sqrt_lt_R0.
                apply (Rplus_lt_reg_l (r²)). setl (r²). setr (x₁² + (y₁ - r)²). assumption.
                
                assert ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))/ (2 * r - y₁) <
                        (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))/ (2 * r - y₁)) as argord.
                apply (Rmult_lt_reg_l (2 * r - y₁)). assumption.
                setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)). assumption.
                setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)). assumption.
                assumption.
                
                specialize (atan_increasing _ _ argord) as rtord.
                clear numord. 
                set (s := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *.
                set (s' := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *.
                assert (0 < atan s) as atmlb.
                apply (Rmult_lt_reg_l 2). lra. setl 0. rewrite <- sn. setr q. assumption.
                assert (atan s < PI/2) as atmub.
                apply (Rmult_lt_reg_l 2). lra. setr PI. rewrite <- sn. setl q. assumption.
                specialize (atan_bound ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) as [atplb atpub].
                clear atplb. change (atan s' < PI/2) in atpub.
                assert (0 < atan s') as atplb.
                apply (Rlt_trans _ (atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))).
                assumption. assumption.
    
                set (q' := 2 * atan s').
                assert (0 < q') as zltq'. unfold q'. lra.
                assert (q' < PI) as q'ltPI. unfold q'. lra.
                assert (-PI < q' < PI) as q'rng. unfold q'. split; lra.
                assert (q' <> 0) as q'ne0. unfold q'. intro. lra.
                assert (sign (κ' x₁ y₁ r q') = 0) as s1.
                
                rewrite (k_deriv_sign_rng _ _ _ _ q'rng rne0 phase).
                unfold q'.
                
                fieldrewrite (2 * atan s' / 2) (atan s').
                rewrite atan_right_inv.
                assert (r * ((2 * r - y₁) * s'² - 2 * x₁ * s' + y₁) = 0) as id.
                assert ((2 * r - y₁) / r <> 0) as prodne0.
                specialize (Rdiv_lt_0_compat _ _ y1quad rgt0) as prodgt0. intro.
                rewrite H in prodgt0. lra.
                apply (Rmult_eq_reg_r ((2 * r - y₁)/r)); [|assumption]. setr 0. assumption.
                unfold s'.
                setl ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))² -
                      2 * x₁ * ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))) + y₁ * (2 * r - y₁)).
                split; assumption. unfold Rsqr.
                setl ((sqrt (x₁² - (2 * r - y₁) * y₁))² - x₁² + y₁ * (2 * r - y₁)).
                rewrite Rsqr_sqrt. field. left.
                apply (Rplus_lt_reg_l (r²)). setl (r²). setr (x₁² + (y₁ - r)²). assumption.
                rewrite id. apply sign_0.
                assert (- PI < q' <= PI) as q'rng2. inversion_clear q'rng. split; lra.
                
                (*********)
                assert (~ (x₁ - r * sin q' = 0 /\ y₁ - r * (1 - cos q') = 0)) as noton'. {
                  intro notx1y1.
                  inversion_clear notx1y1 as [xnot ynot].
                  
                  assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
                  rewrite id in phasec. clear id.
                  rewrite <- (Rplus_0_l r²) in phasec at 1.
                  apply RIneq.Rplus_lt_reg_r in phasec.
                  assert (x₁ = r * sin q') as x1def.
                  rewrite <- Rplus_0_r, <- xnot. field.
                  assert (y₁ = r * (1 - cos q')) as y1def.
                  rewrite <- Rplus_0_r, <- ynot. field.
                  rewrite x1def, y1def in phasec.
                  assert ((r * sin q')² - (2 * r - r * (1 - cos q')) * (r * (1 - cos q')) = 0) as id.
                  unfold Rsqr.
                  setl (r * r * (sin q' * sin q' + cos q' * cos q' - 1)).
                  change (r * r * ((sin q')² + (cos q')² - 1) = 0).
                  rewrite sin2_cos2. field.
                  rewrite id in phasec. lra. }
      
                (**********)
                generalize s1. intro s1'.
                unfold sign in s1.
                specialize (atan2_bound _ _ noton') as at2rng.
                change (- PI < κ₂ x₁ y₁ r q' <= PI) in at2rng.
                inversion_clear at2rng as [at2lb at2ub].
                
                destruct (total_order_T 0 (κ' x₁ y₁ r q')).
                destruct s2. lra. symmetry in e. clear s1.
                rewrite (k_extrema_vals y₁ x₁ r q' q'rng2 rne0 noton') in e.
                inversion_clear e as [m k2def2].
                exfalso.
                assert (κ₂ x₁ y₁ r q < κ₂ x₁ y₁ r q') as k2order. rewrite k2def2, k2def.
                unfold q'.
                assert (q = 2 * atan s) as qdef. rewrite <- sn. field. rewrite qdef.
                destruct m. lra.
                
                exfalso.
                rewrite k2def2 in at2ub.
                assert (1 <= IZR (Z.pos p0)) as ord.
                apply IZR_le.
                specialize (Zgt_pos_0 p0) as nonz. omega.
                apply (Rmult_le_compat_r PI) in ord.
                apply (Rplus_le_compat_l q') in ord.
                lra. lra.
                
                rewrite k2def2 in at2lb.
                assert (- PI + IZR (Z.pos p0) * PI < q') as ord.
                rewrite <- Pos2Z.opp_neg, Ropp_Ropp_IZR.
                apply (Rplus_lt_reg_r (IZR (Z.neg p0) * PI)). setl (-PI). assumption.
                assert (1 <= IZR (Z.pos p0)) as ord2.
                apply IZR_le.
                specialize (Zgt_pos_0 p0) as nonz. omega.
                inversion_clear ord2 as [oltIZR | oeqIZR].
                assert (2 <= IZR (Z.pos p0)) as ord3.
                apply IZR_le.
                apply lt_IZR in oltIZR.
                omega.
                exfalso.
                apply (Rmult_le_compat_r PI) in ord3.
                apply (Rplus_le_compat_l q') in ord3.
                lra. lra.
                
                rewrite <- (Pos2Z.opp_pos p0), Ropp_Ropp_IZR.
                rewrite <- oeqIZR in *.
                apply (Rplus_lt_reg_r (PI)). setl (2 *atan s). setr (2 * atan s').
                lra.
                clear k2def2.
                
                assert (forall z, q < z < q' -> κ' x₁ y₁ r z < 0) as signs. {
                  intros.
                  specialize (k_deriv_sign_quad_Apos_rpos _ _ _ y1quad rgt0 phase) as signsgen.
                  inversion_clear H as [qlb qub].
                  assert (- PI < z < PI) as zrng. split; lra.
                  assert (z <> 0) as zne0. intro. lra.
                  specialize (signsgen z zrng). inversion_clear signsgen as [lsg rsg].
                  
                  rewrite <- signeqm1_eqv.
                  apply lsg.
                  change (atan s < z / 2 < atan s').
                  split. rewrite <- sn. lra.
                  apply (Rmult_lt_reg_l 2). lra. setl z. change (z < q'). assumption.  }
                
                rewrite signeq0_eqv in s1', s0.
    
                assert (q < q') as qltq'.
                unfold q'.
                apply (Rmult_lt_reg_r (/2)).
                apply Rinv_0_lt_compat. lra.
                setl (q/2). setr (atan s').
                rewrite sn. assumption.
                
                (*************************)
                set (h := κ₂ x₁ y₁ r) in *.
                
                assert (forall z,
                           ~ (x₁ - r * sin z <= 0 /\ y₁ - r * (1 - cos z) = 0)) as idsc. {
                  intros. intro. inversion_clear H as [xcond ycond].
                  assert (x₁² + (y₁ - r)² <= r²) as contra.
                  assert (x₁² <= (r * sin z)²) as x1ineq.
                  apply sqrt_le_0. apply Rle_0_sqr.
                  apply Rle_0_sqr.
                  rewrite sqrt_Rsqr; [| lra].
                  rewrite sqrt_Rsqr; [| lra].
                  lra.
                  assert (y₁ - r = - (r * cos z)) as ymrdef.
                  apply (Rplus_eq_reg_r (r*cos z)). setr 0. rewrite <- ycond.
                  field.
                  rewrite ymrdef.
                  rewrite <- Rsqr_neg.
                  rewrite Rsqr_mult.
                  rewrite <- Rmult_1_r.
                  rewrite <- (sin2_cos2 z).
                  rewrite Rmult_plus_distr_l.
                  rewrite Rsqr_mult in x1ineq.
                  lra. lra. }
                
                
                assert (derivable h) as derf. {
                  unfold derivable. intros.
                  apply ex_derive_Reals_0.
                  unfold ex_derive. simpl.
                  exists (κ' x₁ y₁ r x).
                  apply (k_is_derive_atan2 _ _ _ _ rne0 (idsc x)). }
                
                assert (forall z:R, is_derive (κ₂ x₁ y₁ r) z (κ' x₁ y₁ r z)) as k2deriv. {
                  intro.
                  apply (k_is_derive_atan2 _ _ _ _ rne0 (idsc z)). }
                
                change (forall z : R, is_derive h z (κ' x₁ y₁ r z)) in k2deriv.
                assert (forall z : R, q < z < q' -> derive_pt h z (derf z) < 0) as cond. {
                  intros.
                  specialize (k2deriv z).
                  rewrite Derive_Reals.
                  rewrite (is_derive_unique _ _ _ k2deriv).
                  apply signs. assumption. }
                
                specialize (derive_decreasing_interv q q' h derf qltq' cond) as hdecr. {
                  assert (q <= q <= q') as qpos. split; lra.
                  assert (q <= q' <= q') as q'pos. split; lra.
                  specialize (hdecr _ _ qpos q'pos qltq').
                  lra. }
      
                lra.
       +++ apply noton.
                
           rewrite <- k2eq in qlt0.
           assert (0 < IZR (2 * Z.neg p + 1)) as postm.
           apply (Rmult_lt_reg_r PI). assumption.
           apply (Rplus_lt_reg_l q). setl q. assumption.
           lra.
           
    ++ exists (-k)%Z.
       rewrite <- sp.
       fieldrewrite (2*(q/2)) q.
       rewrite mult_IZR, opp_IZR.
       apply (Rplus_eq_reg_r (2 * IZR k * PI)).
       setr q. unfold q. field.

  + exfalso.
    unfold κ₂ in k2def.
    rewrite qeq0 in *.
    rewrite cos_PI, sin_PI in k2def.
    
    assert (y₁ - r * (1 - -1) = y₁ - 2 * r ) as id. field.
    rewrite id in k2def. clear id.
    assert (x₁ - r * 0 = x₁) as id. field.
    rewrite id in k2def. clear id.
    
    assert (y₁ - 2 * r < 0) as yinq. lra.
    assert (- (PI / 2) <= atan2 (y₁ - 2 * r) (x₁) < 0) as a2inq. {
    inversion_clear x1quad as [x1gt0 |x1eq0].
    specialize (atan2Q4 _ _ x1gt0 yinq) as [a2l a2u].
    split; [left|]; assumption.
    rewrite <- x1eq0, (atan2_mPI2 _ yinq).
    split; [right; setl (-PI/2); reflexivity|
            apply (Rmult_lt_reg_r 2);
            [lra|
             setl (-PI); setr 0; lra]]. }
    rewrite k2def in a2inq.
    rewrite plus_IZR, mult_IZR in a2inq.
    assert (PI + (2 * IZR (n - k) + 1) * PI =
            2* (IZR (n - k + 1)) * PI) as mult2PI.
    rewrite plus_IZR. field. rewrite mult2PI in a2inq. clear mult2PI.
    
    inversion_clear a2inq as [a2lb a2ub].
    destruct (n - k + 1)%Z.
    ++ lra.
    
    ++ specialize (Zle_0_pos p) as zleZpos.
       apply IZR_le in zleZpos.
       apply Ropp_lt_contravar in a2ub.
       rewrite Ropp_0 in a2ub.
       rewrite Rmult_assoc in a2ub.
       rewrite Ropp_mult_distr_r in a2ub.
       rewrite Ropp_mult_distr_l in a2ub.
       rewrite <- Rmult_assoc in a2ub.
       rewrite Rmult_comm in a2ub.
       rewrite <- Rmult_assoc in a2ub.
       assert (0 <= PI * 2) as zle2PI. lra.
       specialize (zlt_mult _ _ a2ub zle2PI) as cdx. lra.
       
    ++ clear a2ub.
       rewrite <- Pos2Z.opp_pos in a2lb.
       specialize (Zle_0_pos p) as zleZpos.
       assert (Z.pos p <> 0)%Z.
       discriminate.
       assert (1 <= Z.pos p)%Z as zltZpos. omega. clear H zleZpos.
       rewrite opp_IZR in a2lb.
       apply IZR_le in zltZpos.
       
       rewrite Rmult_assoc in a2lb.
       rewrite Rmult_comm in a2lb.
       rewrite Rmult_assoc in a2lb.
       rewrite Ropp_mult_distr_l_reverse in a2lb.
       apply Ropp_le_contravar in a2lb.
       rewrite Ropp_involutive in a2lb.
       rewrite Ropp_involutive in a2lb.
       assert (4 * IZR (Z.pos p) <= 1) as a2lb2.
       apply (Rmult_le_reg_r (PI/2)).
       lra.
       setr (PI/2). setl (IZR (Z.pos p) * (PI * 2)).  assumption.
       lra.
Qed.


Lemma negroot_even_Q1_rpos :
  forall x₁ y₁ r θ
         (x1quad :  0 <= x₁)
         (y1quad : 0 < 2*r - y₁)
         (y1pos : 0 < y₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) -> 
    exists m, θ = 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) + 
        IZR (2 * m) * PI.
Proof.
  intros until 5. intros k2vale.
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp.
  inversion_clear k2vale as [n k2val].
  exists (2*n)%Z. assumption.


  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. split. setl (- (2*PI)/2). assumption.
  setr (2*PI/2). assumption.
  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id. field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k)) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2. {
      rewrite mult_IZR. field. }
    rewrite id2. clear id2.
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k)) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k))) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k))) = 2 * n)%Z as id3. omega.
    rewrite id3. clear id3. reflexivity. }
  
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k)) * PI) in k2def.
  clear slb sub.

  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field. 
    rewrite id in phase. clear id.
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def.
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption.
    assert (y₁ = r * (1-cos q)) as y1def.
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption.
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id.
    unfold Rsqr.
    setl (r * r * (sin q * sin q + cos q * cos q - 1)).
    change (r * r * ((sin q)² + (cos q)² - 1) = 0).
    rewrite sin2_cos2. field.
    rewrite id in phase. lra. }
  
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp. {
  exists (2* (n-k))%Z. assumption. }

  assert (r<>0) as rne0. intro. subst. lra.
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  inversion_clear qrng as [qlb qub].
  inversion_clear qub as [qlt0 | qeq0].

  + assert (q <> 0) as qne0. {
    intro qeq0. rewrite qeq0 in *.
    unfold κ₂ in k2def.
    rewrite sin_0, cos_0 in k2def.
    
    assert (y₁ - r * (1 - 1) = y₁) as y1def. field.
    assert (x₁ - r * 0 = x₁) as x1def. field.
    rewrite y1def, x1def in k2def.
    rewrite Rplus_0_l in k2def.
    
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO.
    intro. inversion_clear H as [xO yO].
    rewrite xO, yO in *. lra.
    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].
    
    assert (- 1 < 2 * (n - k))%Z as Zlb.
    apply lt_IZR.
    apply (Rmult_lt_reg_r (PI)). assumption. setl (-PI).
    assumption.
  
    assert (2 * (n - k) <= 1)%Z as Zub.
    apply le_IZR.
    apply (Rmult_le_reg_r (PI)). assumption. setr (PI).
    assumption.
    
    assert ((n-k)%Z = 0%Z) as nmkeq0. omega.
    rewrite nmkeq0 in k2def. clear nmkeq0.
    rewrite mult_IZR in k2def.
    autorewrite with null in k2def.
    clear Zlb Zub at2ub at2lb y1def x1def.
    specialize (atan2_0_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra. }
    
    rename phase into phasec.
    rename phaseb into phase.
    
    assert (2 * r - y₁ <> 0) as ntc. intro. lra.
    specialize (k_deriv_sign_quad2 _ _ _ _ (conj qlb qlt0) rne0 phase ntc s0) as [sn | sp].
    ++ exists (-k)%Z.
       rewrite <- sn, mult_IZR, opp_IZR.
       unfold q.
       field.
       
    ++ exfalso.

       assert (0 < q) as zltq. {
       apply (Rmult_lt_reg_r (/2)); try lra. setl 0. setr (q/2).
       rewrite sp.
       rewrite <- (sqrt_Rsqr x₁) at 1; [| assumption].
       
       assert (0 < (2 * r - y₁) * y₁) as id1. {
       apply Rmult_lt_0_compat; assumption. }

       assert (0 < sqrt x₁² + sqrt (x₁² - (2 * r - y₁) * y₁)) as npos. {
         apply (Rplus_lt_reg_l ( - sqrt (x₁² - (2 * r - y₁) * y₁))).
         setr (sqrt x₁²). setl (- sqrt (x₁² - (2 * r - y₁) * y₁)).
         apply (Rlt_le_trans _ 0).
         
         rewrite <- Ropp_0.
         apply Ropp_lt_contravar.
         apply sqrt_lt_R0.
         apply (Rplus_lt_reg_r (r²)).
         lrag phasec.
         zltab. }

       rewrite <- atan_0.
       apply atan_increasing.
       zltab. }
       
       assert (-PI < κ₂ x₁ y₁ r q <= PI) as k2rng.
       unfold κ₂.
       apply atan2_bound.
       assumption.

       case_eq (n-k)%Z.
       +++ intro nkz.
           rewrite nkz in *.
           assert (n = k) as neqk. omega.
           rewrite neqk in *.
           clear nkz neqk n.
           autorewrite with null in k2def.
           (* unfold q in k2def. *)
           (* rewrite (Rmult_comm (IZR k)), 
                      Rmult_assoc, (Rmult_comm PI), <- Rmult_assoc in k2def. *)
           (* rewrite <- k2_periodic, <- mult_IZR in k2def. *)
           clear k2vale k2valp qlb qne0 .

           (*****)
           exfalso.
           let m := fresh "D" in 
           match goal with
           | sp : ?q / 2 = atan ((x₁ + ?D)/?n) |- _ =>
             set (m := D) in *
           end.
           assert (x₁ - D < x₁ + D) as numord. {
             apply (Rplus_lt_reg_l (-x₁)).
             setl (- D).
             setr D.
             apply pos_opp_lt.
             apply sqrt_lt_R0.
             apply (Rplus_lt_reg_l (r²)). setl (r²). setr (x₁² + (y₁ - r)²). assumption. }
             
           assert ((x₁ - D)/ (2 * r - y₁) <
                   (x₁ + D)/ (2 * r - y₁)) as argord. {
             apply (Rmult_lt_reg_l (2 * r - y₁)). assumption.
             setl (x₁ - D). assumption.
             setr (x₁ + D). assumption.
             assumption. }

           specialize (atan_increasing _ _ argord) as rtord.
           clear numord. 
           set (s' := ((x₁ - D) / (2 * r - y₁))) in *.
           set (s := ((x₁ + D) / (2 * r - y₁))) in *.
           assert (0 < atan s) as atmlb. {
             apply (Rmult_lt_reg_l 2). lra. setl 0. lra.  }
           assert (atan s < PI/2) as atmub. {
           apply (Rmult_lt_reg_l 2). lra. setr PI. lra. }

           assert (0 < (2 * r - y₁) * y₁) as id1. {
           apply Rmult_lt_0_compat; assumption. }

           assert (0 < x₁ - D) as npos. {
             apply (Rplus_lt_reg_l D).
             setr x₁. setl D.
             rewrite <- sqrt_Rsqr.
             apply sqrt_lt_1.
             
             setr (x₁² + y₁ * y₁ - 2 * r * y₁).
             apply (Rplus_le_reg_r r²). setl (r²).
             unfold Rsqr at 3.
             setr (x₁² + (y₁-r)²). left. assumption.
             
             apply Rle_0_sqr.

             apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)). setl 0.
             setr ((2 * r - y₁) * y₁). assumption.
             assumption. }

           assert (0 < atan s') as atplb. {
             assert (0 < (x₁ - D) / (2 * r - y₁)) as argpos. {
               apply Rdiv_lt_0_compat.  assumption.
               lra. }
             rewrite <- atan_0.
             apply atan_increasing. assumption. }

           
           set (q' := 2 * atan s').
           assert (0 < q') as zltq'. unfold q'. lra.
           assert (q' < PI) as q'ltPI. unfold q'. lra.
           assert (-PI < q' < PI) as q'rng. unfold q'. split; lra.
           assert (q' <> 0) as q'ne0. unfold q'. intro. lra.

           assert (sign (κ' x₁ y₁ r q') = 0) as s1. {
           
             rewrite (k_deriv_sign_rng _ _ _ _ q'rng rne0 phase).
             unfold q'.
             
             fieldrewrite (2 * atan s' / 2) (atan s').
             rewrite atan_right_inv.
             assert (r * ((2 * r - y₁) * s'² - 2 * x₁ * s' + y₁) = 0) as id.
             assert ((2 * r - y₁) / r <> 0) as prodne0.
             specialize (Rdiv_lt_0_compat _ _ y1quad rgt0) as prodgt0. intro.
             rewrite H in prodgt0. lra.
             apply (Rmult_eq_reg_r ((2 * r - y₁)/r)); [|assumption]. setr 0. assumption.
             unfold s'.
             setl ((x₁ + D)² - 2 * x₁ * ((x₁ + D)) + y₁ * (2 * r - y₁)).
             split; assumption. unfold Rsqr.
             setl (D² - x₁² + y₁ * (2 * r - y₁)).
             unfold D.
             rewrite Rsqr_sqrt. field. left.
             apply (Rplus_lt_reg_l (r²)). setl (r²). setr (x₁² + (y₁ - r)²). assumption.
             rewrite id. apply sign_0. }

           assert (- PI < q' <= PI) as q'rng2. inversion_clear q'rng. split; lra.
             
           assert (~ (x₁ - r * sin q' = 0 /\ y₁ - r * (1 - cos q') = 0)) as noton'. {
             intro notx1y1.
             inversion_clear notx1y1 as [xnot ynot].   
             assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
             rewrite id in phasec. clear id.
             rewrite <- (Rplus_0_l r²) in phasec at 1.
             apply RIneq.Rplus_lt_reg_r in phasec.
             assert (x₁ = r * sin q') as x1def.
             rewrite <- Rplus_0_r, <- xnot. field.
             assert (y₁ = r * (1 - cos q')) as y1def.
             rewrite <- Rplus_0_r, <- ynot. field.
             rewrite x1def, y1def in phasec.
             assert ((r * sin q')² - (2 * r - r * (1 - cos q')) * (r * (1 - cos q')) = 0) as id.
             unfold Rsqr.
             setl (r * r * (sin q' * sin q' + cos q' * cos q' - 1)).
             change (r * r * ((sin q')² + (cos q')² - 1) = 0).
             rewrite sin2_cos2. field.
             rewrite id in phasec. lra. }
           
           specialize (atan2_bound _ _ noton') as at2rng.
           change (- PI < κ₂ x₁ y₁ r q' <= PI) in at2rng.
           destruct at2rng as [at2lb at2ub].
           
           generalize s1. intro s1'.
           rewrite signeq0_eqv in s1.
           rename s1 into e.
           rewrite (k_extrema_vals y₁ x₁ r q' q'rng2 rne0 noton') in e.
           destruct e as [m k2def2].

           
           assert (κ₂ x₁ y₁ r q' < κ₂ x₁ y₁ r q) as k2order. {
             rewrite k2def2, k2def.
             unfold q'.
             assert (q = 2 * atan s) as qdef. {
               lra. }
             rewrite qdef.
           
             destruct m.
             - arn. lra.
             - specialize (IZRposge1 p) as zp.
               exfalso.
               rewrite k2def2 in at2lb, at2ub.
               clear - at2ub pigt0 zp zltq' q'ltPI.
               destruct zp as [olt |oe].
               -- apply (Rmult_lt_compat_r PI) in olt; try lra.
               -- rewrite <- oe in *. 
                  lra.
             - specialize (IZRneglen1 p) as zn.
               apply (Rle_lt_trans _ (2 * atan s' + -1 * PI)).
               apply (Rplus_le_reg_r (- 2 * atan s')).
               apply (Rmult_le_reg_r (/ PI)); try zltab.
               lrag zn.
               lra. }


           assert (forall z, q' < z < q -> κ' x₁ y₁ r z < 0) as signs. {
             intros.
             specialize (k_deriv_sign_quad_Apos_rpos _ _ _ y1quad rgt0 phase) as signsgen.
             inversion_clear H as [qlb qub].
             assert (- PI < z < PI) as zrng. split; lra.
             assert (z <> 0) as zne0. intro. lra.
             specialize (signsgen z zrng).
             inversion_clear signsgen as [lsg rsg].
             change (atan s' < z/2 < atan s -> sign (κ' x₁ y₁ r z) = -1) in lsg.
             change (z/2 < atan s' \/ atan s < z/2 -> sign (κ' x₁ y₁ r z) = 1) in rsg.
             
             rewrite <- signeqm1_eqv.
             apply lsg.
             split.
             unfold q' in qlb.
             clear - qlb.
             lra.
             rewrite <- sp.
             clear - qub.
             lra. }
             
             rewrite signeq0_eqv in s1', s0.
             
           assert (q' < q) as qltq'. {
           unfold q'.
           assert (q = 2 * atan s) as id. lra.
           rewrite id.

           apply (Rmult_lt_reg_r (/2)).
           apply Rinv_0_lt_compat. lra.
           lra. }

           set (h := κ₂ x₁ y₁ r) in *.
           
           assert (forall z,
                      ~ (x₁ - r * sin z <= 0 /\ y₁ - r * (1 - cos z) = 0)) as idsc.
           intros. intro. inversion_clear H as [xcond ycond].
           assert (x₁² + (y₁ - r)² <= r²) as contra.
           assert (x₁² <= (r * sin z)²) as x1ineq.
           apply sqrt_le_0. apply Rle_0_sqr.
           apply Rle_0_sqr.
           rewrite sqrt_Rsqr; [| lra].
           rewrite sqrt_Rsqr; [| lra].
           lra.
           assert (y₁ - r = - (r * cos z)) as ymrdef.
           apply (Rplus_eq_reg_r (r*cos z)). setr 0. rewrite <- ycond.
           field.
           rewrite ymrdef.
           rewrite <- Rsqr_neg.
           rewrite Rsqr_mult.
           rewrite <- Rmult_1_r.
           rewrite <- (sin2_cos2 z).
           rewrite Rmult_plus_distr_l.
           rewrite Rsqr_mult in x1ineq.
           lra. lra.
           
           assert (derivable h) as derf. {
             unfold derivable. intros.
             apply ex_derive_Reals_0.
             unfold ex_derive. simpl.
             exists (κ' x₁ y₁ r x).
             apply (k_is_derive_atan2 _ _ _ _ rne0 (idsc x)). }
           assert (forall z:R, is_derive (κ₂ x₁ y₁ r) z (κ' x₁ y₁ r z)) as k2deriv. {
             intro.
             apply (k_is_derive_atan2 _ _ _ _ rne0 (idsc z)). }
           change (forall z : R, is_derive h z (κ' x₁ y₁ r z)) in k2deriv.
           assert (forall z : R, q' < z < q -> derive_pt h z (derf z) < 0) as cond. {
             intros.
             specialize (k2deriv z).
             rewrite Derive_Reals.
             rewrite (is_derive_unique _ _ _ k2deriv).
             apply signs. assumption. }
           
           specialize (derive_decreasing_interv q' q h derf qltq' cond) as hdecr.
           assert (q' <= q <= q) as qpos. split; lra.
           assert (q' <= q' <= q) as q'pos. split; lra.
           specialize (hdecr _ _ q'pos qpos qltq').
           lra.

       +++ intros p nm.
           rewrite nm in *.
           rewrite k2def, mult_IZR in k2rng.
           specialize (IZRposge1 p) as pge1.
           apply (Rmult_le_compat_r PI) in pge1; try lra.

       +++ intros p nm.
           rewrite nm in *.
           rewrite k2def, mult_IZR in k2rng.
           specialize (IZRneglen1 p) as pge1.
           apply (Rmult_le_compat_r PI) in pge1; try lra.

  + exfalso.
    unfold κ₂ in k2def.
    rewrite qeq0 in *.
    rewrite cos_PI, sin_PI in k2def.
    
    assert (y₁ - r * (1 - -1) = y₁ - 2 * r ) as id. field.
    rewrite id in k2def. clear id.
    assert (x₁ - r * 0 = x₁) as id. field.
    rewrite id in k2def. clear id.
    
    assert (y₁ - 2 * r < 0) as yinq. lra.
    assert (- (PI / 2) <= atan2 (y₁ - 2 * r) (x₁) < 0) as a2inq. {
      inversion_clear x1quad as [x1gt0 |x1eq0].
      specialize (atan2Q4 _ _ x1gt0 yinq) as [a2l a2u].
      split; [left|]; assumption.
      rewrite <- x1eq0, (atan2_mPI2 _ yinq).
      split; [right; setl (-PI/2); reflexivity|
              apply (Rmult_lt_reg_r 2);
              [lra|
               setl (-PI); setr 0; lra]]. }

    rewrite k2def in a2inq.
    rewrite mult_IZR in a2inq.
    inversion_clear a2inq as [a2lb a2ub].

    destruct (n - k)%Z.
    ++ lra.
    ++ specialize (IZRposge1 p) as zleZpos.
       apply (Rmult_le_compat_r PI) in zleZpos; try lra.
    ++ specialize (IZRneglen1 p) as zleZpos.
       apply (Rmult_le_compat_r PI) in zleZpos; try lra.
Qed.



Lemma posroot_odd_Q2_rpos :
  forall x₁ y₁ r θ
         (x1quad :  x₁ < 0)
         (y1quad : 0 < 2*r - y₁)
         (y1pos : 0 < y₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 5. intros k2vale.
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp.
  inversion_clear k2vale as [n k2val].
  exists (2*n+1)%Z. assumption.

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (straight_std_impl_ineq _ _ _ phase) as phasec.
  
  assert (r <> 0) as rne0. intro. lra.
  specialize (k2_odd_deriv_0 _ _ _ _ rne0 k2vale phase) as k'theq0.

  specialize (inrange_0T θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.

  specialize sign_0 as s0.
  rewrite <- k'theq0 in s0 at 1.
  assert (0 <= q < 2*PI) as qrng. split; assumption.

  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id. field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n + 1) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k) + 1) * PI) as id.
  assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2.
  rewrite mult_IZR. field.
  rewrite id2. clear id2.
  fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k) + 1) * PI)
               (θ + (IZR (2 * k) + IZR (2 * (n - k) + 1)) * PI).
  rewrite <- plus_IZR.
  assert ((2 * k + (2 * (n - k) + 1)) = 2 * n + 1)%Z as id3. omega.
  rewrite id3. clear id3. reflexivity.
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k) + 1) * PI) in k2def.
  clear slb sub.

  rewrite (k'_periodic _ _ _ k) in k'theq0.
  assert (θ + 2 * IZR k * PI = q) as qid. unfold q. field.
  rewrite qid in k'theq0. clear qid.
  
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k) + 1)%Z. assumption.

  specialize (k2k3rel _ _ _ _ (str_noton _ _ _ phase q)) as [j k2k3def].
  generalize k2def. intro k2def'.
  rewrite k2k3def in k2def.

  assert (κ₃ x₁ y₁ r q = q + IZR (2 * (n - k - j) + 1) * PI) as k3def. {
    rewrite plus_IZR. rewrite mult_IZR.
    rewrite minus_IZR.
    fieldrewrite ((2 * (IZR (n - k) - IZR j) + 1) * PI)
                 ((2 * (IZR (n - k)) + 1) * PI  - 2 * IZR j * PI).
    rewrite <- mult_IZR.
    rewrite <- plus_IZR.
    apply (Rplus_eq_reg_r (2 * IZR j * PI)).
    setr (q + IZR (2 * (n - k) + 1) * PI). assumption. }
  
  assert (exists p : Z, κ₃ x₁ y₁ r q = q + IZR p * PI) as k3defp. {
    exists (2* (n-k-j) + 1)%Z. assumption. }

  clear k2def k2defp.
    
  inversion_clear qrng as [qlb qub].
  
  assert (q <> 0) as qne0. {
    intro qeq0. symmetry in qeq0.
    
    rewrite <- qeq0 in *.
    unfold κ₃ in k3def.
    rewrite sin_0, cos_0 in k3def.
    assert (y₁ - r * (1 - 1) = y₁) as y1def. field.
    assert (x₁ - r * 0 = x₁) as x1def. field.
    rewrite y1def, x1def in k3def.
    rewrite Rplus_0_l in k3def.
    
    assert (~ ((- x₁) = 0 /\ (- y₁) = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      apply (Ropp_eq_0_compat) in xO.
      apply (Ropp_eq_0_compat) in yO.
      rewrite Ropp_involutive in xO,yO.
      rewrite xO, yO in *. lra. }
      
    unfold atan3 in k3def.
    specialize (atan2_bound _ _ notO) as [at2lb at2ub]. 
    assert (0 < atan2 (- y₁) (- x₁) + PI <= 2*PI) as at2bnd.
    split; lra. 
    rewrite k3def in at2bnd.
    inversion_clear at2bnd as [at3lb at3ub].
    
    assert (0 < 2 * (n - k - j) + 1)%Z as Zlb.
    apply lt_IZR.
    apply (Rmult_lt_reg_r (PI)). assumption. setl (0).
    assumption.
    
    assert (2 * (n - k - j) + 1 <= 2)%Z as Zub.
    apply le_IZR.
    apply (Rmult_le_reg_r PI). assumption. 
    assumption.
    
    assert ((n-k-j)%Z = 0%Z) as nmkeq0. omega.
    rewrite nmkeq0 in k3def. clear nmkeq0.
    assert ((2 * 0 + 1)%Z = 1%Z) as id. omega.
    rewrite id in k3def. clear id.
    assert (1 * PI = PI) as id.
    field.
    rewrite id in k3def. clear id.
    clear Zlb Zub at2ub at2lb y1def x1def.
    assert (atan2 (- y₁) (- x₁) = 0) as k2def2.
    apply (Rplus_eq_reg_r PI). setr PI. assumption.
    change (atan3 (y₁) (x₁) = PI) in k3def.
    specialize (atan2_0_impl  _ _ notO k2def2) as [xb yb].
    rewrite yb in *. lra. }
  
  
  inversion_clear qlb as [zltq | qeq0]; [|exfalso; apply qne0; auto].
  
  rewrite (k'_periodic _ _ _ k) in s0.
  assert (θ + 2 * IZR k * PI=q) as id.
  unfold q. field. rewrite id in s0. clear id.

  destruct (Rlt_dec q PI).
  + assert (- PI < q < PI) as qbnd. split; [lra|assumption].
    assert (2 * r - y₁ <> 0) as ntc. intro. lra.
    specialize (k_deriv_sign_quad2 _ _ _ _ qbnd rne0 phase ntc s0) as [sn | sp].
    
    ++ exfalso.
       
       assert (q < 0) as qlt0.
       apply (Rmult_lt_reg_r (/2)). lra. setr 0. setl (q/2).
       rewrite sn.
       rewrite <- atan_0.
       apply atan_increasing.
       
       apply (Rmult_lt_reg_r (2 * r - y₁)). assumption.
       setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)).
       intro. lra. setr 0.
       apply (Rplus_lt_reg_r (sqrt (x₁² - (2 * r - y₁) * y₁))).
       setl (x₁). setr (sqrt (x₁² - (2 * r - y₁) * y₁)).
       specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as zlesqrta.
       lra. lra.
       
    ++ exfalso.
       assert (q < 0) as qlt0.
       apply (Rmult_lt_reg_r (/2)). lra. setr 0. setl (q/2).
       rewrite sp.
       rewrite <- atan_0.
       apply atan_increasing.
       
       apply (Rmult_lt_reg_r (2 * r - y₁)). assumption.
       setl (- - x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)). intro. lra. setr 0.
       rewrite <- (sqrt_Rsqr (- x₁)); [| lra].
       rewrite <- Rsqr_neg.
       apply (Rplus_lt_reg_r (sqrt x₁²)).
       setr (sqrt x₁²).
       setl (sqrt (x₁² - (2 * r - y₁) * y₁)).
       apply sqrt_lt_1; [|apply Rle_0_sqr|].
       
       left.
       apply (Rplus_lt_reg_r (r²)).
       rewrite Rplus_0_l. setr (x₁² + (y₁ - r)²). assumption.
       
       apply (Rplus_lt_reg_r ((2 * r - y₁) * y₁ - x₁²)). setr ((2 * r - y₁) * y₁). setl 0.
       apply Rmult_lt_0_compat. assumption. assumption. lra.
       
  + apply Rnot_lt_le in n0. clear zltq.
    inversion_clear n0 as [PIltq |PIeqq].
    
    ++ assert (- PI < q-2*IZR 1*PI < PI) as qbnd. {
         split; lra. }
       assert (2 * r - y₁ <> 0) as ntc. intro. lra.
       assert (q-2*IZR 1*PI <>0) as qsftne0. intro. lra.
       rewrite (k'_periodic _ _ _ (-1)) in s0.
       assert (q + 2 * -1 * PI = q - 2 * 1 * PI) as id. field. rewrite id in s0. clear id.
       
       specialize (k_deriv_sign_quad2 _ _ _ _ qbnd rne0 phase ntc s0) as [sn | sp].
       +++ exfalso.
           assert (~(- (x₁ - r * sin q)  = 0 /\
                     - (y₁ - r * (1 - cos q)) = 0)) as nz.
           intro. inversion_clear H as [xaeq0 yaeq0].
           apply Ropp_eq_compat in xaeq0.
           apply Ropp_eq_compat in yaeq0.
           rewrite Ropp_0 in yaeq0, xaeq0.
           rewrite Ropp_involutive in xaeq0.
           rewrite Ropp_involutive in yaeq0.
           
           assert (x₁ = r * sin q) as xdef.
           apply (Rplus_eq_reg_r (- r * sin q)).
           setr 0. setl (x₁ - r * sin q). assumption.
           assert (y₁ = r * (1 - cos q)) as ydef.
           apply (Rplus_eq_reg_r (- r * (1-cos q))).
           setr 0. setl (y₁ - r * (1-cos q)). assumption.
           clear xaeq0 yaeq0.
           subst.
           
           assert ((r * sin q)² + (r * (1 - cos q) - r)² = r²) as r2id. {
             assert (r * (1 - cos q) - r = - r *cos q) as iid. field.
             rewrite iid. clear iid.
             rewrite Rsqr_mult.
             rewrite Rsqr_mult.
             rewrite <- Rsqr_neg.
             rewrite <- Rmult_plus_distr_l.
             rewrite sin2_cos2.
             apply Rmult_1_r. }
           rewrite r2id in phasec. clear r2id.
           lra.
           
           assert (0 < κ₃ x₁ y₁ r q <= 2*PI) as k3rng. {
             unfold κ₃, atan3.
             specialize (atan2_bound _ _ nz) as [at2lb at2ub].
             split; lra. }
           clear nz.
           rewrite k3def in k3rng.
           
           destruct (n-k-j)%Z.
           ++++ assert ((2 * 0 + 1)%Z = 1%Z) as id. omega.
                rewrite id in k3def, k3rng. clear id.
                assert (1 * PI = PI) as id. field. rewrite id in k3def, k3rng. clear id.
                inversion_clear k3rng as [k3lb k3ub].
                lra.
           
           ++++ assert (3 <= IZR (2 * Z.pos p + 1)) as postm.
                rewrite plus_IZR, mult_IZR.
                assert (1 <= IZR (Z.pos p)) as pospos.
                apply IZR_le.
                specialize (Zle_0_pos p) as zleZpos.
                assert (Z.pos p <> 0)%Z.
                discriminate. omega.
                apply (Rle_trans _ (2 * 1 + 1)). 
                lra. lra.
                inversion_clear k3rng as [k2lb k2ub].
                assert (q + 3 * PI <= 2 * PI) as contra.
                apply (Rle_trans _ (q + IZR (2 * Z.pos p + 1) * PI)).
                apply (Rplus_le_reg_r (-q)).
                apply (Rmult_le_reg_r (/PI)).
                apply Rinv_0_lt_compat. assumption.
                setl 3. intro. lra.
                setr (IZR (2 * Z.pos p + 1)). intro. lra. assumption.
                assumption. lra.
           
           ++++ assert (IZR (2 * Z.neg p + 1) <= -1 ) as negtm.
                rewrite plus_IZR, mult_IZR.
                assert (IZR (Z.neg p) <= -1) as negneg.
                rewrite <- Pos2Z.opp_pos.
                rewrite opp_IZR.
                apply Ropp_le_contravar.
                change (IZR 1 <= IZR (Z.pos p)).
                apply IZR_le.
                specialize (Zle_0_pos p) as zleZpos.
                assert (Z.pos p <> 0)%Z.
                discriminate. omega.
                apply (Rle_trans _ (2 * (- 1) + 1)).
                apply (Rplus_le_reg_r (-1)). setr (2 * -1). setl (2 * IZR (Z.neg p)).
                apply (Rmult_le_reg_r (/2)).
                apply Rinv_0_lt_compat. lra.
                setr (-1). setl (IZR (Z.neg p)). assumption.
                lra.
                inversion_clear k3rng as [k3lb k3ub].
                
                inversion_clear negtm as [ltm1 | eqm1].
           
                +++++ rewrite plus_IZR, mult_IZR in ltm1.
                assert (IZR (Z.neg p) < -1) as ltm12.
                apply (Rmult_lt_reg_r 2). lra. apply (Rplus_lt_reg_r 1).
                setl (2 * IZR (Z.neg p) + 1). setr (-1). assumption.
                specialize (lt_IZR _ _ ltm12) as ltm12Z.
                assert (Z.neg p <= -2)%Z. omega.
                assert (IZR (Z.neg p) <= -2) as negneg2.
                apply IZR_le. assumption.
                
                assert (0 < q + -3 * PI) as lb.
                apply (Rlt_le_trans _ (q + IZR (2 * Z.neg p + 1) * PI)). assumption.
                apply (Rplus_le_reg_r (-q)). apply (Rmult_le_reg_r (/PI)).
                apply Rinv_0_lt_compat. assumption. setl (IZR (2 * Z.neg p + 1)). intro. lra.
                setr (-3). intro. lra.
                rewrite plus_IZR, mult_IZR.
                apply (Rplus_le_reg_r (-1)). apply (Rmult_le_reg_r (/2)).
                apply Rinv_0_lt_compat. lra.
                setl (IZR (Z.neg p)). setr (-2). assumption.
                lra.
                
                +++++ rewrite eqm1 in *. clear eqm1.
                assert (q + - 1 * PI = q - PI) as id. field. rewrite id in *. clear id.
                assert (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁) <
                        x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) as numord. {
                  apply (Rplus_lt_reg_l (-x₁)).
                  setl (- sqrt (x₁² - (2 * r - y₁) * y₁)).
                  setr (sqrt (x₁² - (2 * r - y₁) * y₁)).
                  apply pos_opp_lt.
                  apply sqrt_lt_R0.
                  apply (Rplus_lt_reg_l (r²)). setl (r²). setr (x₁² + (y₁ - r)²). assumption. }
                
                assert ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))/ (2 * r - y₁) <
                        (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))/ (2 * r - y₁)) as argord. {
                  apply (Rmult_lt_reg_l (2 * r - y₁)). assumption.
                  setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)). assumption.
                  setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)). assumption.
                  assumption. }
                
                specialize (atan_increasing _ _ argord) as rtord.
                clear numord. 
                set (s := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *.
                set (s' := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *.
                assert (atan s < 0) as atmlb.
                rewrite <- sn. apply (Rmult_lt_reg_l 2). lra. setr 0.
                setl (q-2*PI). lra.
                assert (- PI/2 < atan s) as atmub.
                rewrite <- sn. apply (Rmult_lt_reg_l 2). lra. setl (- PI).
                setr (q-2*PI). lra.
                specialize (atan_bound ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                  as [atplb atpub]. 
                clear atpub. change (- PI/2 <atan s') in atplb.
                assert (atan s' < 0) as atpub.
                rewrite <- atan_0.
                apply atan_increasing.
                unfold s'.
                apply (Rmult_lt_reg_r (2*r- y₁)). assumption.
                setl (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)).
                intro. lra. setr 0.
                
                apply (Rplus_lt_reg_r (-x₁)). setr (-x₁).
                setl (sqrt (x₁² - (2 * r - y₁) * y₁)).
                rewrite <- Rabs_left; [|assumption].
                rewrite <- (Rabs_right (sqrt (x₁² - (2 * r - y₁) * y₁)));
                  [|apply Rle_ge; apply sqrt_pos].
                apply Rsqr_lt_abs_0.
                rewrite Rsqr_sqrt.
                apply (Rplus_lt_reg_r (- x₁² + (2 * r - y₁) * y₁)).
                setl 0. setr ((2 * r - y₁) * y₁).
                apply Rmult_lt_0_compat; assumption.
                
                left.
                apply (Rplus_lt_reg_r (r²)). setl (r²).
                unfold Rsqr at 3. setr (x₁² + (y₁ - r) * (y₁ - r)).
                assumption.
                
                set (q' := 2 * atan s' + 2 * PI) in *.
                assert (q' < 2 * PI) as zltq'. unfold q'. lra.
                assert (PI < q') as q'ltPI. unfold q'.
                apply (Rplus_lt_reg_r (-PI)).
                apply (Rmult_lt_reg_r (/2)).
                apply Rinv_0_lt_compat. lra.
                setl 0. setr (atan s' + PI/2).
                apply (Rplus_lt_reg_r (-PI/2)).
                setl (-PI/2). setr (atan s').
                lra.
                
                assert (-PI < q' - 2 * 1 * PI < PI) as q'rng. split; lra.
                assert (q' - 2 * 1 * PI <> 0) as q'ne0. intro. lra.
                assert (sign (κ' x₁ y₁ r q') = 0) as s1.
                rewrite (k'_periodic _ _ _ (- 1)%Z).
                fieldrewrite (q' + 2 * -1 * PI) (q' - 2 * 1 * PI).
                rewrite (k_deriv_sign_rng _ _ _ _ q'rng rne0 phase).
                unfold q'.
                
                fieldrewrite ((2 * atan s' + 2 * PI - 2 * 1 * PI) / 2) (atan s').
                rewrite atan_right_inv.
                assert (r * ((2 * r - y₁) * s'² - 2 * x₁ * s' + y₁) = 0) as id.
                assert ((2 * r - y₁) / r <> 0) as prodne0.
                specialize (Rdiv_lt_0_compat _ _ y1quad rgt0) as prodgt0. intro.
                rewrite H in prodgt0. lra.
                apply (Rmult_eq_reg_r ((2 * r - y₁)/r)); [|assumption]. setr 0. assumption.
                unfold s'.
                setl ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))² -
                      2 * x₁ * ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))) + y₁ * (2 * r - y₁)).
                split; assumption. unfold Rsqr.
                setl ((sqrt (x₁² - (2 * r - y₁) * y₁))² - x₁² + y₁ * (2 * r - y₁)).
                rewrite Rsqr_sqrt. field. left.
                apply (Rplus_lt_reg_l (r²)). setl (r²). setr (x₁² + (y₁ - r)²). assumption.
                rewrite id. apply sign_0.
                assert (- PI < q' + 2 * - 1 * PI <= PI) as q'rng2. inversion_clear q'rng. split; lra.
                
                assert (~ (x₁ - r * sin (q' + 2 * - 1 * PI) = 0 /\
                           y₁ - r * (1 - cos (q' + 2 * - 1 * PI)) = 0)) as noton'. {
                  intro notx1y1.
                  inversion_clear notx1y1 as [xnot ynot].
                  
                  assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
                  rewrite id in phasec. clear id.
                  rewrite <- (Rplus_0_l r²) in phasec at 1.
                  apply RIneq.Rplus_lt_reg_r in phasec.
                  assert (x₁ = r * sin (q' + 2 * - 1 * PI)) as x1def.
                  rewrite <- Rplus_0_r, <- xnot. field.
                  assert (y₁ = r * (1 - cos (q' + 2 * - 1 * PI))) as y1def.
                  rewrite <- Rplus_0_r, <- ynot. field.
                  rewrite x1def, y1def in phasec.
                  assert ((r * sin (q' + 2 * - 1 * PI))² -
                     (2 * r - r * (1 - cos (q' + 2 * - 1 * PI))) *
                     (r * (1 - cos (q' + 2 * - 1 * PI))) = 0) as id.
                  unfold Rsqr.
                  setl (r * r * (sin (q' + 2 * - 1 * PI) * sin (q' + 2 * - 1 * PI)
                                 + cos (q' + 2 * - 1 * PI) * cos (q' + 2 * - 1 * PI) - 1)).
                  change (r * r * ((sin (q' + 2 * - 1 * PI))² + (cos (q' + 2 * - 1 * PI))² - 1) = 0).
                  rewrite sin2_cos2. field.
                  rewrite id in phasec. lra. }
                rewrite (k'_periodic _ _ _ (-1)%Z) in s1.

                generalize s1. intro s1'.
                unfold sign in s1.
                
                assert (q < q') as qltq'. {
                  unfold q'.
                  apply (Rplus_lt_reg_r (- 2 * 1 * PI)).
                  apply (Rmult_lt_reg_r (/2)).
                  apply Rinv_0_lt_compat. lra. setl ((q - 2 * 1 * PI)/2). setr (atan s').
                  rewrite sn. assumption. }
                
                
                assert (~(- (x₁ - r * sin q')  = 0 /\
                          - (y₁ - r * (1 - cos q')) = 0)) as nz. {
                  intro. inversion_clear H as [xaeq0 yaeq0].
                  apply Ropp_eq_compat in xaeq0.
                  apply Ropp_eq_compat in yaeq0.
                  rewrite Ropp_0 in yaeq0, xaeq0.
                  rewrite Ropp_involutive in xaeq0.
                  rewrite Ropp_involutive in yaeq0.
                  
                  assert (x₁ = r * sin q') as xdef.
                  apply (Rplus_eq_reg_r (- r * sin q')).
                  setr 0. setl (x₁ - r * sin q'). assumption.
                  assert (y₁ = r * (1 - cos q')) as ydef.
                  apply (Rplus_eq_reg_r (- r * (1-cos q'))).
                  setr 0. setl (y₁ - r * (1-cos q')). assumption.
                  clear xaeq0 yaeq0.
                  rewrite xdef, ydef in phasec.
                  clear xdef ydef.
                  
                  assert ((r * sin q')² + (r * (1 - cos q') - r)² = r²) as r2id.
                  assert (r * (1 - cos q') - r = - r *cos q') as iid. field.
                  rewrite iid. clear iid.
                  rewrite Rsqr_mult.
                  rewrite Rsqr_mult.
                  rewrite <- Rsqr_neg.
                  rewrite <- Rmult_plus_distr_l.
                  rewrite sin2_cos2.
                  apply Rmult_1_r.
                  rewrite r2id in phasec. clear r2id.
                  lra. }
                
                rewrite <- (k'_periodic _ _ _ (- 1%Z)) in s1'.
                assert (0 < κ₃ x₁ y₁ r q' <= 2*PI) as k3rng'. {
                  unfold κ₃, atan3.
                  specialize (atan2_bound _ _ nz) as [at2lb at2ub].
                  split; lra. }
                
                destruct (total_order_T 0 (κ' x₁ y₁ r (q'+2 * -1 * PI ))).
                destruct s2. lra. symmetry in e. clear s1.
                
                rewrite (k_extrema_vals y₁ x₁ r (q' + 2* -1*PI) q'rng2 rne0 noton') in e.
                inversion_clear e as [m k2def2].
                assert (κ₂ x₁ y₁ r q' = q' + IZR (m - 2) * PI) as k2defq'.
                rewrite (k2_periodic _ _ _ (- 1)%Z).
                rewrite minus_IZR.
                rewrite Rmult_minus_distr_r.
                rewrite k2def2. field.
                
                rewrite sin_period1, cos_period1 in noton'.
                specialize (k2k3rel _ _ _ _ noton') as [t k2k3eq].
                rewrite k2k3eq in k2defq'.
                
                assert (κ₃ x₁ y₁ r q' = q' + IZR (m - 2 - 2 * t) * PI) as k3def'.
                rewrite minus_IZR at 1. rewrite mult_IZR.
                apply (Rplus_eq_reg_r (2 * IZR t * PI)).
                setr (q' + IZR (m - 2) * PI). assumption.
                
                assert (forall z, q < z < q' -> κ' x₁ y₁ r z < 0) as signs. {
                  intros. 
                  specialize (k_deriv_sign_quad_Apos_rpos
                                _ _ _ y1quad rgt0 phase (z + 2 * -1 * PI)) as signsgen.
                  inversion_clear H as [zlb zub].
                  
                  assert (- PI < z + 2 * -1 * PI < PI) as zrng.
                  split.
                  clear - pigt0 zlb zub zltq' q'ltPI qub PIltq. lra.
                  clear - pigt0 zlb zub zltq' q'ltPI qub PIltq. lra.
                  assert (z + 2 * -1 * PI <> 0) as zne0.
                  intro.
                  clear - pigt0 zlb zub zltq' q'ltPI qub PIltq H. lra.
                  
                  specialize (signsgen zrng).
                  inversion_clear signsgen as [lsg rsg].
                  
                  rewrite <- signeqm1_eqv.
                  rewrite (k'_periodic _ _ _ (-1)%Z).
                  apply lsg.
                  change (atan s < (z + 2 * -1 * PI)/ 2 < atan s').
                  split. rewrite <- sn. clear - zlb. 
                  apply (Rmult_lt_reg_l 2). lra. setl (q + 2 * - 1*PI).
                  setr (z + 2 * -1 * PI). lra.
                  apply (Rmult_lt_reg_l 2). clear. lra.
                  apply (Rplus_lt_reg_r (2*PI)). setl z. change (z < q'). assumption. }
                
                rewrite signeq0_eqv in s1', s0.
                
                set (h := κ₃ x₁ y₁ r) in *.
                
                assert (forall z, ~ (0 <= x₁ - r * sin z /\
                                     y₁ - r * (1 - cos z) = 0)) as idsc. {
                  intros. intro. inversion_clear H as [xcond ycond].
                  assert (x₁² + (y₁ - r)² <= r²) as contra.
                  assert ((- x₁)² <= (- (r * sin z))²) as x1ineq.
                  apply sqrt_le_0. apply Rle_0_sqr.
                  apply Rle_0_sqr.
                  rewrite sqrt_Rsqr; [| lra].
                  rewrite sqrt_Rsqr.
                  apply (Rplus_le_reg_l x₁). setl 0. clear - xcond. lra.
                  setl (-0).
                  apply Ropp_le_contravar.
                  apply (Rle_trans _ x₁).
                  clear - xcond. lra. left. assumption.
                  rewrite <- Rsqr_neg in x1ineq.
                  rewrite <- Rsqr_neg in x1ineq.
                  
                  assert (y₁ - r = - (r * cos z)) as ymrdef.
                  apply (Rplus_eq_reg_r (r*cos z)). setr 0. rewrite <- ycond.
                  field.
                  rewrite ymrdef.
                  rewrite <- Rsqr_neg.
                  rewrite Rsqr_mult.
                  rewrite <- Rmult_1_r.
                  rewrite <- (sin2_cos2 z).
                  rewrite Rmult_plus_distr_l.
                  rewrite Rsqr_mult in x1ineq.
                  lra. lra. }
                
                assert (derivable h) as derf. {
                  unfold derivable. intros.
                  apply ex_derive_Reals_0.
                  unfold ex_derive. simpl.
                  exists (κ' x₁ y₁ r x).
                  apply (k_is_derive_atan3 _ _ _ _ rne0 (idsc x)). }
                assert (forall z:R, is_derive (κ₃ x₁ y₁ r) z (κ' x₁ y₁ r z)) as k3deriv. {
                  intro.
                  apply (k_is_derive_atan3 _ _ _ _ rne0 (idsc z)). }
                
                change (forall z : R, is_derive h z (κ' x₁ y₁ r z)) in k3deriv.
                assert (forall z : R, q < z < q' -> derive_pt h z (derf z) < 0) as cond. {
                  intros.
                  specialize (k3deriv z).
                  rewrite Derive_Reals.
                  rewrite (is_derive_unique _ _ _ k3deriv).
                  apply signs. assumption. }
                
                specialize (derive_decreasing_interv q q' h derf qltq' cond) as hdecr. {
                  assert (q <= q  <= q') as qpos. clear - qltq'. split; lra.
                  assert (q <= q' <= q') as q'pos. clear - qltq'. split; lra.
                  specialize (hdecr _ _ qpos q'pos qltq').
                  
                  clear qpos q'pos cond k3deriv derf idsc k2k3eq k2defq'
                        k2def2 nz k2k3def k2def' k2vale k2valp.
                  
                  
                  destruct (m - 2 - 2 * t)%Z.
                  assert (h q < h q') as k3order.
                  rewrite k3def', k3def. setr q'. clear - qltq' pigt0.
                  lra.
                  clear - hdecr k3order. lra.
                  
                  clear - q'ltPI k3def' k3rng'.
                  rewrite k3def' in k3rng'.
                  inversion_clear k3rng' as [k3rlb k3rub].
                  
                  assert (1 <= IZR (Z.pos p0)) as ord.
                  apply IZR_le.
                  specialize (Zgt_pos_0 p0) as nonz. omega.
                  apply (Rmult_le_compat_r PI) in ord.
                  apply (Rplus_le_compat_l q') in ord.
                  lra. lra.
                  
                  assert (IZR (Z.neg p0) <= -1 ) as negtm.
                  rewrite <- Pos2Z.opp_pos.
                  rewrite opp_IZR.
                  apply Ropp_le_contravar.
                  change (IZR 1 <= IZR (Z.pos p0)).
                  apply IZR_le.
                  specialize (Zle_0_pos p0) as zleZpos.
                  assert (Z.pos p0 <> 0)%Z.
                  discriminate. omega.
                  
                  inversion_clear negtm as [ltm1 | eqm1].
                  specialize (lt_IZR _ _ ltm1) as ltm12Z.
                  assert (Z.neg p0 <= -2)%Z. omega.
                  assert (IZR (Z.neg p0) <= -2) as negneg2.
                  apply IZR_le. assumption.
                  inversion_clear k3rng' as [k3lb' k3ub'].
                  clear - k3lb' negneg2 k3def' zltq' pigt0.
                  rewrite k3def' in k3lb'.
                  apply (Rmult_le_compat_r PI) in negneg2.
                  apply (Rplus_le_compat_l q') in negneg2.
                  lra. lra.
                  
                  rewrite eqm1 in *. clear eqm1.
                  rewrite k3def', k3def in hdecr.
                  clear - hdecr qltq'.
                  lra. }
                
                clear - s1. lra.
                
       +++ exists (-k + 1)%Z.
           rewrite <- sp.
           fieldrewrite (2*((q - 2 * 1 * PI)/2)) (q - 2 * 1 * PI).
           rewrite mult_IZR, plus_IZR, opp_IZR.
           apply (Rplus_eq_reg_r (- 2 * (- IZR k + 1) * PI)).
           setr (q - 2 * 1 * PI). unfold q. field.
       
    (* q = PI case *)
    ++ exfalso.
       rewrite <- PIeqq in *.
       clear PIeqq.
       unfold κ₃, atan3 in k3def.
       clear qub qne0.
       assert (atan2 (- (y₁ - 2 * r)) (- x₁) =
               IZR (2 * (n - k - j) + 1) * PI) as a2def. {
         fieldrewrite (y₁ - 2 * r) (y₁ - r* ( 1 - - 1)).  rewrite <- cos_PI.
         fieldrewrite (- x₁) (- (x₁ - r * 0)). rewrite <- sin_PI.
         apply (Rplus_eq_reg_r PI).
         rewrite (Rplus_comm (IZR (2 * (n - k - j) + 1) * PI) PI).
         assumption. }
       clear k3def k3defp.
       
       assert (~ ((- x₁) = 0 /\ (- (y₁ - 2 * r)) = 0)) as cond. {
       intro. inversion_clear H as [ls rs]. clear - ls x1quad. lra. }
       
       specialize (atan2_bound _ _ cond) as [at2lb at2ub].
       set (w := atan2 (- (y₁ - 2 * r)) (- x₁) ) in *.
       clear k2k3def k2def'.
       
       destruct (n - k - j)%Z.
       
       +++ assert (IZR (2 * 0 + 1) * PI = PI) as id.
           rewrite plus_IZR, mult_IZR. field. rewrite id in *. clear id.
           
           specialize (atan2_PI_impl _ _ cond a2def) as [xlt0 contra].
           clear - xlt0 x1quad. lra.
       
       +++ assert (3 <= IZR (2 * Z.pos p + 1)) as postm.
           rewrite plus_IZR, mult_IZR.
           assert (1 <= IZR (Z.pos p)) as pospos.
           apply IZR_le.
           specialize (Zle_0_pos p) as zleZpos.
           assert (Z.pos p <> 0)%Z.
           discriminate. omega.
           apply (Rle_trans _ (2 * 1 + 1)). 
           lra. lra.
           
           apply (Rmult_le_compat_r PI) in postm; [|lra].
           rewrite <- a2def in postm.
           clear - at2ub postm pigt0. lra.
           
       +++ assert (IZR (2 * Z.neg p + 1) <= -1 ) as negtm.
           rewrite plus_IZR, mult_IZR.
           assert (IZR (Z.neg p) <= -1) as negneg.
           rewrite <- Pos2Z.opp_pos.
           rewrite opp_IZR.
           apply Ropp_le_contravar.
           change (IZR 1 <= IZR (Z.pos p)).
           apply IZR_le.
           specialize (Zle_0_pos p) as zleZpos.
           assert (Z.pos p <> 0)%Z.
           discriminate. omega.
           apply (Rle_trans _ (2 * (- 1) + 1)).
           apply (Rplus_le_reg_r (-1)). setr (2 * -1).
           setl (2 * IZR (Z.neg p)).
           apply (Rmult_le_reg_r (/2)).
           apply Rinv_0_lt_compat. lra.
           setr (-1). setl (IZR (Z.neg p)). assumption.
           lra.
           
           apply (Rmult_le_compat_r PI) in negtm; [|lra].
           rewrite <- a2def in negtm.
           clear - at2lb negtm pigt0. lra.
Qed.



Lemma negroot_even_Q2_rpos :
  forall x₁ y₁ r θ
         (x1quad :  x₁ < 0)
         (y1quad : 0 < 2*r - y₁)
         (y1pos : 0 < y₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 5. intros k2vale.

  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (straight_std_impl_ineq _ _ _ phase) as phasec.
  
  assert (r <> 0) as rne0. {
    intro. lra. }

  specialize (k2_even_deriv_0 _ _ _ _ rne0 k2vale phase) as k'theq0.
  
  specialize (inrange_0T θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.

  specialize sign_0 as s0.
  rewrite <- k'theq0 in s0 at 1.
  assert (0 <= q < 2*PI) as qrng. split; assumption.

  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id. field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k)) * PI) as id.
  assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2.
  rewrite mult_IZR. field.
  rewrite id2. clear id2.
  fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k)) * PI)
               (θ + (IZR (2 * k) + IZR (2 * (n - k))) * PI).
  rewrite <- plus_IZR.
  assert ((2 * k + (2 * (n - k))) = 2 * n)%Z as id3. omega.
  rewrite id3. clear id3. reflexivity.
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k)) * PI) in k2def.
  clear slb sub.

  rewrite (k'_periodic _ _ _ k) in k'theq0.
  assert (θ + 2 * IZR k * PI = q) as qid. unfold q. field.
  rewrite qid in k'theq0. clear qid.
  
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k))%Z. assumption.

  specialize (k2k3rel _ _ _ _ (str_noton _ _ _ phase q)) as [j k2k3def].
  generalize k2def. intro k2def'.
  rewrite k2k3def in k2def.

  assert (κ₃ x₁ y₁ r q = q + IZR (2 * (n - k - j)) * PI) as k3def. {
    rewrite mult_IZR.
    rewrite minus_IZR.
    fieldrewrite ((2 * (IZR (n - k) - IZR j)) * PI)
                 ((2 * (IZR (n - k))) * PI  - 2 * IZR j * PI).
    rewrite <- mult_IZR.
    apply (Rplus_eq_reg_r (2 * IZR j * PI)).
    setr (q + IZR (2 * (n - k)) * PI). assumption. }
  
  assert (exists p : Z, κ₃ x₁ y₁ r q = q + IZR p * PI) as k3defp. {
    exists (2* (n-k-j))%Z. assumption. }

  clear k2def k2defp.
    
  inversion_clear qrng as [qlb qub].
  
  assert (q <> 0) as qne0. {
    intro qeq0. symmetry in qeq0.
    
    rewrite <- qeq0 in *.
    unfold κ₃ in k3def.
    rewrite sin_0, cos_0 in k3def.
    assert (y₁ - r * (1 - 1) = y₁) as y1def. field.
    assert (x₁ - r * 0 = x₁) as x1def. field.
    rewrite y1def, x1def in k3def.
    rewrite Rplus_0_l in k3def.
    
    assert (~ ((- x₁) = 0 /\ (- y₁) = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      apply (Ropp_eq_0_compat) in xO.
      apply (Ropp_eq_0_compat) in yO.
      rewrite Ropp_involutive in xO,yO.
      rewrite xO, yO in *. lra. }
      
    unfold atan3 in k3def.
    specialize (atan2_bound _ _ notO) as [at2lb at2ub]. 
    assert (0 < atan2 (- y₁) (- x₁) + PI <= 2*PI) as at2bnd.
    split; lra. 
    rewrite k3def in at2bnd.
    inversion_clear at2bnd as [at3lb at3ub].
    
    assert (0 < 2 * (n - k - j))%Z as Zlb.
    apply lt_IZR.
    apply (Rmult_lt_reg_r (PI)). assumption. setl (0).
    assumption.
    
    assert (2 * (n - k - j) <= 2)%Z as Zub.
    apply le_IZR.
    apply (Rmult_le_reg_r PI). assumption. 
    assumption.
    
    assert ((n-k-j)%Z = 1%Z) as nmkeq0. lia.
    rewrite nmkeq0 in k3def. clear nmkeq0.
    assert ((2 * 1)%Z = 2%Z) as id. lia.
    rewrite id in k3def. clear id.
    (*assert (1 * PI = PI) as id.
    field. rewrite id in k3def. clear id. *)
    clear Zlb Zub at2ub at2lb y1def x1def.
    assert (atan2 (- y₁) (- x₁) = PI) as k2def2.
    apply (Rplus_eq_reg_r PI). setr (2*PI). assumption.
    change (atan3 (y₁) (x₁) = 2*PI) in k3def.
    specialize (atan2_PI_impl  _ _ notO k2def2) as [xb yb].
    rewrite yb in *. lra. }
  
  inversion_clear qlb as [zltq | qeq0]; [|exfalso; apply qne0; auto].
  
  rewrite (k'_periodic _ _ _ k) in s0.
  assert (θ + 2 * IZR k * PI=q) as id.
  unfold q. field. rewrite id in s0. clear id.

  destruct (Rlt_dec q PI).
  + assert (- PI < q < PI) as qbnd. split; [lra|assumption].
    assert (2 * r - y₁ <> 0) as ntc. intro. lra.
    specialize (k_deriv_sign_quad2 _ _ _ _ qbnd rne0 phase ntc s0) as [sn | sp].
    
    ++ (* exfalso. ! *)
       unfold q in sn.
       exists (-k)%Z.
       rewrite <- sn, mult_IZR, opp_IZR.
       field.

    ++ exfalso.
       assert (q < 0) as qlt0. {
         apply (Rmult_lt_reg_r (/2)). lra. setr 0. setl (q/2).
         rewrite sp.
         rewrite <- atan_0.
         apply atan_increasing.
       
         apply (Rmult_lt_reg_r (2 * r - y₁)). assumption.
         setl (- - x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)). intro. lra. setr 0.
         rewrite <- (sqrt_Rsqr (- x₁)); [| lra].
         rewrite <- Rsqr_neg.
         apply (Rplus_lt_reg_r (sqrt x₁²)).
         setr (sqrt x₁²).
         setl (sqrt (x₁² - (2 * r - y₁) * y₁)).
         apply sqrt_lt_1; [|apply Rle_0_sqr|].
       
         left.
         apply (Rplus_lt_reg_r (r²)).
         rewrite Rplus_0_l. setr (x₁² + (y₁ - r)²). assumption.
       
         apply (Rplus_lt_reg_r ((2 * r - y₁) * y₁ - x₁²)).
         setr ((2 * r - y₁) * y₁). setl 0.
         apply Rmult_lt_0_compat. assumption. assumption. }
       lra.
       
  + apply Rnot_lt_le in n0. clear zltq.
    inversion_clear n0 as [PIltq |PIeqq].
    
    ++ assert (- PI < q-2*IZR 1*PI < PI) as qbnd. {
         split; lra. }
       assert (2 * r - y₁ <> 0) as ntc. intro. lra.
       assert (q-2*IZR 1*PI <>0) as qsftne0. intro. lra.
       rewrite (k'_periodic _ _ _ (-1)) in s0.
       assert (q + 2 * -1 * PI = q - 2 * 1 * PI) as id. field. rewrite id in s0. clear id.
       
       specialize (k_deriv_sign_quad2 _ _ _ _ qbnd rne0 phase ntc s0) as [sn | sp].
       +++ exists (1 - k)%Z.
           rewrite <- sn.
           unfold q.
           rewrite mult_IZR, minus_IZR.
           field.

       +++ exfalso.
           assert (~(- (x₁ - r * sin q)  = 0 /\
                     - (y₁ - r * (1 - cos q)) = 0)) as nz. {
             intro. inversion_clear H as [xaeq0 yaeq0].
             apply Ropp_eq_compat in xaeq0.
             apply Ropp_eq_compat in yaeq0.
             rewrite Ropp_0 in yaeq0, xaeq0.
             rewrite Ropp_involutive in xaeq0.
             rewrite Ropp_involutive in yaeq0.
             
             assert (x₁ = r * sin q) as xdef.
             apply (Rplus_eq_reg_r (- r * sin q)).
             setr 0. setl (x₁ - r * sin q). assumption.
             assert (y₁ = r * (1 - cos q)) as ydef.
             apply (Rplus_eq_reg_r (- r * (1-cos q))).
             setr 0. setl (y₁ - r * (1-cos q)). assumption.
             clear xaeq0 yaeq0.
             subst.
             
             assert ((r * sin q)² + (r * (1 - cos q) - r)² = r²) as r2id. {
               assert (r * (1 - cos q) - r = - r *cos q) as iid. field.
               rewrite iid. clear iid.
               rewrite Rsqr_mult.
               rewrite Rsqr_mult.
               rewrite <- Rsqr_neg.
               rewrite <- Rmult_plus_distr_l.
               rewrite sin2_cos2.
               apply Rmult_1_r. }
             rewrite r2id in phasec. clear r2id.
             lra. }
             
           assert (0 < κ₃ x₁ y₁ r q <= 2*PI) as k3rng. {
             unfold κ₃, atan3.
             specialize (atan2_bound _ _ nz) as [at2lb at2ub].
             split; lra. }
           clear nz.
           rewrite k3def in k3rng.
             
           case_eq (n-k-j)%Z.
           ++++ intros nmkmj.
                assert (j = n - k)%Z as jd. lia.
                assert ((2 * 0)%Z = 0%Z) as id. lia.
                rewrite nmkmj, id in k3def, k3rng. clear id.
                autorewrite with null in k3def, k3rng.
                rewrite <- jd in *.
                inversion_clear k3rng as [k3lb k3ub].
                clear nmkmj.
                rewrite mult_IZR in k2def'.
                
                assert (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁) <
                        x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) as numord. {
                  apply (Rplus_lt_reg_l (-x₁)).
                  setl (- sqrt (x₁² - (2 * r - y₁) * y₁)).
                  setr (sqrt (x₁² - (2 * r - y₁) * y₁)).
                  apply pos_opp_lt.
                  apply sqrt_lt_R0.
                  apply (Rplus_lt_reg_l (r²)). setl (r²). setr (x₁² + (y₁ - r)²). assumption. }
                
                assert ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))/ (2 * r - y₁) <
                        (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))/ (2 * r - y₁)) as argord. {
                  apply (Rmult_lt_reg_l (2 * r - y₁)). assumption.
                  setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)). assumption.
                  setr (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)). assumption.
                  assumption. }
                
                specialize (atan_increasing _ _ argord) as rtord.
                clear numord. 
                set (s' := ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *.
                set (s := ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))) in *.
                assert (atan s < 0) as atmlb.
                rewrite <- sp. apply (Rmult_lt_reg_l 2). lra. setr 0.
                setl (q-2*PI). lra.
                assert (- PI/2 < atan s) as atmub.
                rewrite <- sp. apply (Rmult_lt_reg_l 2). lra. setl (- PI).
                setr (q-2*PI). lra.
                specialize (atan_bound ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)))
                  as [atplb atpub]. 
                clear atpub. change (- PI / 2 < atan s') in atplb.
                assert (atan s' < 0) as atpub.
                rewrite <- atan_0.
                apply atan_increasing.
                unfold s'.
                apply (Rmult_lt_reg_r (2*r- y₁)). assumption.
                setl (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)).
                intro. lra. setr 0.

                apply Ropp_lt_cancel.
                setl 0.
                setr (- x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)).
                specialize ( sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sqrtgt0.
                lra.
                
                set (q' := 2 * atan s' + 2 * PI) in *.
                assert (q' < 2 * PI) as zltq'. unfold q'. lra.
                assert (PI < q') as q'ltPI. unfold q'.
                apply (Rplus_lt_reg_r (-PI)).
                apply (Rmult_lt_reg_r (/2)).
                apply Rinv_0_lt_compat. lra.
                setl 0. setr (atan s' + PI/2).
                apply (Rplus_lt_reg_r (-PI/2)).
                setl (-PI/2). setr (atan s').
                lra.
                
                assert (-PI < q' - 2 * 1 * PI < PI) as q'rng. split; lra.
                assert (q' - 2 * 1 * PI <> 0) as q'ne0. intro. lra.
                assert (sign (κ' x₁ y₁ r q') = 0) as s1.
                rewrite (k'_periodic _ _ _ (- 1)%Z).
                fieldrewrite (q' + 2 * -1 * PI) (q' - 2 * 1 * PI).
                rewrite (k_deriv_sign_rng _ _ _ _ q'rng rne0 phase).
                unfold q'.
                
                fieldrewrite ((2 * atan s' + 2 * PI - 2 * 1 * PI) / 2) (atan s').
                rewrite atan_right_inv.
                assert (r * ((2 * r - y₁) * s'² - 2 * x₁ * s' + y₁) = 0) as id.
                assert ((2 * r - y₁) / r <> 0) as prodne0.
                specialize (Rdiv_lt_0_compat _ _ y1quad rgt0) as prodgt0. intro.
                rewrite H in prodgt0. lra.
                apply (Rmult_eq_reg_r ((2 * r - y₁)/r)); [|assumption]. setr 0. assumption.
                unfold s'.
                setl ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))² -
                      2 * x₁ * ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))) + y₁ * (2 * r - y₁)).
                split; assumption. unfold Rsqr.
                setl ((sqrt (x₁² - (2 * r - y₁) * y₁))² - x₁² + y₁ * (2 * r - y₁)).
                rewrite Rsqr_sqrt. field. left.
                apply (Rplus_lt_reg_l (r²)). setl (r²). setr (x₁² + (y₁ - r)²). assumption.
                rewrite id. apply sign_0.
                assert (- PI < q' + 2 * - 1 * PI <= PI) as q'rng2. inversion_clear q'rng. split; lra.
                
                assert (~ (x₁ - r * sin (q' + 2 * - 1 * PI) = 0 /\
                           y₁ - r * (1 - cos (q' + 2 * - 1 * PI)) = 0)) as noton'. {
                  intro notx1y1.
                  inversion_clear notx1y1 as [xnot ynot].
                  
                  assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
                  rewrite id in phasec. clear id.
                  rewrite <- (Rplus_0_l r²) in phasec at 1.
                  apply RIneq.Rplus_lt_reg_r in phasec.
                  assert (x₁ = r * sin (q' + 2 * - 1 * PI)) as x1def.
                  rewrite <- Rplus_0_r, <- xnot. field.
                  assert (y₁ = r * (1 - cos (q' + 2 * - 1 * PI))) as y1def.
                  rewrite <- Rplus_0_r, <- ynot. field.
                  rewrite x1def, y1def in phasec.
                  assert ((r * sin (q' + 2 * - 1 * PI))² -
                     (2 * r - r * (1 - cos (q' + 2 * - 1 * PI))) *
                     (r * (1 - cos (q' + 2 * - 1 * PI))) = 0) as id.
                  unfold Rsqr.
                  setl (r * r * (sin (q' + 2 * - 1 * PI) * sin (q' + 2 * - 1 * PI)
                                 + cos (q' + 2 * - 1 * PI) * cos (q' + 2 * - 1 * PI) - 1)).
                  change (r * r * ((sin (q' + 2 * - 1 * PI))² + (cos (q' + 2 * - 1 * PI))² - 1) = 0).
                  rewrite sin2_cos2. field.
                  rewrite id in phasec. lra. }
                rewrite (k'_periodic _ _ _ (-1)%Z) in s1.

                generalize s1. intro s1'.
                unfold sign in s1.
                
                assert (q' < q) as qltq'. {
                  unfold q'.
                  apply (Rplus_lt_reg_r (- 2 * 1 * PI)).
                  apply (Rmult_lt_reg_r (/2)).
                  apply Rinv_0_lt_compat. lra.
                  setr ((q - 2 * 1 * PI)/2). setl (atan s').
                  rewrite sp. assumption. }
                
                
                assert (~(- (x₁ - r * sin q') = 0 /\
                          - (y₁ - r * (1 - cos q')) = 0)) as nz. {
                  intro. inversion_clear H as [xaeq0 yaeq0].
                  apply Ropp_eq_compat in xaeq0.
                  apply Ropp_eq_compat in yaeq0.
                  rewrite Ropp_0 in yaeq0, xaeq0.
                  rewrite Ropp_involutive in xaeq0.
                  rewrite Ropp_involutive in yaeq0.
                  
                  assert (x₁ = r * sin q') as xdef.
                  apply (Rplus_eq_reg_r (- r * sin q')).
                  setr 0. setl (x₁ - r * sin q'). assumption.
                  assert (y₁ = r * (1 - cos q')) as ydef.
                  apply (Rplus_eq_reg_r (- r * (1-cos q'))).
                  setr 0. setl (y₁ - r * (1-cos q')). assumption.
                  clear xaeq0 yaeq0.
                  rewrite xdef, ydef in phasec.
                  clear xdef ydef.
                  
                  assert ((r * sin q')² + (r * (1 - cos q') - r)² = r²) as r2id.
                  assert (r * (1 - cos q') - r = - r *cos q') as iid. field.
                  rewrite iid. clear iid.
                  rewrite Rsqr_mult.
                  rewrite Rsqr_mult.
                  rewrite <- Rsqr_neg.
                  rewrite <- Rmult_plus_distr_l.
                  rewrite sin2_cos2.
                  apply Rmult_1_r.
                  rewrite r2id in phasec. clear r2id.
                  lra. }
                
                rewrite <- (k'_periodic _ _ _ (- 1%Z)) in s1'.
                assert (0 < κ₃ x₁ y₁ r q' <= 2*PI) as k3rng'. {
                  unfold κ₃, atan3.
                  specialize (atan2_bound _ _ nz) as [at2lb at2ub].
                  split; lra. }
                
                destruct (total_order_T 0 (κ' x₁ y₁ r (q'+2 * -1 * PI ))).
                destruct s2. lra. symmetry in e. clear s1.
                
                rewrite (k_extrema_vals y₁ x₁ r (q' + 2* -1*PI) q'rng2 rne0 noton') in e.
                inversion_clear e as [m k2def2].
                assert (κ₂ x₁ y₁ r q' = q' + IZR (m - 2) * PI) as k2defq'.
                rewrite (k2_periodic _ _ _ (- 1)%Z).
                rewrite minus_IZR.
                rewrite Rmult_minus_distr_r.
                rewrite k2def2. field.
                
                rewrite sin_period1, cos_period1 in noton'.
                specialize (k2k3rel _ _ _ _ noton') as [t k2k3eq].
                rewrite k2k3eq in k2defq'.
                
                assert (κ₃ x₁ y₁ r q' = q' + IZR (m - 2 - 2 * t) * PI) as k3def'. {
                rewrite minus_IZR at 1. rewrite mult_IZR.
                apply (Rplus_eq_reg_r (2 * IZR t * PI)).
                setr (q' + IZR (m - 2) * PI). assumption. }
                
                assert (forall z, q' < z < q -> κ' x₁ y₁ r z < 0) as signs. {
                  intros. 
                  specialize (k_deriv_sign_quad_Apos_rpos
                                _ _ _ y1quad rgt0 phase (z + 2 * -1 * PI)) as signsgen.
                  inversion_clear H as [zlb zub].
                  
                  assert (- PI < z + 2 * -1 * PI < PI) as zrng.
                  split.
                  clear - pigt0 zlb zub zltq' q'ltPI qub PIltq. lra.
                  clear - pigt0 zlb zub zltq' q'ltPI qub PIltq. lra.
                  assert (z + 2 * -1 * PI <> 0) as zne0. {
                    intro.
                    clear - pigt0 zlb zub zltq' q'ltPI qub PIltq H. lra. }
                  
                  specialize (signsgen zrng).
                  inversion_clear signsgen as [lsg rsg].
                  clear rsg.
                  
                  rewrite <- signeqm1_eqv.
                  rewrite (k'_periodic _ _ _ (-1)%Z).
                  apply lsg.
                  change (atan s' < (z + 2 * -1 * PI)/ 2 < atan s).
                  split.
                  apply (Rmult_lt_reg_l 2). clear. lra.
                  apply (Rplus_lt_reg_r (2*PI)). setr z. change (q' < z ). assumption.
                  rewrite <- sp. clear - zub. 
                  apply (Rmult_lt_reg_l 2). lra.
                  setr (q + 2 * - 1*PI).
                  setl (z + 2 * -1 * PI). lra. }
                
                rewrite signeq0_eqv in s1', s0.
                
                set (h := κ₃ x₁ y₁ r) in *.
                
                assert (forall z, ~ (0 <= x₁ - r * sin z /\
                                     y₁ - r * (1 - cos z) = 0)) as idsc. {
                  intros. intro. inversion_clear H as [xcond ycond].
                  assert (x₁² + (y₁ - r)² <= r²) as contra.
                  assert ((- x₁)² <= (- (r * sin z))²) as x1ineq.
                  apply sqrt_le_0. apply Rle_0_sqr.
                  apply Rle_0_sqr.
                  rewrite sqrt_Rsqr; [| lra].
                  rewrite sqrt_Rsqr.
                  apply (Rplus_le_reg_l x₁). setl 0. clear - xcond. lra.
                  setl (-0).
                  apply Ropp_le_contravar.
                  apply (Rle_trans _ x₁).
                  clear - xcond. lra. left. assumption.
                  rewrite <- Rsqr_neg in x1ineq.
                  rewrite <- Rsqr_neg in x1ineq.
                  
                  assert (y₁ - r = - (r * cos z)) as ymrdef.
                  apply (Rplus_eq_reg_r (r*cos z)). setr 0. rewrite <- ycond.
                  field.
                  rewrite ymrdef.
                  rewrite <- Rsqr_neg.
                  rewrite Rsqr_mult.
                  rewrite <- Rmult_1_r.
                  rewrite <- (sin2_cos2 z).
                  rewrite Rmult_plus_distr_l.
                  rewrite Rsqr_mult in x1ineq.
                  lra. lra. }
                
                assert (derivable h) as derf. {
                  unfold derivable. intros.
                  apply ex_derive_Reals_0.
                  unfold ex_derive. simpl.
                  exists (κ' x₁ y₁ r x).
                  apply (k_is_derive_atan3 _ _ _ _ rne0 (idsc x)). }
                assert (forall z:R, is_derive (κ₃ x₁ y₁ r) z (κ' x₁ y₁ r z)) as k3deriv. {
                  intro.
                  apply (k_is_derive_atan3 _ _ _ _ rne0 (idsc z)). }
                
                change (forall z : R, is_derive h z (κ' x₁ y₁ r z)) in k3deriv.
                assert (forall z : R, q' < z < q -> derive_pt h z (derf z) < 0) as cond. {
                  intros.
                  specialize (k3deriv z).
                  rewrite Derive_Reals.
                  rewrite (is_derive_unique _ _ _ k3deriv).
                  apply signs. assumption. }
                
                specialize (derive_decreasing_interv q' q h derf qltq' cond) as hdecr. {
                  assert (q' <= q' <= q) as qpos. clear - qltq'. split; lra.
                  assert (q' <= q <= q) as q'pos. clear - qltq'. split; lra.
                  specialize (hdecr _ _ qpos q'pos qltq').
                  
                  clear qpos q'pos cond k3deriv derf idsc k2k3eq k2defq'
                        k2def2 nz k2k3def k2def' k2vale k2valp.
                  
                  destruct (m - 2 - 2 * t)%Z.

                  - assert (h q' < h q) as k3order.
                    rewrite k3def', k3def. setl q'. clear - qltq' pigt0.
                    lra.
                    clear - hdecr k3order. lra.
                  -  clear - q'ltPI k3def' k3rng'.
                     rewrite k3def' in k3rng'.
                     inversion_clear k3rng' as [k3rlb k3rub].

                     specialize (IZRposge1 p) as ord.
                     apply (Rmult_le_compat_r PI) in ord.
                     apply (Rplus_le_compat_l q') in ord.
                     lra. lra.
                  - specialize (IZRneglen1 p) as negtm.

                    inversion_clear negtm as [ltm1 | eqm1].
                    specialize (lt_IZR _ _ ltm1) as ltm12Z.
                    assert (Z.neg p <= -2)%Z. omega.
                    assert (IZR (Z.neg p) <= -2) as negneg2.
                    apply IZR_le. assumption.
                    inversion_clear k3rng' as [k3lb' k3ub'].

                    rewrite k3def' in k3lb'.
                    apply (Rmult_le_compat_r PI) in negneg2.
                    apply (Rplus_le_compat_l q') in negneg2.
                    lra. lra.
                  
                    rewrite eqm1 in *. clear eqm1.
                    rewrite k3def', k3def in hdecr.

                    lra. }
                
                clear - s1. lra.

           ++++ intros p nkjpos.
                assert (2 <= IZR (2 * Z.pos p)) as postm.
                rewrite mult_IZR.
                specialize (IZRposge1 p) as pospos.
                rewrite nkjpos in *.

                apply (Rle_trans _ (2 * 1)). 
                lra. lra.
                inversion_clear k3rng as [k2lb k2ub].
                rewrite nkjpos in *.
                assert (q + 2 * PI <= 2 * PI) as contra. {
                  apply (Rle_trans _ (q + IZR (2 * Z.pos p) * PI)).
                  apply (Rplus_le_reg_r (-q)).
                  apply (Rmult_le_reg_r (/PI)).
                  apply Rinv_0_lt_compat. assumption.
                  setl 2. intro. lra.
                  setr (IZR (2 * Z.pos p)). intro. lra. assumption.
                  assumption. }
                lra.
           
           ++++ intros p nkjd.
                assert (IZR (2 * Z.neg p) <= -2 ) as negtm. {
                  rewrite mult_IZR.
                  specialize (IZRneglen1 p) as negneg.
                  lra. }
                inversion_clear k3rng as [k3lb k3ub].
                
                inversion_clear negtm as [ltm1 | eqm1].
           
                +++++ rewrite mult_IZR in ltm1.
                assert (IZR (Z.neg p) < -1) as ltm12. {
                  apply (Rmult_lt_reg_r 2). lra.
                  setl (2 * IZR (Z.neg p)).
                  setr (-2). assumption.  }
                specialize (lt_IZR _ _ ltm12) as ltm12Z.
                assert (Z.neg p <= -2)%Z. omega.
                assert (IZR (Z.neg p) <= -2) as negneg2.
                apply IZR_le. assumption.

                rewrite nkjd in *.
                assert (0 < q + -2 * PI) as lb. {
                apply (Rlt_le_trans _ (q + IZR (2 * Z.neg p) * PI)).
                assumption.
                apply (Rplus_le_reg_r (-q)). apply (Rmult_le_reg_r (/PI)).
                apply Rinv_0_lt_compat. assumption.
                setl (IZR (2 * Z.neg p)). intro. lra.
                setr (-2). intro. lra.
                rewrite mult_IZR.
                apply (Rmult_le_reg_r (/2)).
                apply Rinv_0_lt_compat. lra.
                setl (IZR (Z.neg p)). setr (-1).
                left.
                assumption. }
                lra.
                
                +++++ 
                rewrite nkjd in *.
                rewrite eqm1 in *.
                clear eqm1 nkjd.
                lra.
                
    (* q = PI case *)
    ++ exfalso.
       rewrite <- PIeqq in *.
       clear PIeqq.
       unfold κ₃, atan3 in k3def.
       clear qub qne0.
       assert (atan2 (- (y₁ - 2 * r)) (- x₁) =
               IZR (2 * (n - k - j)) * PI) as a2def. {
         fieldrewrite (y₁ - 2 * r) (y₁ - r* ( 1 - - 1)).  rewrite <- cos_PI.
         fieldrewrite (- x₁) (- (x₁ - r * 0)). rewrite <- sin_PI.
         apply (Rplus_eq_reg_r PI).
         rewrite (Rplus_comm (IZR (2 * (n - k - j)) * PI) PI).
         assumption. }
       clear k3def k3defp.
       
       assert (~ ((- x₁) = 0 /\ (- (y₁ - 2 * r)) = 0)) as cond. {
       intro. inversion_clear H as [ls rs]. clear - ls x1quad. lra. }
       
       specialize (atan2_bound _ _ cond) as [at2lb at2ub].
       set (w := atan2 (- (y₁ - 2 * r)) (- x₁) ) in *.
       clear k2k3def k2def'.
       
       destruct (n - k - j)%Z.
       
       +++ autorewrite with null in *.
           
           specialize (atan2_0_impl _ _ cond a2def) as [xlt0 contra].
           rewrite Ropp_minus_distr in contra.
           rewrite contra in y1quad.
           lra.
       
       +++ assert (2 <= IZR (2 * Z.pos p)) as postm. {
             rewrite mult_IZR.
             specialize (IZRposge1 p) as pospos.
             apply (Rle_trans _ (2 * 1)). 
             lra.
             lra. }
           
           apply (Rmult_le_compat_r PI) in postm; [|lra].
           rewrite <- a2def in postm.
           clear - at2ub postm pigt0. lra.
           
       +++ assert (IZR (2 * Z.neg p) <= -2) as negtm. {
             rewrite mult_IZR.
             specialize (IZRneglen1 p) as negneg.

             apply (Rle_trans _ (2 * (- 1))).
             apply (Rmult_le_reg_r (/2)).
             apply Rinv_0_lt_compat. lra.
             setr (-1). setl (IZR (Z.neg p)).
             assumption.
             lra. }
           
             apply (Rmult_le_compat_r PI) in negtm; [|lra].
             rewrite <- a2def in negtm.
             clear - at2lb negtm pigt0. lra.
Qed.

Lemma posroot_odd_Q1Q2top_rpos :
  forall x₁ y₁ r θ
         (y1quad : 2*r - y₁ < 0)
         (y1pos : 0 < y₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 4. intros k2vale.
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n+1)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. {
    split. setl (- (2*PI)/2). assumption.
    setr (2*PI/2). assumption. }

  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id. field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n + 1) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k) + 1) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2.
    rewrite mult_IZR. field.
    rewrite id2. clear id2.
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k) + 1) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k) + 1)) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k) + 1)) = 2 * n + 1)%Z as id3. omega.
    rewrite id3. clear id3. reflexivity. }
  
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k) + 1) * PI) in k2def.
  clear slb sub.

  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
    rewrite id in phase. clear id.
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def.
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption.
    assert (y₁ = r * (1-cos q)) as y1def.
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption.
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id.
    unfold Rsqr.
    setl (r * r * (sin q * sin q + cos q * cos q - 1)).
    change (r * r * ((sin q)² + (cos q)² - 1) = 0).
    rewrite sin2_cos2. field.
    rewrite id in phase. lra. }
    
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp. {
  exists (2* (n-k) + 1)%Z. assumption. }
    
  assert (r<>0) as rne0. intro. subst. lra.
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.
    
  inversion_clear qrng as [qlb qub].
  inversion_clear qub as [qlt0 | qeq0].
  + assert (q <> 0) as qne0. {
      intro qeq0. rewrite qeq0 in *.
      unfold κ₂ in k2def.
      rewrite sin_0, cos_0 in k2def.
      
      assert (y₁ - r * (1 - 1) = y₁) as y1def. field.
      assert (x₁ - r * 0 = x₁) as x1def. field.
      rewrite y1def, x1def in k2def.
      rewrite Rplus_0_l in k2def.
      
      assert (~ (x₁ = 0 /\ y₁ = 0)) as notO.
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra.
      specialize (atan2_bound _ _ notO) as at2bnd.
      rewrite k2def in at2bnd.
      inversion_clear at2bnd as [at2lb at2ub].
      
      assert (- 1 < 2 * (n - k) + 1)%Z as Zlb.
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)). assumption. setl (-PI).
      assumption.
    
      assert (2 * (n - k) + 1 <= 1)%Z as Zub.
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)). assumption. setr (PI).
      assumption.
      
      assert ((n-k)%Z = 0%Z) as nmkeq0. omega.
      rewrite nmkeq0 in k2def. clear nmkeq0.
      assert ((2 * 0 + 1)%Z = 1%Z) as id. omega.
      rewrite id in k2def. clear id.
      assert (1 * PI = PI) as id. field. rewrite id in k2def. clear id.
      clear Zlb Zub at2ub at2lb y1def x1def.
      specialize (atan2_PI_impl _ _ notO k2def) as [xb yb].
      rewrite yb in *. lra. }
      
    rename phase into phasec.
    rename phaseb into phase.
      
    assert (- PI < q < PI) as qbnd. split; assumption.
    assert (2 * r - y₁ <> 0) as ntc. intro. lra.
      
    specialize (k_deriv_sign_quad2 _ _ _ _ qbnd rne0 phase ntc s0) as [sn | sp].
    ++ assert (0 < q) as zltq. {
         apply (Rmult_lt_reg_r (/2)). lra. setl 0. setr (q/2).
         rewrite sn.
         
         assert (0 < - (2 * r - y₁) * y₁) as id1. {
           apply Rmult_lt_0_compat. lra. assumption. }
         
         destruct (Rle_dec 0 x₁) as [x1quad | x1nquad].
         rewrite <- (sqrt_Rsqr x₁) at 1; [| assumption].
         assert (sqrt x₁² - sqrt (x₁² - (2 * r - y₁) * y₁) < 0) as npos. {
           apply (Rplus_lt_reg_l (sqrt (x₁² - (2 * r - y₁) * y₁))).
           setl (sqrt x₁²). setr (sqrt (x₁² - (2 * r - y₁) * y₁)).
           apply sqrt_lt_1. apply Rle_0_sqr.
           
           setr (x₁² + y₁ * y₁ - 2 * r * y₁).
           apply (Rplus_le_reg_r r²). setl (r²).
           unfold Rsqr at 3.
           setr (x₁² + (y₁-r)²). left. assumption.
           
           apply (Rplus_lt_reg_r (- x₁²)). setl 0. setr (-(2*r-y₁)*y₁).
           assumption. }
         
         assert (0 < - (sqrt x₁² - sqrt (x₁² - (2 * r - y₁) * y₁)) / - (2 * r - y₁))
           as argpos. {
           apply Rdiv_lt_0_compat. lra. lra. }
         
         rewrite <- atan_0.
         apply atan_increasing.
         setr (-(sqrt x₁² - sqrt (x₁² - (2 * r - y₁) * y₁)) / - (2 * r - y₁)).
         intro. lra.
         assumption.
         
         apply Rnot_le_lt in x1nquad.
         assert (0 < - (x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / - (2 * r - y₁))
           as argpos. {
           apply Rdiv_lt_0_compat.
           rewrite <- Ropp_0.
           apply Ropp_lt_contravar.
           specialize (sqrt_pos (x₁² - (2 * r - y₁) * y₁)) as sqp.
           lra.
           lra. }
         rewrite <- atan_0.
         apply atan_increasing.
         setr (-(x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / - (2 * r - y₁)).
         intro. lra.
         assumption. }
       
       assert (0 < κ₂ x₁ y₁ r q <= PI) as k2rng. {
         unfold κ₂.
         assert (forall z, 0 < y₁ - r * (1 - cos z)) as ysign. {
           intros.
           apply (Rplus_lt_reg_r ((1 - cos z) * r - y₁)).
           setr 0. setl ((1 - cos z) * r - y₁).
           apply (Rle_lt_trans _ (2 * r - y₁)).
           apply (Rplus_le_reg_r y₁).
           apply (Rmult_le_reg_r (/r)).
           apply (Rinv_0_lt_compat). assumption. setr 2. intro. lra.
           setl (1-cos z). intro. lra.
           specialize (COS_bound z) as [coslb cosub].
           lra. assumption. }
         specialize (ysign q).
         destruct (Rlt_dec 0 (x₁ - r * sin q)).
         specialize (atan2Q1 _ _ r0 ysign) as [atlb atub].
         split. assumption.
         apply (Rle_trans _ (PI/2)). left. assumption. lra.
         
         apply Rnot_lt_le in n0.
         inversion_clear n0 as [xarglt0 |xargeq0].
         specialize (atan2Q2 _ _ xarglt0 ysign) as [atlb atub].
         split.
         apply (Rlt_trans _ (PI/2)). lra. assumption.
         left. assumption. rewrite xargeq0.
         rewrite (atan2_PI2 _ ysign). split; lra. }
       
       rewrite k2def in k2rng.
       
       destruct (n-k)%Z.
       +++ exfalso. simpl in k2rng.
           inversion_clear k2rng as [k2lb [k2ub | k2eq]].
           assert (PI < q + 1 * PI) as qgtPI. lra.
           lra. lra.
       +++ exfalso. assert (3 <= IZR (2 * Z.pos p + 1)) as postm.
           rewrite plus_IZR, mult_IZR.
           assert (1 <= IZR (Z.pos p)) as pospos.
           apply IZR_le.
           specialize (Zle_0_pos p) as zleZpos.
           assert (Z.pos p <> 0)%Z.
           discriminate. lia.
           apply (Rle_trans _ (2 * 1 + 1)). 
           lra. lra.
           inversion_clear k2rng as [k2lb [k2ub | k2eq]].
           assert (2 * PI < q + IZR (2 * Z.pos p + 1) * PI) as qgtPI. {
             apply (Rlt_le_trans _ (q + 3 * PI)). 
             lra.
             apply (Rplus_le_reg_r (-q)). setl (3 * PI).
             setr (IZR (2 * Z.pos p + 1) * PI).
             apply (Rmult_le_reg_r (/PI)).
             apply Rinv_0_lt_compat. lra.
             setl 3. intro. lra. setr (IZR (2 * Z.pos p + 1)). intro. lra.
             assumption. }
           lra.
           assert (3 < 1) as fo. {
             apply (Rle_lt_trans _ (IZR (2 * Z.pos p + 1))).
             assumption.
             apply (Rmult_lt_reg_r PI). lra. setr PI.
             rewrite <- k2eq at 2.
             apply (Rplus_lt_reg_r (- IZR (2 * Z.pos p + 1) * PI)).
             setl 0. setr q. assumption. }
           lra.
           
       +++ assert (IZR (2 * Z.neg p + 1) <= -1 ) as negtm.
           rewrite plus_IZR, mult_IZR.
           assert (IZR (Z.neg p) <= -1) as negneg.
           rewrite <- Pos2Z.opp_pos.
           rewrite opp_IZR.
           apply Ropp_le_contravar.
           change (IZR 1 <= IZR (Z.pos p)).
           apply IZR_le.
           specialize (Zle_0_pos p) as zleZpos.
           assert (Z.pos p <> 0)%Z. {
             discriminate. }
           lia.
           apply (Rle_trans _ (2 * (- 1) + 1)).
           apply (Rplus_le_reg_r (-1)). setr (2 * -1). setl (2 * IZR (Z.neg p)).
           apply (Rmult_le_reg_r (/2)).
           apply Rinv_0_lt_compat. lra.
           setr (-1). setl (IZR (Z.neg p)). assumption.
           lra.
           
           inversion_clear k2rng as [k2lb k2ub].
           clear - qlt0 zltq negtm k2lb pigt0.
           apply (Rmult_le_compat_r PI) in negtm.
           lra.
           left. assumption.
           
    ++ exists (-k)%Z.
       rewrite <- sp.
       fieldrewrite (2*(q/2)) q.
       rewrite mult_IZR, opp_IZR.
       apply (Rplus_eq_reg_r (2 * IZR k * PI)).
       setr q. unfold q. field.

  + exfalso.
    unfold κ₂ in k2def.
    rewrite qeq0 in *.
    rewrite cos_PI, sin_PI in k2def.
    
    assert (y₁ - r * (1 - -1) = y₁ - 2 * r ) as id. field.
    rewrite id in k2def. clear id.
    assert (x₁ - r * 0 = x₁) as id. field.
    rewrite id in k2def. clear id.
    
    assert (0 < y₁ - 2 * r) as yinq. lra.
    assert (0 < atan2 (y₁ - 2 * r) x₁ < PI) as a2inq. {
      destruct (Rlt_dec 0 x₁) as [x1quad | x1nquad].
      specialize (atan2Q1 _ _ x1quad yinq) as [q1lb q1ub].
      split. assumption. apply (Rlt_trans _ (PI/2)). assumption. lra.
      apply (Rnot_lt_le) in x1nquad.
      inversion_clear x1nquad as [x1lt0 |x1eq0].
      specialize (atan2Q2 _ _ x1lt0 yinq) as [q1lb q1ub].
      split. apply (Rlt_trans _ (PI/2)). lra.
      assumption. assumption.
      
      subst.
      rewrite atan2_PI2. split; lra. assumption. }
    
    rewrite k2def in *.
    rewrite plus_IZR, mult_IZR in a2inq.
    assert (PI + (2 * IZR (n - k) + 1) * PI =
            2* (IZR (n - k + 1)) * PI) as mult2PI. {
      rewrite plus_IZR. field. }

    rewrite mult2PI in a2inq. clear mult2PI.
    
    inversion_clear a2inq as [a2lb a2ub].
    destruct (n - k + 1)%Z.
  - lra.
  - specialize (IZRposge1 p) as pospos.
    apply (Rmult_le_compat_l 2) in pospos.
    apply (Rmult_le_compat_r (PI)) in pospos.
    lra. left. assumption. left. lra.
  - specialize (IZRneglen1 p) as negneg.
    apply (Rmult_le_compat_l 2) in negneg.
    apply (Rmult_le_compat_r (PI)) in negneg.
    lra. left. assumption. left. lra.
Qed.

Lemma negroot_even_Q1Q2top_rpos :
  forall x₁ y₁ r θ
         (y1quad : 2*r - y₁ < 0)
         (y1pos : 0 < y₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 4. intros k2vale.
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. {
    split. setl (- (2*PI)/2). assumption.
    setr (2*PI/2). assumption. }

  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id. field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k)) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2.
    rewrite mult_IZR. field.
    rewrite id2. clear id2.
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k)) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k))) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k))) = 2 * n)%Z as id3. lia.
    rewrite id3. clear id3. reflexivity. }
  
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k)) * PI) in k2def.
  clear slb sub.

  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
    rewrite id in phase. clear id.
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def.
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption.
    assert (y₁ = r * (1-cos q)) as y1def.
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption.
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id.
    unfold Rsqr.
    setl (r * r * (sin q * sin q + cos q * cos q - 1)).
    change (r * r * ((sin q)² + (cos q)² - 1) = 0).
    rewrite sin2_cos2. field.
    rewrite id in phase. lra. }
    
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp. {
  exists (2* (n-k))%Z. assumption. }
    
  assert (r<>0) as rne0. intro. subst. lra.
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.
    
  inversion_clear qrng as [qlb qub].
  inversion_clear qub as [qlt0 | qeq0].
  + assert (q <> 0) as qne0. {
      intro qeq0. rewrite qeq0 in *.
      unfold κ₂ in k2def.
      rewrite sin_0, cos_0 in k2def.
      
      assert (y₁ - r * (1 - 1) = y₁) as y1def. field.
      assert (x₁ - r * 0 = x₁) as x1def. field.
      rewrite y1def, x1def in k2def.
      rewrite Rplus_0_l in k2def.
      
      assert (~ (x₁ = 0 /\ y₁ = 0)) as notO.
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra.
      specialize (atan2_bound _ _ notO) as at2bnd.
      rewrite k2def in at2bnd.
      inversion_clear at2bnd as [at2lb at2ub].
      
      assert (- 1 < 2 * (n - k))%Z as Zlb.
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)). assumption. setl (-PI).
      assumption.
    
      assert (2 * (n - k) <= 1)%Z as Zub.
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)). assumption. setr (PI).
      assumption.
      
      assert ((n-k)%Z = 0%Z) as nmkeq0. omega.
      rewrite nmkeq0 in k2def. clear nmkeq0.
      assert ((2 * 0)%Z = 0%Z) as id. omega.
      rewrite id in k2def. clear id.
      assert (0 * PI = 0) as id. field.
      rewrite id in k2def. clear id.
      clear Zlb Zub at2ub at2lb y1def x1def.
      specialize (atan2_0_impl _ _ notO k2def) as [xb yb].
      rewrite yb in *. lra. }
      
    rename phase into phasec.
    rename phaseb into phase.
      
    assert (- PI < q < PI) as qbnd. split; assumption.
    assert (2 * r - y₁ <> 0) as ntc. intro. lra.
      
    specialize (k_deriv_sign_quad2 _ _ _ _ qbnd rne0 phase ntc s0) as [sn | sp].

    ++ exists (-k)%Z.
       rewrite <- sn.
       fieldrewrite (2*(q/2)) q.
       rewrite mult_IZR, opp_IZR.
       apply (Rplus_eq_reg_r (2 * IZR k * PI)).
       setr q. unfold q. field.

    ++ assert (q < 0) as zltq. {
         apply (Rmult_lt_reg_r (/2)). lra. setr 0. setl (q/2).
         rewrite sp.
         
         assert (0 < - (2 * r - y₁) * y₁) as id1. {
           apply Rmult_lt_0_compat. lra. assumption. }

         assert (0 < x₁² - (2 * r - y₁) * y₁) as sqapos. {
           apply Rplus_le_lt_0_compat;
             [zltab; lra|lra]. }
         
         destruct (Rle_dec 0 x₁) as [x1quad | x1nquad].
         +++ assert (0 < x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) as npos. {
               apply Rplus_le_lt_0_compat.
               assumption.
               rewrite <- sqrt_0.
               apply sqrt_lt_1; try lra. }
             
             rewrite <- atan_0.
             apply atan_increasing.
             apply (Rmult_lt_reg_r (- (2 * r - y₁))).
             lra.
             setr (-0).
             setl (- (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))).
             lra.
             lra.
         +++ apply Rnot_le_lt in x1nquad.
             assert (0 < (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)))
               as argpos. {
               apply (Rplus_lt_reg_r (-x₁)).
               arn.
               setr (sqrt (x₁² - (2 * r - y₁) * y₁)).
               rewrite <- (Rabs_left x₁) at 1; try assumption.
               rewrite <- sqrt_Rsqr_abs.
               apply sqrt_lt_1; try lra.
               zltab. }
             rewrite <- atan_0.
             apply atan_increasing.
             apply (Rmult_lt_reg_r (- (2 * r - y₁))).
             lra.
             setr (- 0); try lra.
             setl (-(x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))); try lra. }
       
       assert (0 < κ₂ x₁ y₁ r q <= PI) as k2rng. {
         unfold κ₂.
         assert (forall z, 0 < y₁ - r * (1 - cos z)) as ysign. {
           intros.
           apply (Rplus_lt_reg_r ((1 - cos z) * r - y₁)).
           setr 0. setl ((1 - cos z) * r - y₁).
           apply (Rle_lt_trans _ (2 * r - y₁)).
           apply (Rplus_le_reg_r y₁).
           apply (Rmult_le_reg_r (/r)).
           apply (Rinv_0_lt_compat). assumption. setr 2. intro. lra.
           setl (1-cos z). intro. lra.
           specialize (COS_bound z) as [coslb cosub].
           lra. assumption. }
         specialize (ysign q).
         destruct (Rlt_dec 0 (x₁ - r * sin q)).
         specialize (atan2Q1 _ _ r0 ysign) as [atlb atub].
         split. assumption.
         apply (Rle_trans _ (PI/2)). left. assumption. lra.
         
         apply Rnot_lt_le in n0.
         inversion_clear n0 as [xarglt0 |xargeq0].
         specialize (atan2Q2 _ _ xarglt0 ysign) as [atlb atub].
         split.
         apply (Rlt_trans _ (PI/2)). lra. assumption.
         left. assumption. rewrite xargeq0.
         rewrite (atan2_PI2 _ ysign). split; lra. }
       
       rewrite k2def in k2rng.
       
       destruct (n-k)%Z.
       +++ exfalso. simpl in k2rng.
           inversion_clear k2rng as [k2lb [k2ub | k2eq]].
           assert (PI < q + 1 * PI) as qgtPI. lra.
           lra. lra.
       +++ exfalso. assert (2 <= IZR (2 * Z.pos p)) as postm. {
             rewrite mult_IZR.
             specialize (IZRposge1 p) as pospos.
             apply (Rle_trans _ (2 * 1)). 
             lra. lra. }
           inversion_clear k2rng as [k2lb [k2ub | k2eq]].
           assert (PI < q + IZR (2 * Z.pos p) * PI) as qgtPI. {
             apply (Rlt_le_trans _ (q + 2 * PI)). 
             lra.
             apply (Rplus_le_reg_r (-q)). setl (2 * PI).
             setr (IZR (2 * Z.pos p) * PI).
             apply (Rmult_le_reg_r (/PI)).
             apply Rinv_0_lt_compat. lra.
             setl 2. intro. lra.
             setr (IZR (2 * Z.pos p)).
             intro. lra.
             assumption. }
           lra.
           assert (-1 < -1) as fo. {
             assert (-1 = 1 - 2) as id;
               [lra| rewrite id at 2; clear id].
             apply (Rlt_le_trans _ (1 - IZR (2 * Z.pos p))); try lra.
             apply (Rmult_lt_reg_r PI); try lra. }
           lra.
           
       +++ exfalso.
           assert (IZR (2 * Z.neg p) * PI <= -2 * PI ) as negtm. {
             rewrite mult_IZR.
             apply (Rmult_le_reg_r (/ (2 * PI))).
             zltab.
             specialize (IZRneglen1 p) as negneg.
             lrag negneg. }
           lra.
           
  + exfalso.
    unfold κ₂ in k2def.
    rewrite qeq0 in *.
    rewrite cos_PI, sin_PI in *.
    assert (y₁ - r * (1 - -1) = y₁ - 2 * r ) as id;
      [field| rewrite id in *; clear id].
    autorewrite with null in *.
    
    assert (0 < y₁ - 2 * r) as yinq. lra.
    assert (0 < atan2 (y₁ - 2 * r) x₁ < PI) as a2inq. {
      destruct (Rlt_dec 0 x₁) as [x1quad | x1nquad].
      specialize (atan2Q1 _ _ x1quad yinq) as [q1lb q1ub].
      split. assumption. apply (Rlt_trans _ (PI/2)). assumption. lra.
      apply (Rnot_lt_le) in x1nquad.
      inversion_clear x1nquad as [x1lt0 |x1eq0].
      specialize (atan2Q2 _ _ x1lt0 yinq) as [q1lb q1ub].
      split. apply (Rlt_trans _ (PI/2)). lra.
      assumption. assumption.
      
      subst.
      rewrite atan2_PI2. split; lra. assumption. }
    
    rewrite k2def in *.
    rewrite mult_IZR in a2inq.
    
    inversion_clear a2inq as [a2lb a2ub].
    destruct (n - k)%Z.
  - lra.
  - specialize (IZRposge1 p) as pospos.
    apply (Rmult_le_compat_l 2) in pospos.
    apply (Rmult_le_compat_r (PI)) in pospos.
    lra. left. assumption. left. lra.
  - specialize (IZRneglen1 p) as negneg.
    apply (Rmult_le_compat_l 2) in negneg.
    apply (Rmult_le_compat_r (PI)) in negneg.
    lra. left. assumption. left. lra.
Qed.


Lemma posroot_odd_Q1posarm_rpos :
  forall x₁ y₁ r θ
         (x1quad :  0 < x₁)
         (y1quad : 2*r - y₁ = 0)
         (y1pos : 0 < y₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = IZR (2 * m + 1) * PI.
Proof.
  intros until 5. intros k2vale.
  
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n + 1)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.

  assert (- PI < q <= PI) as qrng. {
    split. setl (- (2*PI)/2). assumption. setr (2*PI/2). assumption. }
  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id;
    [field| rewrite id in k2def; clear id].
  assert (θ + IZR (2 * n + 1) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k) + 1) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2;
      [rewrite mult_IZR; field| rewrite id2; clear id2].
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k) + 1) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k) + 1)) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k) + 1)) = 2 * n + 1)%Z as id3. omega.
    rewrite id3. clear id3. reflexivity. }
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k) + 1) * PI) in k2def.
  clear slb sub.
    
  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.

  autorewrite with null in phase.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
    rewrite id in phase. clear id.
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def.
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption.
    assert (y₁ = r * (1-cos q)) as y1def.
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption.
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id.
    unfold Rsqr.
    setl (r * r * (sin q * sin q + cos q * cos q - 1)).
    change (r * r * ((sin q)² + (cos q)² - 1) = 0).
    rewrite sin2_cos2. field.
    rewrite id in phase. lra. }
  
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k) + 1)%Z. assumption.
  
  assert (r<>0) as rne0. intro. subst. lra.
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  assert (q <> 0) as qne0. {
    intro qeq0.
    rewrite qeq0 in *.
    unfold κ₂ in k2def.
    autorewrite with null in k2def.
    rewrite Rminus_eq_0 in k2def.
    autorewrite with null in k2def.
  
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra. }

    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].


    assert (- 1 < 2 * (n - k) + 1)%Z as Zlb. {
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)). assumption. setl (-PI).
      assumption. }
    
    assert (2 * (n - k) + 1 <= 1)%Z as Zub. {
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)). assumption. setr (PI).
      assumption. }


    assert ((n-k)%Z = 0%Z) as nmkeq0. lia.
    rewrite nmkeq0 in k2def. clear nmkeq0.
    assert ((2 * 0 + 1)%Z = 1%Z) as id. lia.
    rewrite id in k2def. clear id.
    assert (1 * PI = PI) as id. field. rewrite id in k2def. clear id.
    specialize (atan2_PI_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra. }

  inversion_clear qrng as [qlb qub].
  
  assert (y₁ = 2 * r) as y1def. {
  apply (Rplus_eq_reg_r (-y₁)). setl 0. rewrite <- y1quad. field. }
  
  inversion_clear qub as [qlt0 | qeq0].
  + exfalso.
    apply k_deriv_sign_lin2 in s0; auto.
    inversion_clear s0 as [q2def x1ne0].
    clear qlb.
    assert (0 < q) as qlb. {
    apply (Rmult_lt_reg_r (/2)). apply (Rinv_0_lt_compat). lra.
    setl 0. setr (q/2). rewrite q2def.
    rewrite <- atan_0.
    apply atan_increasing.
    apply (Rmult_lt_reg_r (2 * x₁)). lra. setl 0.
    setr y₁. intro. lra. assumption.  }
    
    assert (0 <= κ₂ x₁ y₁ r q) as k2nneg. {
      unfold κ₂.
      rewrite y1def.
      fieldrewrite (2 * r - r * (1 - cos q))
                   (r*(1 + cos q)).
      assert (0 <= r*(1 + cos q)) as ynneg.
      setl (r * 0).
      apply Rmult_le_compat_l. left. assumption.
      specialize (COS_bound q) as [cbl cbu].
      lra.
      inversion_clear ynneg as [zlty |zeqy].
      destruct (Rlt_dec 0 (x₁ - r * sin q)).
      left. apply (atan2Q1 _ _ r0 zlty).
      apply Rnot_lt_le in n0.
      inversion_clear n0 as [xlt0 |xeq0].
      left.
      apply (Rlt_trans _ (PI/2)). lra.
      apply (atan2Q2 _ _ xlt0 zlty).
      rewrite xeq0.
      rewrite atan2_PI2; auto. lra.
      rewrite <- zeqy.
      destruct (Rlt_dec 0 (x₁ - r * sin q)).
      right. rewrite atan2_0; auto.
      apply Rnot_lt_le in n0.
      inversion_clear n0 as [xlt0 |xeq0].
      rewrite atan2_PI; auto. left. lra.
      exfalso.
      assert (cos q = -1) as cosqn1.
      apply (Rplus_eq_reg_l 1).
      apply (Rmult_eq_reg_l r). setr 0. symmetry. assumption. intro. lra.
      rewrite <- cos_PI in cosqn1.
      
      apply cos_injective_range in cosqn1. lra.
      split; lra.
      split; lra. }
    
    assert (~ ((x₁ - r * sin q)=0 /\ (y₁ - r * (1 - cos q)) = 0)) as notin. {
      intro contr.
      inversion_clear contr as [xz yz].
      unfold κ₂ in k2nneg.
      
      assert (x₁ = r * sin q) as x1def.
      apply (Rplus_eq_reg_r (- r * sin q)). setr 0.
      rewrite <- xz. field.
      assert (y₁ = r * (1 - cos q)) as y1defq.
      apply (Rplus_eq_reg_r (- r * (1-cos q))). setr 0.
      rewrite <- yz. field.
      rewrite x1def, y1defq in phase.
      assert (r² < r²) as contra.
      rewrite <- Rmult_1_l. rewrite Rmult_comm.
      rewrite <- (sin2_cos2 q).
      rewrite (Rsqr_neg (cos q)).
      fieldrewrite (- cos q) ((1 - cos q) - 1).
      unfold Rsqr.
      setr ((r * sin q)² + (r * (1 - cos q) - r)²).
      assumption. lra. }
    specialize (atan2_bound _ _ notin) as k2bnd.
    change (- PI < κ₂ x₁ y₁ r q <= PI) in k2bnd.
    inversion_clear k2bnd as [k2lb k2ub].
    clear notin k2lb.
    rewrite k2def in k2nneg, k2ub.
    
    destruct (n - k)%Z.
    ++ assert (IZR (2 * 0 + 1) = 1) as IZRid.
       rewrite plus_IZR, mult_IZR. field.
       rewrite IZRid in *.
       lra.
       
    ++ assert (1 <= IZR (2 * (Z.pos p) + 1)) as IZRid. {
         rewrite plus_IZR, mult_IZR.
         specialize (IZRposge1 p) as ppos.
         lra. }
       apply (Rmult_le_compat_r (PI)) in IZRid;
       lra.
       
    ++ assert (IZR (2 * Z.neg p + 1) <= -1 ) as negtm. {
         rewrite plus_IZR, mult_IZR.
         specialize (IZRneglen1 p) as negneg.

         apply (Rle_trans _ (2 * (- 1) + 1)).
         apply (Rplus_le_reg_r (-1)). setr (2 * -1). setl (2 * IZR (Z.neg p)).
         apply (Rmult_le_reg_r (/2)).
         apply Rinv_0_lt_compat. lra.
         setr (-1). setl (IZR (Z.neg p)). assumption.
         lra. }
       
       apply (Rmult_le_compat_r PI) in negtm.
       lra. left. assumption.
  + unfold q in qeq0.
    exists (-k)%Z.
    rewrite plus_IZR, mult_IZR, opp_IZR.
    apply (Rplus_eq_reg_r (IZR k * (2*PI))).
    setr PI. assumption.
Qed.




Lemma negroot_even_Q1posarm_rpos :
  forall x₁ y₁ r θ
         (x1quad :  0 < x₁)
         (y1quad : 2*r - y₁ = 0)
         (y1pos : 0 < y₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = 2 * atan (r / x₁) + IZR (2 * m) * PI.
Proof.
  intros until 5. intros k2vale.
  
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.

  assert (- PI < q <= PI) as qrng. {
    split. setl (- (2*PI)/2). assumption. setr (2*PI/2). assumption. }
  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id;
    [field| rewrite id in k2def; clear id].
  assert (θ + IZR (2 * n) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k)) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2;
      [rewrite mult_IZR; field| rewrite id2; clear id2].
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k)) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k))) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k))) = 2 * n)%Z as id3. omega.
    rewrite id3. clear id3. reflexivity. }
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k)) * PI) in k2def.
  clear slb sub.
    
  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.

  autorewrite with null in phase.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
    rewrite id in phase. clear id.
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def.
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption.
    assert (y₁ = r * (1-cos q)) as y1def.
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption.
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id.
    unfold Rsqr.
    setl (r * r * (sin q * sin q + cos q * cos q - 1)).
    change (r * r * ((sin q)² + (cos q)² - 1) = 0).
    rewrite sin2_cos2. field.
    rewrite id in phase. lra. }
  
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k))%Z. assumption.
  
  assert (r<>0) as rne0. intro. subst. lra.
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  assert (q <> 0) as qne0. {
    intro qeq0.
    rewrite qeq0 in *.
    unfold κ₂ in k2def.
    autorewrite with null in k2def.
    rewrite Rminus_eq_0 in k2def.
    autorewrite with null in k2def.
  
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra. }

    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].


    assert (- 1 < 2 * (n - k))%Z as Zlb. {
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)).
      assumption.
      setl (- PI).
      assumption. }
      
      assert (2 * (n - k) <= 1)%Z as Zub. {
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)).
      assumption.
      setr PI.
      assumption. }
    
    assert ((n-k)%Z = 0%Z) as nmkeq0. omega.
    rewrite nmkeq0 in k2def. clear nmkeq0.
    rewrite mult_IZR in k2def.
    autorewrite with null in k2def.
    specialize (atan2_0_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra. }

  inversion_clear qrng as [qlb qub].
  
  assert (y₁ = 2 * r) as y1def. {
  apply (Rplus_eq_reg_r (-y₁)). setl 0. rewrite <- y1quad. field. }

  inversion_clear qub as [qlt0 | qeq0].
  + apply k_deriv_sign_lin2 in s0; auto.
    inversion_clear s0 as [q2def x1ne0].

    exists (-k)%Z.
    rewrite mult_IZR, opp_IZR.
    apply (Rplus_eq_reg_r (IZR k * (2*PI))).
    apply (Rmult_eq_reg_r (/ 2)).
    setr (atan (r / x₁)).
    rewrite y1def in q2def.
    fieldrewrite (r / x₁) (2 * r / (2 * x₁)).
    lra.
    rewrite <- q2def.
    unfold q.
    field.
    lra.

  + exfalso.
    unfold κ₂ in k2def.
    rewrite qeq0 in *.
    autorewrite with null in k2def.
    assert ((y₁ - r * (1 - -1)) = 0) as id1;
      [rewrite y1def; field| rewrite id1 in *; clear id1].
    rewrite atan2_0 in k2def; try assumption.

    destruct (n - k)%Z.
    ++ rewrite mult_IZR in k2def.
       autorewrite with null in k2def.
       generalize k2def.
       lra.
    ++ assert (0 <= IZR (2 * (Z.pos p)) * PI) as IZRid. {
         rewrite mult_IZR.
         specialize (IZRposge1 p) as ppos.
         apply (Rmult_le_reg_r (/ PI)).
         zltab.
         arn.
         setr (2 * IZR (Z.pos p)).
         lra.
         lra. }
       symmetry in k2def.
       apply Rplus_opp_r_uniq in k2def.
       rewrite k2def in IZRid.
       lra.
       
    ++ assert (IZR (2 * Z.neg p) <= -2 ) as negtm. {
         rewrite mult_IZR.
         specialize (IZRneglen1 p) as negneg.

         apply (Rle_trans _ (2 * (- 1))).
         apply (Rmult_le_reg_r (/2)).
         apply Rinv_0_lt_compat. lra.
         setr (-1). setl (IZR (Z.neg p)). assumption.
         lra. }
       
       apply (Rmult_le_compat_r PI) in negtm.
       lra. left. assumption.
Qed.



Lemma posroot_odd_Q4posarm_rneg :
  forall x₁ y₁ r θ
         (x1quad :  0 < x₁)
         (y1quad : 2*r - y₁ = 0)
         (y1neg : y₁ < 0)
         (rgt0 : r < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = IZR (2 * m + 1) * PI.
Proof.
  intros until 5. intros [m k2val].

  apply straight_symmetry in phase.
  rewrite Ropp_0 in phase.

  rewrite k2_symmetry in k2val.
  assert (exists n, κ₂ x₁ (- y₁) (- r) (- θ) = (-θ) + IZR (2 * n + 1) * PI)
    as k2val2. {
    exists (-m-1)%Z.
    apply (Rmult_eq_reg_l (-1)).
    setl (- κ₂ x₁ (- y₁) (- r) (- θ)).
    rewrite plus_IZR, mult_IZR, minus_IZR, opp_IZR.
    rewrite k2val.
    rewrite plus_IZR, mult_IZR. field. discrR. }
    
  assert (0 < (-y₁)) as zltny1; [ lra|].
  assert (0 < (-r)) as zltnr; [ lra|].

  assert (2 * (-r) - (-y₁) = 0) as y1pos. {
    apply (Rmult_eq_reg_r (-1)); [|discrR].
    setl (2 * r - y₁). setr 0. assumption. }

  specialize (posroot_odd_Q1posarm_rpos
                _ _ _ _ x1quad y1pos zltny1 zltnr phase k2val2)
    as [n nv].

  exists (-n -1)%Z.
  apply (Rmult_eq_reg_r (-1)) ; [| discrR].
  setl (-θ). rewrite nv.
  rewrite plus_IZR, mult_IZR, plus_IZR, mult_IZR, minus_IZR, opp_IZR.
  field.

  intros [xi yi].
  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tpigt0; [lra|].
  assert ( y₁= 2 * r) as y1def. {
    apply (Rplus_eq_reg_r (-y₁)). setl 0. rewrite <- y1quad. field. }
  
  assert (- cos θ  = 1) as cosid. {
    apply (Rplus_eq_reg_r (-1)).
    apply (Rmult_eq_reg_r (-r)); [|intro; lra].
    fieldrewrite (-1) (-1 - 2 + 2).
    setr 0. setl (2 * r - r * (1 - cos θ)).
    rewrite <- y1def. assumption. }
  
  rewrite <- neg_cos in cosid.
  
  specialize (inrange_0T (θ+PI) (2*PI) tpigt0) as [k qrng].
  assert (IZR k * (2 * PI) = 2 * IZR k * PI) as id; [field|].
  rewrite id in qrng. clear id.
  
  rewrite <- (Ropp_involutive (sin θ)) in xi.
  rewrite <- neg_sin in xi.
  rewrite <- (Ropp_involutive (cos θ)) in yi.
  rewrite <- neg_cos in yi.
  rewrite <- (cos_period1 _ k) in yi.
  rewrite <- (sin_period1 _ k) in xi.
  rewrite <- (cos_period1 _ k) in cosid.
  
  set (q := θ + PI + 2 * IZR k * PI) in *.

  specialize (cosθeq1 _ qrng cosid) as qeq0.
  rewrite qeq0 in xi,yi.
  rewrite sin_0, Ropp_0 in xi.
  rewrite cos_0 in yi.
  rewrite (Rmult_0_r r), Rminus_0_r in xi.
  clear - xi x1quad. lra.
Qed.


Lemma negroot_even_Q4posarm_rneg :
  forall x₁ y₁ r θ
         (x1quad :  0 < x₁)
         (y1quad : 2*r - y₁ = 0)
         (y1neg : y₁ < 0)
         (rgt0 : r < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = 2 * atan (r / x₁) + IZR (2 * m) * PI.
Proof.
  intros until 5. intros [m k2val].

  apply straight_symmetry in phase.
  rewrite Ropp_0 in phase.

  rewrite k2_symmetry in k2val.
  assert (exists n, κ₂ x₁ (- y₁) (- r) (- θ) = (-θ) + IZR (2 * n) * PI)
    as k2val2. {
    exists (-m)%Z.
    apply (Rmult_eq_reg_l (-1)).
    setl (- κ₂ x₁ (- y₁) (- r) (- θ)).
    rewrite mult_IZR, opp_IZR.
    rewrite k2val.
    rewrite mult_IZR. field. discrR. }
    
  assert (0 < (-y₁)) as zltny1; [ lra|].
  assert (0 < (-r)) as zltnr; [ lra|].

  assert (2 * (-r) - (-y₁) = 0) as y1pos. {
    apply (Rmult_eq_reg_r (-1)); [|discrR].
    setl (2 * r - y₁). setr 0. assumption. }

  specialize (negroot_even_Q1posarm_rpos
                _ _ _ _ x1quad y1pos zltny1 zltnr phase k2val2)
    as [n nv].

  exists (-n)%Z.
  apply (Rmult_eq_reg_r (-1)) ; [| discrR].
  setl (-θ). rewrite nv.
  rewrite mult_IZR, mult_IZR, opp_IZR.
  fieldrewrite (- r / x₁) (- (r / x₁)).
  lra.
  rewrite atan_opp.
  field.

  intros [xi yi].
  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tpigt0; [lra|].
  assert ( y₁= 2 * r) as y1def. {
    apply (Rplus_eq_reg_r (-y₁)). setl 0. rewrite <- y1quad. field. }
  
  assert (- cos θ  = 1) as cosid. {
    apply (Rplus_eq_reg_r (-1)).
    apply (Rmult_eq_reg_r (-r)); [|intro; lra].
    fieldrewrite (-1) (-1 - 2 + 2).
    setr 0. setl (2 * r - r * (1 - cos θ)).
    rewrite <- y1def. assumption. }
  
  rewrite <- neg_cos in cosid.
  
  specialize (inrange_0T (θ+PI) (2*PI) tpigt0) as [k qrng].
  assert (IZR k * (2 * PI) = 2 * IZR k * PI) as id; [field|].
  rewrite id in qrng. clear id.
  
  rewrite <- (Ropp_involutive (sin θ)) in xi.
  rewrite <- neg_sin in xi.
  rewrite <- (Ropp_involutive (cos θ)) in yi.
  rewrite <- neg_cos in yi.
  rewrite <- (cos_period1 _ k) in yi.
  rewrite <- (sin_period1 _ k) in xi.
  rewrite <- (cos_period1 _ k) in cosid.
  
  set (q := θ + PI + 2 * IZR k * PI) in *.

  specialize (cosθeq1 _ qrng cosid) as qeq0.
  rewrite qeq0 in xi,yi.
  rewrite sin_0, Ropp_0 in xi.
  rewrite cos_0 in yi.
  rewrite (Rmult_0_r r), Rminus_0_r in xi.
  clear - xi x1quad. lra.
Qed.


Lemma posroot_odd_Q2negarm_rpos :
  forall x₁ y₁ r θ
         (x1quad :  x₁ < 0)
         (y1quad : 2*r - y₁ = 0)
         (y1pos : 0 < y₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan (r / x₁) + IZR (2 * m) * PI.
Proof.
  intros until 5. intros k2vale.
  
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n+1)%Z. assumption. } 

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. {
    split. setl (- (2*PI)/2). assumption.
    setr (2*PI/2). assumption. }

  
  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id;
    [field| rewrite id in k2def; clear id].

  assert (θ + IZR (2 * n + 1) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k) + 1) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2. {
      rewrite mult_IZR. field. }
    rewrite id2. clear id2.
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k) + 1) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k) + 1)) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k) + 1)) = 2 * n + 1)%Z as id3. lia.
    rewrite id3. clear id3. reflexivity. }
  
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k) + 1) * PI) in k2def.
  clear slb sub.
  
  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
    rewrite id in phase. clear id.
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def.
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption.
    assert (y₁ = r * (1-cos q)) as y1def.
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption.
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id.
    unfold Rsqr.
    setl (r * r * (sin q * sin q + cos q * cos q - 1)).
    change (r * r * ((sin q)² + (cos q)² - 1) = 0).
    rewrite sin2_cos2. field.
    rewrite id in phase. lra. }
    
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k) + 1)%Z. assumption.
  
  assert (r<>0) as rne0. {
    intro. subst. lra. }
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  assert (q <> 0) as qne0. {
    intro qeq0. rewrite qeq0 in *.
    unfold κ₂ in k2def.
    rewrite sin_0, cos_0 in k2def.
    
    assert (y₁ - r * (1 - 1) = y₁) as y1def; try field.
    assert (x₁ - r * 0 = x₁) as x1def; try field.
    rewrite y1def, x1def in k2def.
    rewrite Rplus_0_l in k2def.
    
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra. }

    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].
    
    assert (- 1 < 2 * (n - k) + 1)%Z as Zlb. {
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)). assumption. setl (-PI).
      assumption. }
    
    assert (2 * (n - k) + 1 <= 1)%Z as Zub. {
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)). assumption. setr (PI).
      assumption. }
    
    assert ((n-k)%Z = 0%Z) as nmkeq0;
      [lia| rewrite nmkeq0 in k2def; clear nmkeq0].
    assert ((2 * 0 + 1)%Z = 1%Z) as id;
      [lia| rewrite id in k2def; clear id].
    assert (1 * PI = PI) as id;
      [field| rewrite id in k2def; clear id].
    clear Zlb Zub at2ub at2lb y1def x1def.
    specialize (atan2_PI_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra. }
  
  inversion_clear qrng as [qlb qub].
  
  assert (y₁ = 2 * r) as y1def. {
    apply (Rplus_eq_reg_r (-y₁)). setl 0. rewrite <- y1quad. field. }
  
  inversion_clear qub as [qlt0 | qeq0].
  + apply k_deriv_sign_lin2 in s0; auto.
    inversion_clear s0 as [q2def x1ne0].

    exists (-k)%Z.
    rewrite mult_IZR, opp_IZR.
    apply (Rplus_eq_reg_r (IZR k * (2*PI))).
    setr (2 * atan (r / x₁)).
    rewrite y1def in q2def.
    fieldrewrite (r / x₁) (2*r / (2*x₁)). assumption.
    rewrite <- q2def. unfold q. field.

  + exfalso.
    clear qlb.

    unfold κ₂ in k2def.
    rewrite qeq0 in *.
    rewrite cos_PI, sin_PI in *.
    assert ((y₁ - r * (1 - -1)) = 0) as id1. rewrite y1def. field.
    rewrite id1 in *. clear id1.
    assert ((x₁ - r * 0) = x₁) as id2. field.
    rewrite id2 in *. clear id2.
    rewrite atan2_PI in k2def; [|assumption].

    assert (IZR (2 * (n - k) + 1) = 0) as contra.
    apply (Rmult_eq_reg_r PI).
    apply (Rplus_eq_reg_l PI).
    rewrite <- k2def. field. auto.

    apply eq_IZR in contra.
    omega.
Qed.


Lemma negroot_even_Q2negarm_rpos :
  forall x₁ y₁ r θ
         (x1quad :  x₁ < 0)
         (y1quad : 2*r - y₁ = 0)
         (y1pos : 0 < y₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = PI + IZR (2 * m) * PI.
Proof.
  intros until 5. intros k2vale.
  
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n)%Z. assumption. } 

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. {
    split. setl (- (2*PI)/2). assumption.
    setr (2*PI/2). assumption. }

  
  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id;
    [field| rewrite id in k2def; clear id].

  assert (θ + IZR (2 * n) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k)) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2. {
      rewrite mult_IZR. field. }
    rewrite id2. clear id2.
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k)) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k))) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k))) = 2 * n)%Z as id3. lia.
    rewrite id3. clear id3. reflexivity. }
  
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k)) * PI) in k2def.
  clear slb sub.
  
  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
    rewrite id in phase. clear id.
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def.
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption.
    assert (y₁ = r * (1-cos q)) as y1def.
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption.
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id.
    unfold Rsqr.
    setl (r * r * (sin q * sin q + cos q * cos q - 1)).
    change (r * r * ((sin q)² + (cos q)² - 1) = 0).
    rewrite sin2_cos2. field.
    rewrite id in phase. lra. }
    
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k))%Z. assumption.
  
  assert (r<>0) as rne0. {
    intro. subst. lra. }
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  assert (q <> 0) as qne0. {
    intro qeq0. rewrite qeq0 in *.
    unfold κ₂ in k2def.
    rewrite sin_0, cos_0 in k2def.
    
    assert (y₁ - r * (1 - 1) = y₁) as y1def; try field.
    assert (x₁ - r * 0 = x₁) as x1def; try field.
    rewrite y1def, x1def in k2def.
    rewrite Rplus_0_l in k2def.
    
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra. }

    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].


    assert (- 1 < 2 * (n - k))%Z as Zlb. {
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)).
      assumption.
      setl (- PI).
      assumption. }
      
    assert (2 * (n - k) <= 1)%Z as Zub. {
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)).
      assumption.
      setr PI.
      assumption. }
    
    assert ((n-k)%Z = 0%Z) as nmkeq0. omega.
    rewrite nmkeq0 in k2def. clear nmkeq0.
    rewrite mult_IZR in k2def.
    autorewrite with null in k2def.
    specialize (atan2_0_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra. }
 
  inversion_clear qrng as [qlb qub].
  
  assert (y₁ = 2 * r) as y1def. {
    apply (Rplus_eq_reg_r (-y₁)). setl 0.
    rewrite <- y1quad. field. }
  
  inversion_clear qub as [qltPI | qeqPI].
  + exfalso.
    apply k_deriv_sign_lin2 in s0; auto.
    inversion_clear s0 as [q2def x1ne0].
    clear qltPI.
    assert (q < 0) as qub. {
      apply (Rmult_lt_reg_r (/2)). apply (Rinv_0_lt_compat). lra.
      setr 0. setl (q/2). rewrite q2def.
      rewrite <- atan_0.
      apply atan_increasing.
      apply (Rmult_lt_reg_r (- (2 * x₁))).
      lra.
      setr 0.
      setl (-y₁).
      lra.
      lra. }
    
    assert (0 <= κ₂ x₁ y₁ r q) as k2nneg. {
      unfold κ₂.
      rewrite y1def.
      fieldrewrite (2 * r - r * (1 - cos q))
                   (r*(1 + cos q)).
      assert (0 <= r*(1 + cos q)) as ynneg.
      setl (r * 0).
      apply Rmult_le_compat_l. left. assumption.
      specialize (COS_bound q) as [cbl cbu].
      lra.
      inversion_clear ynneg as [zlty |zeqy].
      destruct (Rlt_dec 0 (x₁ - r * sin q)).
      left. apply (atan2Q1 _ _ r0 zlty).
      apply Rnot_lt_le in n0.
      inversion_clear n0 as [xlt0 |xeq0].
      left.
      apply (Rlt_trans _ (PI/2)). lra.
      apply (atan2Q2 _ _ xlt0 zlty).
      rewrite xeq0.
      rewrite atan2_PI2; auto. lra.
      rewrite <- zeqy.
      destruct (Rlt_dec 0 (x₁ - r * sin q)).
      right. rewrite atan2_0; auto.
      apply Rnot_lt_le in n0.
      inversion_clear n0 as [xlt0 |xeq0].
      rewrite atan2_PI; auto. left. lra.
      exfalso.
      assert (cos q = -1) as cosqn1.
      apply (Rplus_eq_reg_l 1).
      apply (Rmult_eq_reg_l r). setr 0. symmetry. assumption. intro. lra.
      rewrite <- cos_PI in cosqn1.
      
      apply cos_injective_range in cosqn1. lra.
      split; lra.
      split; lra. }
    
    assert (~ ((x₁ - r * sin q) = 0 /\
               (y₁ - r * (1 - cos q)) = 0)) as notin. {
      intro contr.
      inversion_clear contr as [xz yz].
      unfold κ₂ in k2nneg.
      
      assert (x₁ = r * sin q) as x1def.
      apply (Rplus_eq_reg_r (- r * sin q)). setr 0.
      rewrite <- xz. field.
      assert (y₁ = r * (1 - cos q)) as y1defq.
      apply (Rplus_eq_reg_r (- r * (1-cos q))). setr 0.
      rewrite <- yz. field.
      rewrite x1def, y1defq in phase.
      assert (r² < r²) as contra.
      rewrite <- Rmult_1_l. rewrite Rmult_comm.
      rewrite <- (sin2_cos2 q).
      rewrite (Rsqr_neg (cos q)).
      fieldrewrite (- cos q) ((1 - cos q) - 1).
      unfold Rsqr.
      setr ((r * sin q)² + (r * (1 - cos q) - r)²).
      assumption. lra. }
    
    specialize (atan2_bound _ _ notin) as k2bnd.
    change (- PI < κ₂ x₁ y₁ r q <= PI) in k2bnd.
    inversion_clear k2bnd as [k2lb k2ub].
    clear notin k2lb.
    rewrite k2def in k2nneg, k2ub.
    
    destruct (n - k)%Z.
    ++ rewrite mult_IZR in *.
       autorewrite with null in *.
       lra.
       
    ++ assert (2 <= IZR (2 * (Z.pos p))) as IZRid. {
         rewrite mult_IZR.
         specialize (IZRposge1 p) as ppos.
         lra. }
       apply (Rmult_le_compat_r (PI)) in IZRid; try lra.
       
    ++ assert (IZR (2 * Z.neg p) <= -2 ) as negtm. {
         rewrite mult_IZR.
         specialize (IZRneglen1 p) as negneg.

         apply (Rle_trans _ (2 * (- 1))).
         apply (Rmult_le_reg_r (/2)).
         apply Rinv_0_lt_compat. lra.
         setr (-1). setl (IZR (Z.neg p)). assumption.
         lra. }
       
       apply (Rmult_le_compat_r PI) in negtm.
       lra. left. assumption.

    
  + exists (-k)%Z.
    rewrite mult_IZR, opp_IZR.
    apply (Rplus_eq_reg_r (IZR k * (2*PI))).
    setr (PI).
    rewrite <- qeqPI at 2.
    unfold q. field.
Qed.


Lemma posroot_odd_Q3_rpos :
  forall x₁ y₁ r θ
         (x1quad :  x₁ < 0)
         (y1pos : y₁ < 0)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 4. intros k2vale.
  
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n+1)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0; try lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. {
    split. setl (- (2*PI)/2). assumption.
    setr (2*PI/2). assumption. }
  
  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id;
    [field| rewrite id in k2def; clear id].
  assert (θ + IZR (2 * n + 1) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k) + 1) * PI) as id. {
  assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2;
    [rewrite mult_IZR; field| rewrite id2; clear id2].

  fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k) + 1) * PI)
               (θ + (IZR (2 * k) + IZR (2 * (n - k) + 1)) * PI).
  rewrite <- plus_IZR.
  assert ((2 * k + (2 * (n - k) + 1)) = 2 * n + 1)%Z as id3;
    [lia| rewrite id3; clear id3; reflexivity]. }

  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k) + 1) * PI) in k2def.
  clear slb sub.

  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id;
    [field | rewrite id in phase; clear id].

  autorewrite with null in *.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id;
      [ unfold Rsqr; field| rewrite id in phase; clear id].
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def. {
      apply (Rplus_eq_reg_r (- r * sin q)).
      setr 0. setl (x₁ - r * sin q). assumption. }
    assert (y₁ = r * (1-cos q)) as y1def. {
      apply (Rplus_eq_reg_r (- r * (1-cos q))).
      setr 0. setl (y₁ - r * (1-cos q)). assumption. }
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id. {
      unfold Rsqr.
      setl (r * r * (sin q * sin q + cos q * cos q - 1)).
      change (r * r * ((sin q)² + (cos q)² - 1) = 0).
      rewrite sin2_cos2. field. }
    
    rewrite id in phase. lra. }
  
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp. {
    exists (2* (n-k) + 1)%Z. assumption. }
    
  assert (r<>0) as rne0;
    [intro; subst; lra|].

  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.
  
  assert (q <> 0) as qne0. {
    intro qeq0. rewrite qeq0 in *.
    unfold κ₂ in k2def.
    autorewrite with null in k2def.
    rewrite Rminus_eq_0 in k2def.
    autorewrite with null in k2def.
    
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra. }

    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].
    
    assert (- 1 < 2 * (n - k) + 1)%Z as Zlb. {
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)). assumption. setl (-PI).
      assumption. }
    
    assert (2 * (n - k) + 1 <= 1)%Z as Zub. {
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)). assumption. setr (PI).
      assumption. }
    
    assert ((n-k)%Z = 0%Z) as nmkeq0. omega.
    rewrite nmkeq0 in k2def. clear nmkeq0.
    assert ((2 * 0 + 1)%Z = 1%Z) as id. omega.
    rewrite id in k2def. clear id.
    assert (1 * PI = PI) as id. field. rewrite id in k2def. clear id.

    specialize (atan2_PI_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra. }
  
  inversion_clear qrng as [qlb qub].
  
  inversion_clear qub as [qltPI | qeqPI].
  + apply k_deriv_sign_quad2 in s0; auto; [|intro; lra].
    inversion_clear s0 as [q2n | q2p].
    ++ exfalso.
       assert (q < 0) as qlt0.
       apply (Rmult_lt_reg_r (/2)). apply Rinv_0_lt_compat. lra.
       setr 0. setl (q/2). rewrite q2n.

       assert (0 < 2 * r - y₁) as denpos. {
       apply (Rplus_lt_reg_r (y₁)). setl y₁. setr (2*r).
       apply (Rlt_trans _ 0). assumption. lra. }
       
       rewrite <- atan_0.
       apply atan_increasing.
       apply (Rmult_lt_reg_r (2 * r - y₁)); [assumption|].
       setr 0. setl ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))).
       intro. lra.
       apply (Rplus_lt_reg_r (sqrt (x₁² - (2 * r - y₁) * y₁))).
       setr (sqrt (x₁² - (2 * r - y₁) * y₁)). setl x₁.
       apply (Rlt_le_trans _ 0). assumption.
       apply sqrt_pos.

       clear qltPI q2n.
       assert (-PI < κ₂ x₁ y₁ r q < 0) as [k2rngl k2rngu]. {
       unfold κ₂.
       split. apply (atan2_bound _ _ noton).
       assert (y₁ - r * (1 - cos q) < 0) as yneg.
       apply (Rplus_lt_reg_r (r * (1 - cos q))).
       setr (r * (1 - cos q)). setl y₁.
       apply (Rlt_le_trans _ 0). assumption.
       specialize (COS_bound q) as [cbql cbqu].
       apply Rmult_le_pos. left. assumption.
       lra.
       destruct (Rlt_dec 0 (x₁ - r * sin q)).
       apply atan2Q4; try assumption.
       apply Rnot_lt_le in n0.
       inversion_clear n0 as [xlt0 |xeq0].
       apply (Rlt_trans _ (-(PI/2))).
       apply atan2Q3; try assumption. lra.
       rewrite xeq0.
       rewrite atan2_mPI2; try assumption.
       apply (Rmult_lt_reg_r 2). lra. setr 0. setl (-PI).
       lra. }

       rewrite k2def in k2rngl, k2rngu.
       destruct (n-k)%Z.
       +++ assert (IZR (2 * 0 + 1) = 1) as IZRid.
           rewrite plus_IZR, mult_IZR. field.
           rewrite IZRid in *.
           lra.
           
       +++ assert (1 <= IZR (2 * (Z.pos p) + 1)) as IZRid. {
             rewrite plus_IZR, mult_IZR.
             specialize (IZRposge1 p) as pospos.
             lra. }
           apply (Rmult_le_compat_r (PI)) in IZRid;
           lra. 
           
       +++ assert (IZR (2 * Z.neg p + 1) <= -1 ) as negtm. {
           rewrite plus_IZR, mult_IZR.
           specialize (IZRneglen1 p) as negneg.

           apply (Rle_trans _ (2 * (- 1) + 1)).
           apply (Rplus_le_reg_r (-1)). setr (2 * -1). setl (2 * IZR (Z.neg p)).
           apply (Rmult_le_reg_r (/2)).
           apply Rinv_0_lt_compat. lra.
           setr (-1). setl (IZR (Z.neg p)). assumption.
           lra. }
           
           apply (Rmult_le_compat_r PI) in negtm.
           lra. left. assumption.
           
    ++ exists (-k)%Z.
       rewrite <- q2p. unfold q.
       rewrite mult_IZR,opp_IZR. field.
       
  + exfalso. clear qlb qne0.
    unfold κ₂ in k2def.
    rewrite qeqPI in *.
    rewrite sin_PI, cos_PI in *.
    
    assert (y₁ - r * (1 - - 1) = y₁ - 2*r) as y1def. field.
    assert (x₁ - r * 0 = x₁) as x1def. field.
    rewrite y1def, x1def in *.
    clear y1def x1def.

    assert (y₁ - 2 * r < 0) as yqd. lra.
    specialize (atan2Q3 _ _ x1quad yqd) as rng.
    rewrite k2def in rng.
    inversion_clear rng as [rlb rub].

    destruct ((n - k)%Z).
       ++ assert (IZR (2 * 0 + 1) = 1) as IZRid.
           rewrite plus_IZR, mult_IZR. field.
           rewrite IZRid in *.
           lra.
           
       ++ assert (1 <= IZR (2 * (Z.pos p) + 1)) as IZRid. {
            rewrite plus_IZR, mult_IZR.
            specialize (IZRposge1 p) as pospos.
            lra. }
          apply (Rmult_le_compat_r (PI)) in IZRid.
          lra. lra.
           
       ++ assert (2*Z.neg p + 1 <= -1)%Z as bnd. {
            rewrite <- Pos2Z.opp_pos.
            assert (Z.pos p <> 0)%Z as pne0. discriminate.
            specialize (Pos2Z.is_nonneg p) as pge0.
            assert (1 <= Z.pos p)%Z as pge1. lia.
            lia. }
          destruct (Z.eq_dec (-1)%Z (Z.neg p)).
          rewrite <- e in *.
          assert (PI + IZR (2 * -1 + 1) * PI = 0) as id.
          rewrite plus_IZR, mult_IZR. field. rewrite id in *. clear id.
          clear - rub pigt0. lra.
          
          assert (2 * Z.neg p + 1 <= -2)%Z as plen2. omega.
          apply IZR_le in plen2. 
          apply (Rmult_le_compat_r PI) in plen2.
          apply (Rplus_le_compat_l PI) in plen2.
          clear - rlb plen2. lra. left. assumption.
Qed.

Lemma negroot_even_Q3_rpos :
  forall x₁ y₁ r θ
         (x1quad :  x₁ < 0)
         (y1pos : y₁ < 0)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 4. intros k2vale.
  
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0; try lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. {
    split. setl (- (2*PI)/2). assumption.
    setr (2*PI/2). assumption. }
  
  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id;
    [field| rewrite id in k2def; clear id].
  assert (θ + IZR (2 * n) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k)) * PI) as id. {
  assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2;
    [rewrite mult_IZR; field| rewrite id2; clear id2].

  fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k)) * PI)
               (θ + (IZR (2 * k) + IZR (2 * (n - k))) * PI).
  rewrite <- plus_IZR.
  assert ((2 * k + (2 * (n - k))) = 2 * n)%Z as id3;
    [lia| rewrite id3; clear id3; reflexivity]. }

  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k)) * PI) in k2def.
  clear slb sub.

  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id;
    [field | rewrite id in phase; clear id].

  autorewrite with null in *.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id;
      [ unfold Rsqr; field| rewrite id in phase; clear id].
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def. {
      apply (Rplus_eq_reg_r (- r * sin q)).
      setr 0. setl (x₁ - r * sin q). assumption. }
    assert (y₁ = r * (1-cos q)) as y1def. {
      apply (Rplus_eq_reg_r (- r * (1-cos q))).
      setr 0. setl (y₁ - r * (1-cos q)). assumption. }
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id. {
      unfold Rsqr.
      setl (r * r * (sin q * sin q + cos q * cos q - 1)).
      change (r * r * ((sin q)² + (cos q)² - 1) = 0).
      rewrite sin2_cos2. field. }
    
    rewrite id in phase. lra. }
  
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp. {
    exists (2* (n-k))%Z. assumption. }
    
  assert (r<>0) as rne0;
    [intro; subst; lra|].

  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.
  
  assert (q <> 0) as qne0. {
    intro qeq0. rewrite qeq0 in *.
    unfold κ₂ in k2def.
    autorewrite with null in k2def.
    rewrite Rminus_eq_0 in k2def.
    autorewrite with null in k2def.
    
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra. }

    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].


    assert (- 1 < 2 * (n - k))%Z as Zlb. {
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)).
      assumption.
      setl (- PI).
      assumption. }
      
    assert (2 * (n - k) <= 1)%Z as Zub. {
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)).
      assumption.
      setr PI.
      assumption. }
    
    assert ((n-k)%Z = 0%Z) as nmkeq0. omega.
    rewrite nmkeq0 in k2def. clear nmkeq0.
    rewrite mult_IZR in k2def.
    autorewrite with null in k2def.
    specialize (atan2_0_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra. }

  inversion_clear qrng as [qlb qub].
  
  inversion_clear qub as [qltPI | qeqPI].
  + apply k_deriv_sign_quad2 in s0; auto; [|intro; lra].
    inversion_clear s0 as [q2n | q2p].
    ++ exists (-k)%Z.
       rewrite <- q2n. unfold q.
       rewrite mult_IZR,opp_IZR. field.
       
    ++ exfalso.
       assert (0 < q) as qlt0. {
         apply (Rmult_lt_reg_r (/2)). apply Rinv_0_lt_compat. lra.
         setl 0. setr (q/2).
         rewrite q2p.

         assert (0 < 2 * r - y₁) as denpos. {
           apply (Rplus_lt_reg_r (y₁)). setl y₁. setr (2*r).
           apply (Rlt_trans _ 0). assumption. lra. }

         assert (0 <= x₁² - (2 * r - y₁) * y₁) as argnn. {
           rewrite <- pm.
           zltab.
           setr ((2 * r - y₁) * - y₁).
           zltab. }

         rewrite <- atan_0.
         apply atan_increasing.
         apply (Rmult_lt_reg_r (2 * r - y₁)); [assumption|].
         setl 0.
         setr ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))).
         lra.
         apply (Rplus_lt_reg_r (- x₁)).
         setr (sqrt (x₁² - (2 * r - y₁) * y₁)).
         rewrite <- Rabs_left; try assumption.
         rewrite <- sqrt_Rsqr_abs.
         arn.
         apply sqrt_lt_1.
         zltab.
         assumption.
         apply (Rplus_lt_reg_r (- x₁²)).
         setl 0.
         setr ((2 * r - y₁) * - y₁).
         zltab. }
       
         clear qlb q2p.
       assert (-PI < κ₂ x₁ y₁ r q < 0) as [k2rngl k2rngu]. {
       unfold κ₂.
       split. apply (atan2_bound _ _ noton).
       assert (y₁ - r * (1 - cos q) < 0) as yneg.
       apply (Rplus_lt_reg_r (r * (1 - cos q))).
       setr (r * (1 - cos q)). setl y₁.
       apply (Rlt_le_trans _ 0). assumption.
       specialize (COS_bound q) as [cbql cbqu].
       apply Rmult_le_pos. left. assumption.
       lra.
       destruct (Rlt_dec 0 (x₁ - r * sin q)).
       apply atan2Q4; try assumption.
       apply Rnot_lt_le in n0.
       inversion_clear n0 as [xlt0 |xeq0].
       apply (Rlt_trans _ (-(PI/2))).
       apply atan2Q3; try assumption. lra.
       rewrite xeq0.
       rewrite atan2_mPI2; try assumption.
       apply (Rmult_lt_reg_r 2). lra. setr 0. setl (-PI).
       lra. }

       rewrite k2def in k2rngl, k2rngu.
       destruct (n-k)%Z.
       +++ assert (IZR (2 * 0) = 0) as IZRid.
           rewrite mult_IZR. field.
           rewrite IZRid in *.
           lra.
           
       +++ assert (2 <= IZR (2 * (Z.pos p))) as IZRid. {
             rewrite mult_IZR.
             specialize (IZRposge1 p) as pospos.
             lra. }
           apply (Rmult_le_compat_r (PI)) in IZRid;
           lra. 
           
       +++ assert (IZR (2 * Z.neg p) <= -2 ) as negtm. {
           rewrite mult_IZR.
           specialize (IZRneglen1 p) as negneg.

           apply (Rle_trans _ (2 * (- 1))).
           apply (Rmult_le_reg_r (/2)).
           apply Rinv_0_lt_compat. lra.
           setr (-1). setl (IZR (Z.neg p)). assumption.
           lra. }
           
           apply (Rmult_le_compat_r PI) in negtm.
           lra. left. assumption.
           
  + exfalso.
    clear qlb qne0.
    unfold κ₂ in k2def.
    rewrite qeqPI in *.
    rewrite sin_PI, cos_PI in *.
    
    assert (y₁ - r * (1 - - 1) = y₁ - 2*r) as y1def. field.
    assert (x₁ - r * 0 = x₁) as x1def. field.
    rewrite y1def, x1def in *.
    clear y1def x1def.

    assert (y₁ - 2 * r < 0) as yqd. lra.
    specialize (atan2Q3 _ _ x1quad yqd) as rng.
    rewrite k2def in rng.
    inversion_clear rng as [rlb rub].

    destruct ((n - k)%Z).
       ++ assert (IZR (2 * 0) = 0) as IZRid.
           rewrite mult_IZR. field.
           rewrite IZRid in *.
           lra.
           
       ++ assert (2 <= IZR (2 * (Z.pos p))) as IZRid. {
            rewrite mult_IZR.
            specialize (IZRposge1 p) as pospos.
            lra. }
          apply (Rmult_le_compat_r (PI)) in IZRid.
          lra. lra.
           
       ++ assert (2*Z.neg p <= -2)%Z as bnd. {
            rewrite <- Pos2Z.opp_pos.
            assert (Z.pos p <> 0)%Z as pne0. discriminate.
            specialize (Pos2Z.is_nonneg p) as pge0.
            assert (1 <= Z.pos p)%Z as pge1. lia.
            lia. }
          assert (-2 < 2 * Z.neg p)%Z.
          apply lt_IZR.
          apply (Rmult_lt_reg_r PI); try lra.
          lia.
Qed.


Lemma posroot_odd_Q4_rpos :
  forall x₁ y₁ r θ
         (x1quad :  0 <= x₁)
         (y1pos : y₁ < 0)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 4. intros k2vale.
  
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
  inversion_clear k2vale as [n k2val].
  exists (2*n+1)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. split. setl (- (2*PI)/2). assumption.
  setr (2*PI/2). assumption.
  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id. field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n + 1) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k) + 1) * PI) as id. {
  assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2.
  rewrite mult_IZR. field.
  rewrite id2. clear id2.
  fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k) + 1) * PI)
               (θ + (IZR (2 * k) + IZR (2 * (n - k) + 1)) * PI).
  rewrite <- plus_IZR.
  assert ((2 * k + (2 * (n - k) + 1)) = 2 * n + 1)%Z as id3. omega.
  rewrite id3. clear id3. reflexivity. }
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k) + 1) * PI) in k2def.
  clear slb sub.

  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
    rewrite id in phase. clear id.
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def.
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption.
    assert (y₁ = r * (1-cos q)) as y1def.
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption.
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id.
    unfold Rsqr.
    setl (r * r * (sin q * sin q + cos q * cos q - 1)).
    change (r * r * ((sin q)² + (cos q)² - 1) = 0).
    rewrite sin2_cos2. field.
    rewrite id in phase. lra. }
  
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k) + 1)%Z. assumption.

  assert (r<>0) as rne0; [intro; subst; lra|].
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  assert (q <> 0) as qne0. {
    intro qeq0. rewrite qeq0 in *.
    unfold κ₂ in k2def.
    autorewrite with null in k2def.
    rewrite Rminus_eq_0 in k2def.
    autorewrite with null in k2def.
    
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra. }
    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].
    
    assert (- 1 < 2 * (n - k) + 1)%Z as Zlb. {
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)). assumption. setl (-PI).
      assumption. }
      
    assert (2 * (n - k) + 1 <= 1)%Z as Zub. {
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)). assumption. setr (PI).
      assumption. }
    
    assert ((n-k)%Z = 0%Z) as nmkeq0;
     [lia| rewrite nmkeq0 in k2def; clear nmkeq0].
    autorewrite with null in k2def.
    clear Zlb Zub at2ub at2lb.
    specialize (atan2_PI_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra. }
  
  inversion_clear qrng as [qlb qub].
  
  inversion_clear qub as [qltPI | qeqPI].
  + apply k_deriv_sign_quad2 in s0; auto; [|intro; lra].
    inversion_clear s0 as [q2n | q2p].
    ++ exfalso.
       assert (q < 0) as qlt0. {
         apply (Rmult_lt_reg_r (/2)). apply Rinv_0_lt_compat. lra.
         setr 0. setl (q/2). rewrite q2n.
         
         assert (0 < 2 * r - y₁) as denpos. {
           apply (Rplus_lt_reg_r (y₁)). setl y₁. setr (2*r).
           apply (Rlt_trans _ 0). assumption. lra. }
         
         rewrite <- atan_0.
         apply atan_increasing.
         apply (Rmult_lt_reg_r (2 * r - y₁)); [assumption|].
         setr 0. setl ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))).
         lra.
         apply (Rplus_lt_reg_r (sqrt (x₁² - (2 * r - y₁) * y₁))).
         setr (sqrt (x₁² - (2 * r - y₁) * y₁)). setl x₁.
         
         rewrite <- (sqrt_Rsqr x₁) at 1; [|assumption].
         apply sqrt_lt_1. apply Rle_0_sqr.
         apply (Rplus_le_reg_r ((2 * r - y₁) * y₁)). setr (x₁²).
         setl ((2 * r - y₁) * y₁).
         
         apply (Rle_trans _ 0); [|apply Rle_0_sqr].
         apply Ropp_le_cancel.
         rewrite Ropp_0. setr ((2 * r - y₁) * (-y₁)).
         left.
         apply Rmult_lt_0_compat. assumption. lra.
         apply (Rplus_lt_reg_r (- (x₁²))). setl 0. setr ((2 * r - y₁) * (-y₁)).
         apply Rmult_lt_0_compat. assumption. lra. }
       
       clear qltPI q2n.
       assert (-PI < κ₂ x₁ y₁ r q < 0) as [k2rngl k2rngu]. {
         unfold κ₂.
         split. apply (atan2_bound _ _ noton).
         assert (y₁ - r * (1 - cos q) < 0) as yneg. {
           apply (Rplus_lt_reg_r (r * (1 - cos q))).
           setr (r * (1 - cos q)). setl y₁.
           apply (Rlt_le_trans _ 0). assumption.
           specialize (COS_bound q) as [cbql cbqu].
           apply Rmult_le_pos. left. assumption.
           lra. }
         destruct (Rlt_dec 0 (x₁ - r * sin q)).
         - apply atan2Q4; try assumption.
         - apply Rnot_lt_le in n0.
           inversion_clear n0 as [xlt0 |xeq0].
           apply (Rlt_trans _ (-(PI/2))).
           apply atan2Q3; try assumption. lra.
           rewrite xeq0.
           rewrite atan2_mPI2; try assumption.
           apply (Rmult_lt_reg_r 2). lra. setr 0. setl (-PI).
           lra. }

       rewrite k2def in k2rngl, k2rngu.
       destruct (n-k)%Z.
       +++ assert (IZR (2 * 0 + 1) = 1) as IZRid;
             [rewrite plus_IZR, mult_IZR; field|
              rewrite IZRid in *].
           lra.
           
       +++ assert (1 <= IZR (2 * (Z.pos p) + 1)) as IZRid. {
             rewrite plus_IZR, mult_IZR.
             assert (1 <= IZR (Z.pos p)).
             specialize (Pos2Z.is_pos p) as zltp.
             apply IZR_le. omega. lra. }
           apply (Rmult_le_compat_r (PI)) in IZRid; lra. 
           
       +++ assert (IZR (2 * Z.neg p + 1) <= -1 ) as negtm. {
             rewrite plus_IZR, mult_IZR.
             assert (IZR (Z.neg p) <= -1) as negneg.
             rewrite <- Pos2Z.opp_pos.
             rewrite opp_IZR.
             apply Ropp_le_contravar.
             change (IZR 1 <= IZR (Z.pos p)).
             apply IZR_le.
             specialize (Zle_0_pos p) as zleZpos.
             assert (Z.pos p <> 0)%Z.
             discriminate. omega.
             apply (Rle_trans _ (2 * (- 1) + 1)).
             apply (Rplus_le_reg_r (-1)). setr (2 * -1). setl (2 * IZR (Z.neg p)).
             apply (Rmult_le_reg_r (/2)).
             apply Rinv_0_lt_compat. lra.
             setr (-1). setl (IZR (Z.neg p)). assumption.
             lra. }
           
           apply (Rmult_le_compat_r PI) in negtm.
           lra. left. assumption.
           
    ++ exists (-k)%Z.
       rewrite <- q2p. unfold q.
       rewrite mult_IZR,opp_IZR. field.
       
  + exfalso. clear qlb qne0.
    unfold κ₂ in k2def.
    rewrite qeqPI in *.
    rewrite sin_PI, cos_PI in *.
    
    assert (y₁ - r * (1 - - 1) = y₁ - 2*r) as y1def. field.
    assert (x₁ - r * 0 = x₁) as x1def. field.
    rewrite y1def, x1def in *.
    clear y1def x1def.

    assert (y₁ - 2 * r < 0) as yqd; try lra.
    assert (- (PI / 2) <= atan2 (y₁ - 2 * r) (x₁) < 0) as rng. {
      inversion_clear x1quad as [x1gt0 | x1eq0].
      split; [left|]; specialize (atan2Q4 _ _ x1gt0 yqd) as [rngl rngu];assumption.
      rewrite <- x1eq0; rewrite (atan2_mPI2 _ yqd); split;
        [right; setl (-PI/2); reflexivity|
         apply (Rmult_lt_reg_r 2); [lra | setl (-PI); setr 0; lra]]. }
    
    rewrite k2def in rng.
    inversion_clear rng as [rlb rub].

    destruct ((n - k)%Z).
       ++ assert (IZR (2 * 0 + 1) = 1) as IZRid;
            [rewrite plus_IZR, mult_IZR; field
            |rewrite IZRid in *].
           lra.
           
       ++ assert (1 <= IZR (2 * (Z.pos p) + 1)) as IZRid. {
            rewrite plus_IZR, mult_IZR.
            assert (1 <= IZR (Z.pos p)).
            specialize (Pos2Z.is_pos p) as zltp.
            apply IZR_le. omega. lra. }
          apply (Rmult_le_compat_r (PI)) in IZRid; lra. 
           
       ++ assert (2*Z.neg p + 1 <= -1)%Z as bnd. {
            rewrite <- Pos2Z.opp_pos.
            assert (Z.pos p <> 0)%Z as pne0. discriminate.
            specialize (Pos2Z.is_nonneg p) as pge0.
            assert (1 <= Z.pos p)%Z as pge1. lia.
            lia. }
          destruct (Z.eq_dec (-1)%Z (Z.neg p)).
          rewrite <- e in *.
          assert (PI + IZR (2 * -1 + 1) * PI = 0) as id;
            [rewrite plus_IZR, mult_IZR; field| rewrite id in *; clear id].
          clear - rub pigt0. lra.
          
          assert (2 * Z.neg p + 1 <= -2)%Z as plen2; try lia.
          apply IZR_le in plen2. clear bnd n0.
          apply (Rmult_le_compat_r PI) in plen2.
          apply (Rplus_le_compat_l PI) in plen2.
          clear - rlb plen2 pigt0. lra. left. assumption.
Qed.

Lemma negroot_even_Q4_rpos :
  forall x₁ y₁ r θ
         (x1quad :  0 <= x₁)
         (y1pos : y₁ < 0)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 4. intros k2vale.
  
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
  inversion_clear k2vale as [n k2val].
  exists (2*n)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. split. setl (- (2*PI)/2). assumption.
  setr (2*PI/2). assumption.
  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id. field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k)) * PI) as id. {
  assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2.
  rewrite mult_IZR. field.
  rewrite id2. clear id2.
  fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k)) * PI)
               (θ + (IZR (2 * k) + IZR (2 * (n - k))) * PI).
  rewrite <- plus_IZR.
  assert ((2 * k + (2 * (n - k))) = 2 * n)%Z as id3. lia.
  rewrite id3. clear id3. reflexivity. }
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k)) * PI) in k2def.
  clear slb sub.

  generalize phase. intro phaseb.
  unfold straight, Tcx, Tcy in phase.
  assert ((PI / 2 + 0) = PI/2) as id. field. rewrite id in phase. clear id.
  rewrite cos_PI2, sin_PI2 in phase.
  assert (x₁ - (0 + r * 0) = x₁) as id. field.
  rewrite id in phase. clear id.
  assert (y₁ - (0 + r * 1) = y₁ - r) as id. field.
  rewrite id in phase. clear id.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id. unfold Rsqr. field.
    rewrite id in phase. clear id.
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def.
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption.
    assert (y₁ = r * (1-cos q)) as y1def.
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption.
    rewrite x1def, y1def in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id.
    unfold Rsqr.
    setl (r * r * (sin q * sin q + cos q * cos q - 1)).
    change (r * r * ((sin q)² + (cos q)² - 1) = 0).
    rewrite sin2_cos2. field.
    rewrite id in phase. lra. }
  
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k))%Z. assumption.

  assert (r<>0) as rne0; [intro; subst; lra|].
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  assert (q <> 0) as qne0. {
    intro qeq0. rewrite qeq0 in *.
    unfold κ₂ in k2def.
    autorewrite with null in k2def.
    rewrite Rminus_eq_0 in k2def.
    autorewrite with null in k2def.
    
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra. }
    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].
    
    assert (- 2 < 2 * (n - k))%Z as Zlb. {
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)). assumption. 
      lra.  }
      
    assert (2 * (n - k) <= 1)%Z as Zub. {
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)). assumption.
      arn.
      assumption. }
    
    assert ((n-k)%Z = 0%Z) as nmkeq0;
     [lia| rewrite nmkeq0 in k2def; clear nmkeq0].
    autorewrite with null in k2def.
    clear Zlb Zub at2ub at2lb.
    specialize (atan2_0_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra. }
  
  inversion_clear qrng as [qlb qub].
  
  inversion_clear qub as [qltPI | qeqPI].
  + apply k_deriv_sign_quad2 in s0; auto; [|intro; lra].
    inversion_clear s0 as [q2n | q2p].
    ++ exists (-k)%Z.
       rewrite <- q2n. unfold q.
       rewrite mult_IZR,opp_IZR. field.

    ++ exfalso.
       assert (0 < q) as qlt0. {
         apply (Rmult_lt_reg_r (/2)). apply Rinv_0_lt_compat. lra.
         setl 0. setr (q/2).
         rewrite q2p.

         assert (0 < 2 * r - y₁) as denpos. {
           apply (Rplus_lt_reg_r (y₁)). setl y₁. setr (2*r).
           apply (Rlt_trans _ 0). assumption. lra. }

         assert (0 < x₁² - (2 * r - y₁) * y₁) as argnn. {
           rewrite <- pm.
           apply Rplus_le_lt_0_compat.
           zltab.
           setr ((2 * r - y₁) * - y₁).
           zltab. }

         rewrite <- atan_0.
         apply atan_increasing.
         apply (Rmult_lt_reg_r (2 * r - y₁)); [assumption|].
         setl 0.
         setr ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))).
         lra.
         apply Rplus_le_lt_0_compat; try assumption.
         apply sqrt_lt_R0; try assumption. }
       
       clear qlb q2p.
       assert (-PI < κ₂ x₁ y₁ r q < 0) as [k2rngl k2rngu]. {
       unfold κ₂.
       split. apply (atan2_bound _ _ noton).
       assert (y₁ - r * (1 - cos q) < 0) as yneg.
       apply (Rplus_lt_reg_r (r * (1 - cos q))).
       setr (r * (1 - cos q)). setl y₁.
       apply (Rlt_le_trans _ 0). assumption.
       specialize (COS_bound q) as [cbql cbqu].
       apply Rmult_le_pos. left. assumption.
       lra.
       destruct (Rlt_dec 0 (x₁ - r * sin q)).
       apply atan2Q4; try assumption.
       apply Rnot_lt_le in n0.
       inversion_clear n0 as [xlt0 |xeq0].
       apply (Rlt_trans _ (-(PI/2))).
       apply atan2Q3; try assumption. lra.
       rewrite xeq0.
       rewrite atan2_mPI2; try assumption.
       apply (Rmult_lt_reg_r 2). lra. setr 0. setl (-PI).
       lra. }

       rewrite k2def in k2rngl, k2rngu.
       destruct (n-k)%Z.
       +++ assert (IZR (2 * 0) = 0) as IZRid.
           rewrite mult_IZR. field.
           rewrite IZRid in *.
           lra.
           
       +++ assert (2 <= IZR (2 * (Z.pos p))) as IZRid. {
             rewrite mult_IZR.
             specialize (IZRposge1 p) as pospos.
             lra. }
           apply (Rmult_le_compat_r (PI)) in IZRid;
           lra. 
           
       +++ assert (IZR (2 * Z.neg p) <= -2 ) as negtm. {
           rewrite mult_IZR.
           specialize (IZRneglen1 p) as negneg.

           apply (Rle_trans _ (2 * (- 1))).
           apply (Rmult_le_reg_r (/2)).
           apply Rinv_0_lt_compat. lra.
           setr (-1). setl (IZR (Z.neg p)). assumption.
           lra. }
           
           apply (Rmult_le_compat_r PI) in negtm.
           lra. left. assumption.

  + exfalso. clear qlb qne0.
    unfold κ₂ in k2def.
    rewrite qeqPI in *.
    rewrite sin_PI, cos_PI in *.
    
    assert (y₁ - r * (1 - - 1) = y₁ - 2*r) as y1def. field.
    assert (x₁ - r * 0 = x₁) as x1def. field.
    rewrite y1def, x1def in *.
    clear y1def x1def.

    assert (y₁ - 2 * r < 0) as yqd; try lra.
    assert (- (PI / 2) <= atan2 (y₁ - 2 * r) (x₁) < 0) as rng. {
      inversion_clear x1quad as [x1gt0 | x1eq0].
      split; [left|]; specialize (atan2Q4 _ _ x1gt0 yqd) as [rngl rngu];assumption.
      rewrite <- x1eq0; rewrite (atan2_mPI2 _ yqd); split;
        [right; setl (-PI/2); reflexivity|
         apply (Rmult_lt_reg_r 2); [lra | setl (-PI); setr 0; lra]]. }
    
    rewrite k2def in rng.
    inversion_clear rng as [rlb rub].

    destruct ((n - k)%Z).
       ++ assert (IZR (2 * 0) = 0) as IZRid;
            [rewrite mult_IZR; field
            |rewrite IZRid in *].
           lra.
           
       ++ assert (0 <= IZR (2 * (Z.pos p))) as IZRid. {
            rewrite mult_IZR.
            assert (1 <= IZR (Z.pos p)).
            specialize (Pos2Z.is_pos p) as zltp.
            apply IZR_le. omega. lra. }
          apply (Rmult_le_compat_r (PI)) in IZRid; lra. 
           
       ++ assert (2*Z.neg p <= -2)%Z as bnd. {
            rewrite <- Pos2Z.opp_pos.
            assert (Z.pos p <> 0)%Z as pne0. discriminate.
            specialize (Pos2Z.is_nonneg p) as pge0.
            assert (1 <= Z.pos p)%Z as pge1. lia.
            lia. }

          destruct (Z.eq_dec (-1)%Z (Z.neg p)).
          rewrite <- e in *.
          assert (PI + IZR (2 * -1) * PI = - PI) as id;
            [rewrite mult_IZR; field| rewrite id in *; clear id].
          clear - rlb pigt0.
          lra.

          assert (2 * Z.neg p <= -4)%Z as plen2; try lia.
          apply IZR_le in plen2. clear bnd n0.
          apply (Rmult_le_compat_r PI) in plen2.
          apply (Rplus_le_compat_l PI) in plen2.
          clear - rlb plen2 pigt0.
          lra. left. assumption.
Qed.

Lemma posroot_odd_xaxispos_rpos :
  forall x₁ y₁ r θ
         (y1def :  y₁ = 0)
         (x1quad :  0 < x₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan (x₁ / r) + IZR (2 * m) * PI.
Proof.
  intros until 4. intros k2vale.
  
  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. split. setl (- (2*PI)/2). assumption.
  setr (2*PI/2). assumption.

  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id; try field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n + 1) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k) + 1) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2.
    rewrite mult_IZR. field.
    rewrite id2. clear id2.
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k) + 1) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k) + 1)) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k) + 1)) = 2 * n + 1)%Z as id3. lia.
    rewrite id3. clear id3. reflexivity. }
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k) + 1) * PI) in k2def.
  clear slb sub.

  specialize (straight_std_impl_ineq _ _ _ phase) as phaseb.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id;
      [unfold Rsqr; field| rewrite id in phaseb; clear id].
    rewrite <- (Rplus_0_l r²) in phaseb at 1.
    apply RIneq.Rplus_lt_reg_r in phaseb.
    assert (x₁ = r * sin q) as x1def. {
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption. }
    assert (y₁ = r * (1-cos q)) as y1def'. {
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption. }
    rewrite x1def, y1def' in phaseb.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id. {
      unfold Rsqr.
      setl (r * r * (sin q * sin q + cos q * cos q - 1)).
      change (r * r * ((sin q)² + (cos q)² - 1) = 0).
      rewrite sin2_cos2. field. }
    rewrite id in phaseb. lra.
  }
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k) + 1)%Z. assumption.
  
  assert (r<>0) as rne0; [intro; subst; lra|].
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

 
  assert (q <> 0) as qne0. {
    intro qeq0. rewrite qeq0 in *.
    unfold κ₂ in k2def.
    rewrite sin_0, cos_0 in k2def.
    
    assert (y₁ - r * (1 - 1) = y₁) as y1def'; try field.
    assert (x₁ - r * 0 = x₁) as x1def; try field.
    rewrite y1def', x1def in k2def.
    rewrite Rplus_0_l in k2def.
    
    assert (~ (x₁ = 0 /\ y₁ = 0)) as notO. {
      intro. inversion_clear H as [xO yO].
      rewrite xO, yO in *. lra. }
    specialize (atan2_bound _ _ notO) as at2bnd.
    rewrite k2def in at2bnd.
    inversion_clear at2bnd as [at2lb at2ub].
    
    assert (- 1 < 2 * (n - k) + 1)%Z as Zlb. {
      apply lt_IZR.
      apply (Rmult_lt_reg_r (PI)). assumption. setl (-PI).
      assumption. }
      
    assert (2 * (n - k) + 1 <= 1)%Z as Zub. {
      apply le_IZR.
      apply (Rmult_le_reg_r (PI)). assumption. setr (PI).
      assumption. }
      
    assert ((n-k)%Z = 0%Z) as nmkeq0; try lia.
    rewrite nmkeq0 in k2def. clear nmkeq0.
    assert ((2 * 0 + 1)%Z = 1%Z) as id; try lia.
    rewrite id in k2def. clear id.
    assert (1 * PI = PI) as id. field. rewrite id in k2def. clear id.
    clear Zlb Zub at2ub at2lb y1def x1def.
    specialize (atan2_PI_impl _ _ notO k2def) as [xb yb].
    rewrite yb in *. lra.
  }

  assert (y₁ - r * (1 - cos q) <= 0) as xnpos. {
    rewrite y1def.
    specialize (COS_bound q) as [clb cub].
    setl (- (r * (1 - cos q))). setr (-0).
    apply Ropp_le_contravar.
    apply Rmult_le_pos. left. assumption. lra. }
  
  inversion_clear xnpos as [xnlt0 |xneq0].
  + assert (κ₂ x₁ y₁ r q < 0) as k2lt0. {
      unfold κ₂. 
      destruct (Rlt_dec 0 (x₁ - r * sin q)).
      ++ apply (atan2Q4 _ _ r0 xnlt0).
      ++ apply Rnot_lt_le in n0.
         inversion_clear n0 as [xalt0 |xaeq0].
         +++ apply (Rlt_trans _ (-(PI/2))).
             apply (atan2Q3 _ _ xalt0 xnlt0).
             lra.
         +++ rewrite xaeq0.
             rewrite atan2_mPI2.
             apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr 0.
             lra. assumption.
    }
    specialize (atan2_bound _ _ noton) as [at2lb at2ub].
    clear at2ub. change (- PI < κ₂ x₁ y₁ r q) in at2lb.
    rewrite k2def in at2lb,k2lt0.

    inversion_clear qrng as [qlb qub].
    destruct (n - k)%Z.
    ++ assert (IZR (2 * 0 + 1) = 1) as IZRid. {
         rewrite plus_IZR, mult_IZR. field. }
       rewrite IZRid in *.
       lra.
           
    ++ assert (1 <= IZR (2 * (Z.pos p) + 1)) as IZRid. {
         rewrite plus_IZR, mult_IZR.
         assert (1 <= IZR (Z.pos p)).
         specialize (Pos2Z.is_pos p) as zltp.
         apply IZR_le. omega. lra. }
       apply (Rmult_le_compat_r (PI)) in IZRid.
       lra. lra.
           
    ++ assert (2*Z.neg p + 1 <= -1)%Z as bnd. {
         rewrite <- Pos2Z.opp_pos.
         assert (Z.pos p <> 0)%Z as pne0. discriminate.
         specialize (Pos2Z.is_nonneg p) as pge0.
         assert (1 <= Z.pos p)%Z as pge1. lia.
         lia. }
       
       destruct (Z.eq_dec (-1)%Z (Z.neg p)).
       +++ rewrite <- e in *.
           assert (q + IZR (2 * -1 + 1) * PI = q - PI) as id.
           rewrite plus_IZR, mult_IZR. field. rewrite id in *. clear id.

           inversion_clear qub as [qltPI| qeqPI].
           ++++ exists (-k)%Z.
                apply k_deriv_sign_lin_rpos3 in s0;
                  ((split; assumption) || lra || assumption || idtac).
                rewrite <- s0. unfold q.
                rewrite mult_IZR, opp_IZR. field.
           ++++ exfalso. rewrite qeqPI in k2lt0. lra.
                
       +++ exfalso.
           assert (2 * Z.neg p + 1 <= -2)%Z as plen2; try lia.
           apply IZR_le in plen2. clear bnd n0.
           apply (Rmult_le_compat_r PI) in plen2.
           apply (Rplus_le_compat_l q) in plen2.
           clear - at2lb plen2 pigt0 qlb qub. lra.
           left. assumption.
           
  + exfalso.
    assert (cos q = 1) as cosqeq1. {
      symmetry.
      apply (Rplus_eq_reg_r (- cos q)).
      apply (Rmult_eq_reg_l (-r)).
      apply (Rplus_eq_reg_l (y₁)). setl (y₁ - r * (1 - cos q)).
      rewrite y1def at 2. setr 0. assumption.
      apply Ropp_neq_0_compat. assumption. }
    
    inversion_clear qrng as [qlb qub].
    destruct (Rle_dec 0 q).
    apply qne0.
    apply cosθeq1; try assumption. split; lra.
    apply Rnot_le_lt in n0. clear qub.
    
    rewrite <- (cos_period1 _ 1) in cosqeq1.
    assert (0 <= q + 2 * 1 * PI < 2*PI) as qrng2.
    split; lra.
    specialize (cosθeq1 _ qrng2 cosqeq1) as qeqn2PI; try assumption.
    lra.
Qed.

Lemma negroot_even_xaxispos_rpos :
  forall x₁ y₁ r θ
         (y1def :  y₁ = 0)
         (x1quad :  0 < x₁)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = IZR (2 * m) * PI. 
Proof.
  intros until 4. intros k2vale.
  
  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0. lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. split. setl (- (2*PI)/2). assumption.
  setr (2*PI/2). assumption.

  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id; try field.
  rewrite id in k2def. clear id.
  assert (θ + IZR (2 * n) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k)) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2.
    rewrite mult_IZR. field.
    rewrite id2. clear id2.
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k)) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k))) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k))) = 2 * n)%Z as id3. lia.
    rewrite id3. clear id3. reflexivity. }
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k)) * PI) in k2def.
  clear slb sub.

  specialize (straight_std_impl_ineq _ _ _ phase) as phaseb.

  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].

    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id;
      [unfold Rsqr; field| rewrite id in phaseb; clear id].
    rewrite <- (Rplus_0_l r²) in phaseb at 1.
    apply RIneq.Rplus_lt_reg_r in phaseb.

    assert (x₁ = r * sin q) as x1def. {
    apply (Rplus_eq_reg_r (- r * sin q)).
    setr 0. setl (x₁ - r * sin q). assumption. }
    assert (y₁ = r * (1-cos q)) as y1def'. {
    apply (Rplus_eq_reg_r (- r * (1-cos q))).
    setr 0. setl (y₁ - r * (1-cos q)). assumption. }
    rewrite x1def, y1def' in phaseb.

    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id. {
      unfold Rsqr.
      setl (r * r * (sin q * sin q + cos q * cos q - 1)).
      change (r * r * ((sin q)² + (cos q)² - 1) = 0).
      rewrite sin2_cos2. field. }
    rewrite id in phaseb.
    lra.
  }
  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k))%Z. assumption.
  
  assert (r<>0) as rne0; [intro; subst; lra|].
  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  destruct (Req_dec q 0) as [qeq0|qne0].
  + unfold q in qeq0.
    exists (-k)%Z.
    rewrite Rplus_comm in qeq0.
    apply Rplus_opp_r_uniq in qeq0.
    rewrite qeq0, mult_IZR, opp_IZR.
    field.

  + assert (y₁ - r * (1 - cos q) <= 0) as xnpos. {
      rewrite y1def.
      specialize (COS_bound q) as [clb cub].
      setl (- (r * (1 - cos q))). setr (-0).
      apply Ropp_le_contravar.
      apply Rmult_le_pos. left. assumption. lra. }
  
    destruct xnpos as [xnlt0 |xneq0].
    ++ assert (κ₂ x₁ y₁ r q < 0) as k2lt0. {
         unfold κ₂. 
         destruct (Rlt_dec 0 (x₁ - r * sin q)).
         +++ apply (atan2Q4 _ _ r0 xnlt0).
         +++ apply Rnot_lt_le in n0.
            inversion_clear n0 as [xalt0 |xaeq0].
            ++++ apply (Rlt_trans _ (-(PI/2))).
                 apply (atan2Q3 _ _ xalt0 xnlt0).
                 lra.
            ++++ rewrite xaeq0.
                 rewrite atan2_mPI2.
                 apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr 0.
                 lra. assumption.
       }
       specialize (atan2_bound _ _ noton) as [at2lb at2ub].
       clear at2ub. change (- PI < κ₂ x₁ y₁ r q) in at2lb.
       rewrite k2def in at2lb,k2lt0.

       rewrite (k'_periodic _ _ _ (n-k)%Z) in s0.
       rewrite mult_IZR in at2lb, k2lt0.
       apply k_deriv_sign_lin_rpos3 in s0;
         [| split; lra|assumption |assumption |lra | assumption].
       assert (0 < atan (x₁ / r)) as atpos. {
         rewrite <- atan_0.
         apply atan_increasing.
         rewrite <- RmultRinv.
         zltab. }
       rewrite <- s0 in atpos.
       clear - atpos k2lt0.
       lra.
    ++ unfold κ₂ in k2def.
       rewrite xneq0 in k2def.
       destruct (Rlt_dec 0 (x₁ - r * sin q)) as [xd|xd].
       +++ rewrite atan2_0 in k2def; try assumption.
           unfold q in k2def.
           exists (-n)%Z.
           rewrite mult_IZR, opp_IZR.
           apply (Rplus_eq_reg_r (IZR k * (2 * PI) + IZR (2 * (n - k)) * PI)).
           rewrite mult_IZR at 2.
           rewrite minus_IZR.
           setr 0.
           symmetry.
           rewrite <- Rplus_assoc.
           assumption.
       +++ apply Rnot_lt_le in xd.
           rewrite y1def in xneq0.
           assert (cos q = 1) as cosqeq1. {
             apply (Rplus_eq_reg_r (- cos q)).
             repeat rewrite pm.
             apply (Rmult_eq_reg_l (- r)).
             symmetry.
             setr 0.
             autorewrite with null in xneq0.
             lrag xneq0.
             lra. }
           specialize (inrange_0T q _ tPIgt0) as [v vrng].
           rewrite <- (cos_period1 _ v), (Rmult_comm 2), Rmult_assoc in cosqeq1.
           apply cosθeq1 in cosqeq1; try assumption.
           unfold q in cosqeq1.
           exists (-k -v)%Z.
           rewrite mult_IZR, minus_IZR, opp_IZR.
           rewrite Rplus_assoc, Rplus_comm in cosqeq1.
           apply Rplus_opp_r_uniq in cosqeq1.
           rewrite cosqeq1.
           field.
Qed.

Lemma posroot_odd_xaxisnpos_rpos :
  forall x₁ y₁ r θ
         (y1def :  y₁ = 0)
         (x1quad :  x₁ <= 0)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = IZR (2 * m) * PI.
Proof.
  intros until 4. intros k2vale.
  
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n+1)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0; try lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. {
    split. setl (- (2*PI)/2). assumption.
    setr (2*PI/2). assumption. }

  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id;
    [field|  rewrite id in k2def; clear id].
  assert (θ + IZR (2 * n + 1) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k) + 1) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2. {
      rewrite mult_IZR. field. }
    rewrite id2. clear id2.
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k) + 1) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k) + 1)) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k) + 1)) = 2 * n + 1)%Z as id3. omega.
    rewrite id3. clear id3. reflexivity. }
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k) + 1) * PI) in k2def.
  clear slb sub.

  rename phase into phaseb.
  specialize (straight_std_impl_ineq _ _ _ phaseb) as phase.


  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id;
      [unfold Rsqr;field| rewrite id in phase; clear id].
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def. {
      apply (Rplus_eq_reg_r (- r * sin q)).
      setr 0. setl (x₁ - r * sin q). assumption. }
    assert (y₁ = r * (1-cos q)) as y1def'. {
      apply (Rplus_eq_reg_r (- r * (1-cos q))).
      setr 0. setl (y₁ - r * (1-cos q)). assumption. }
    rewrite x1def, y1def' in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id. {
      unfold Rsqr.
      setl (r * r * (sin q * sin q + cos q * cos q - 1)).
      change (r * r * ((sin q)² + (cos q)² - 1) = 0).
      rewrite sin2_cos2. field. }
    rewrite id in phase. lra.
  }

  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k) + 1)%Z. assumption.

  assert (r<>0) as rne0. {
    intro. subst. lra. }

  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  inversion_clear qrng as [qlb qub].

  destruct (Req_dec q 0) as [qeq0 | qne0].
  + unfold q in qeq0.
    exists (-k)%Z.
    rewrite mult_IZR, opp_IZR.
    apply (Rplus_eq_reg_r (IZR k * (2 * PI))).
    setr 0. assumption.

  + assert (y₁ - r * (1 - cos q) <= 0) as xnpos. {
      rewrite y1def.
      specialize (COS_bound q) as [clb cub].
      setl (- (r * (1 - cos q))). setr (-0).
      apply Ropp_le_contravar.
      apply Rmult_le_pos. left. assumption. lra. }
    
    inversion_clear xnpos as [xnlt0 |xneq0].
    ++ assert (κ₂ x₁ y₁ r q < 0) as k2lt0. {
         unfold κ₂. 
         destruct (Rlt_dec 0 (x₁ - r * sin q)).
         apply (atan2Q4 _ _ r0 xnlt0).
         apply Rnot_lt_le in n0.
         inversion_clear n0 as [xalt0 |xaeq0].
         apply (Rlt_trans _ (-(PI/2))).
         apply (atan2Q3 _ _ xalt0 xnlt0).
         lra. rewrite xaeq0.
         rewrite atan2_mPI2.
         apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr 0.
         lra. assumption.
       }
       specialize (atan2_bound _ _ noton) as [at2lb at2ub].
       clear at2ub. change (- PI < κ₂ x₁ y₁ r q) in at2lb.
       rewrite k2def in at2lb,k2lt0.

       destruct (n - k)%Z.
       +++  assert (IZR (2 * 0 + 1) = 1) as IZRid.
            rewrite plus_IZR, mult_IZR. field.
            rewrite IZRid in *.
            lra.
           
       +++ assert (1 <= IZR (2 * (Z.pos p) + 1)) as IZRid.
           rewrite plus_IZR, mult_IZR.
           specialize (IZRposge1 p) as pospos.
           lra.
           apply (Rmult_le_compat_r (PI)) in IZRid;
           lra.
           
       +++ assert (2*Z.neg p + 1 <= -1)%Z as bnd. {
             rewrite <- Pos2Z.opp_pos.
             assert (Z.pos p <> 0)%Z as pne0. discriminate.
             specialize (Pos2Z.is_nonneg p) as pge0.
             assert (1 <= Z.pos p)%Z as pge1; lia. }
           
           destruct (Z.eq_dec (-1)%Z (Z.neg p)).
           ++++ rewrite <- e in *.
                assert (q + IZR (2 * -1 + 1) * PI = q - PI) as id.
                rewrite plus_IZR, mult_IZR. field. rewrite id in *. clear id.
                
                inversion_clear qub as [qltPI| qeqPI].
                +++++ exfalso.
                assert (0 < q) as zltq; try lra.
                clear e bnd k2lt0 at2lb qlb.
                
                apply k_deriv_sign_lin_rpos3 in s0;
                  ((split; assumption) || lra || assumption || idtac).
                inversion_clear x1quad as [x1lt0 |x1eq0].
                assert (q < 0) as qle0. {
                  apply (Rmult_lt_reg_r (/2)).
                  apply Rinv_0_lt_compat. lra. setr 0. setl (q/2).
                  rewrite s0. rewrite <- atan_0.
                  apply atan_increasing.
                  apply (Rmult_lt_reg_r r); try assumption. setr 0. setl x₁.
                  intro. lra. assumption. }
                clear - qle0 zltq. lra.
                assert (q = 0) as qeq0. {
                  apply (Rmult_eq_reg_r (/2)); [|apply Rinv_neq_0_compat; discrR].
                  setr 0. setl (q/2).
                  rewrite <- atan_0.
                  assert (0 = x₁/r) as id. rewrite x1eq0. field. intro. lra.
                  rewrite id. assumption. }
                lra.
                  
                +++++ exfalso. rewrite qeqPI in k2lt0. lra.
                
           ++++ exfalso.
                assert (2 * Z.neg p + 1 <= -2)%Z as plen2. lia.
                apply IZR_le in plen2. clear bnd n0.
                apply (Rmult_le_compat_r PI) in plen2.
                apply (Rplus_le_compat_l q) in plen2.
                clear - at2lb plen2 pigt0 qlb qub. lra. left.
                assumption.
                
    ++ exfalso.
       assert (cos q = 1) as cosqeq1. symmetry.
       apply (Rplus_eq_reg_r (- cos q)).
       apply (Rmult_eq_reg_l (-r)).
       apply (Rplus_eq_reg_l (y₁)). setl (y₁ - r * (1 - cos q)).
       rewrite y1def at 2. setr 0. assumption.
       apply Ropp_neq_0_compat. assumption.
       
       destruct (Rle_dec 0 q).
       apply qne0.
       apply cosθeq1; try assumption. split; lra.
       apply Rnot_le_lt in n0. clear qub.
       
       rewrite <- (cos_period1 _ 1) in cosqeq1.
       assert (0 <= q + 2 * 1 * PI < 2*PI) as qrng2.
       split; lra.
       specialize (cosθeq1 _ qrng2 cosqeq1) as qeqn2PI; try assumption.
       lra.
Qed.


Lemma negroot_even_xaxisnpos_rpos :
  forall x₁ y₁ r θ
         (y1def :  y₁ = 0)
         (x1quad :  x₁ <= 0)
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = 2 * atan (x₁ / r) + IZR (2 * m) * PI.
Proof.
  intros until 4. intros k2vale.
  
  assert (exists p : Z, κ₂ x₁ y₁ r θ = θ + IZR p * PI) as k2valp. {
    inversion_clear k2vale as [n k2val].
    exists (2*n)%Z. assumption. }

  specialize PI_RGT_0 as pigt0.
  assert (2*PI > 0) as tPIgt0; try lra.

  specialize (inrange_mT2T2 θ (2*PI) tPIgt0) as [k [slb sub]].
  set (q := θ + IZR k * (2*PI)) in *.
  assert (- PI < q <= PI) as qrng. {
    split. setl (- (2*PI)/2). assumption.
    setr (2*PI/2). assumption. }

  inversion k2vale as [n k2def].
  rewrite (k2_periodic _ _ _ k) in k2def.
  assert (θ + 2 * IZR k * PI = θ + IZR k * (2 * PI)) as id;
    [field |  rewrite id in k2def; clear id].
  assert (θ + IZR (2 * n) * PI =
          (θ + IZR k * (2 * PI)) + IZR (2 * (n-k)) * PI) as id. {
    assert (IZR k * (2 * PI) = IZR (2*k) * PI) as id2. {
      rewrite mult_IZR. field. }
    rewrite id2. clear id2.
    fieldrewrite (θ + IZR (2 * k) * PI + IZR (2 * (n - k)) * PI)
                 (θ + (IZR (2 * k) + IZR (2 * (n - k))) * PI).
    rewrite <- plus_IZR.
    assert ((2 * k + (2 * (n - k))) = 2 * n)%Z as id3. lia.
    rewrite id3. clear id3. reflexivity. }
  rewrite id in k2def. clear id.
  change (κ₂ x₁ y₁ r q = q + IZR (2 * (n-k)) * PI) in k2def.
  clear slb sub.

  rename phase into phaseb.
  specialize (straight_std_impl_ineq _ _ _ phaseb) as phase.


  assert (~ (x₁ - r * sin q = 0 /\ y₁ - r * (1 - cos q) = 0)) as noton. {
    intro notx1y1.
    inversion_clear notx1y1 as [notx1 noty1].
    
    assert (x₁² + (y₁ - r)² = x₁² - (2 * r - y₁) * y₁ + r²) as id;
      [unfold Rsqr;field| rewrite id in phase; clear id].
    rewrite <- (Rplus_0_l r²) in phase at 1.
    apply RIneq.Rplus_lt_reg_r in phase.
    assert (x₁ = r * sin q) as x1def. {
      apply (Rplus_eq_reg_r (- r * sin q)).
      setr 0. setl (x₁ - r * sin q). assumption. }
    assert (y₁ = r * (1-cos q)) as y1def'. {
      apply (Rplus_eq_reg_r (- r * (1-cos q))).
      setr 0. setl (y₁ - r * (1-cos q)). assumption. }
    rewrite x1def, y1def' in phase.
    assert ((r * sin q)² - (2 * r - r * (1 - cos q)) * (r * (1 - cos q)) = 0) as id. {
      unfold Rsqr.
      setl (r * r * (sin q * sin q + cos q * cos q - 1)).
      change (r * r * ((sin q)² + (cos q)² - 1) = 0).
      rewrite sin2_cos2. field. }
    rewrite id in phase. lra.
  }

  assert (exists p : Z, κ₂ x₁ y₁ r q = q + IZR p * PI) as k2defp.
  exists (2* (n-k))%Z. assumption.

  assert (r<>0) as rne0. {
    intro. subst. lra. }

  rewrite <- (k_extrema_vals _ _ _ _ qrng rne0 noton) in k2defp.
  specialize sign_0 as s0.
  rewrite <- k2defp in s0 at 1.

  inversion_clear qrng as [qlb qub].

  destruct (Req_dec q 0) as [qeq0 | qne0].
  + exfalso.
    rewrite qeq0 in *.
    unfold κ₂ in k2def.
    autorewrite with null in k2def.
    rewrite Rminus_eq_0 in k2def.
    autorewrite with null in k2def.
    rewrite y1def in k2def.
    destruct x1quad as [x1lt0 | x1eq0].
    ++ rewrite atan2_PI, mult_IZR in k2def; try assumption.
       assert (1 = 2 * (n - k))%Z as contra. {
         apply eq_IZR.
         apply (Rmult_eq_reg_r PI); try lra.
         arn.
         rewrite mult_IZR.
         assumption. }
       lia.
    ++ rewrite y1def, x1eq0 in *.
       autorewrite with null in phase.
       rewrite <- Rsqr_neg in phase.
       lra.
  + assert (y₁ - r * (1 - cos q) <= 0) as xnpos. {
      rewrite y1def.
      specialize (COS_bound q) as [clb cub].
      setl (- (r * (1 - cos q))). setr (-0).
      apply Ropp_le_contravar.
      apply Rmult_le_pos. left. assumption. lra. }
    
    inversion_clear xnpos as [xnlt0 |xneq0].
    ++ assert (κ₂ x₁ y₁ r q < 0) as k2lt0. {
         unfold κ₂. 
         destruct (Rlt_dec 0 (x₁ - r * sin q)).
         apply (atan2Q4 _ _ r0 xnlt0).
         apply Rnot_lt_le in n0.
         inversion_clear n0 as [xalt0 |xaeq0].
         apply (Rlt_trans _ (-(PI/2))).
         apply (atan2Q3 _ _ xalt0 xnlt0).
         lra. rewrite xaeq0.
         rewrite atan2_mPI2.
         apply (Rmult_lt_reg_r 2). lra. setl (-PI). setr 0.
         lra. assumption.
       }
       specialize (atan2_bound _ _ noton) as [at2lb at2ub].
       clear at2ub. change (- PI < κ₂ x₁ y₁ r q) in at2lb.
       rewrite k2def in at2lb,k2lt0.

       destruct qub as [qltPI | qeqPI].
       +++ apply k_deriv_sign_lin_rpos3 in s0;
             [rewrite <- s0;
              unfold q;
              exists (-k)%Z;
              rewrite mult_IZR, opp_IZR;
              field | split; assumption |
              assumption | assumption |
              assumption | assumption].
       +++ rewrite qeqPI, mult_IZR in *.
           destruct (n - k)%Z; autorewrite with null in *.
           ++++ lra.
           ++++ specialize (IZRposge1 p) as pospos.
                apply (Rmult_le_compat_r PI) in pospos; try lra.
           ++++ specialize (IZRneglen1 p) as pospos.
                apply (Rmult_le_compat_r PI) in pospos; try lra.
    ++ exfalso.
       assert (cos q = 1) as cosqeq1. symmetry.
       apply (Rplus_eq_reg_r (- cos q)).
       apply (Rmult_eq_reg_l (-r)).
       apply (Rplus_eq_reg_l (y₁)). setl (y₁ - r * (1 - cos q)).
       rewrite y1def at 2. setr 0. assumption.
       apply Ropp_neq_0_compat. assumption.
       
       destruct (Rle_dec 0 q).
       apply qne0.
       apply cosθeq1; try assumption. split; lra.
       apply Rnot_le_lt in n0. clear qub.
       
       rewrite <- (cos_period1 _ 1) in cosqeq1.
       assert (0 <= q + 2 * 1 * PI < 2*PI) as qrng2.
       split; lra.
       specialize (cosθeq1 _ qrng2 cosqeq1) as qeqn2PI; try assumption.
       lra.
Qed.


Lemma posroot_odd_rpos :
  forall x₁ y₁ r θ
         (cond : ~ (2 * r - y₁ = 0))
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))/(2 * r - y₁))  + 
          IZR (2 * m) * PI.
Proof.
  intros until 3. intros k2vale.

  destruct (Rlt_dec y₁ 0).
  + assert (0 < 2 * r - y₁) as denpos.
    apply (Rplus_lt_reg_r y₁).
    apply (Rlt_trans _ 0); lra. 

    destruct (Rlt_dec x₁ 0).
    ++ specialize (posroot_odd_Q3_rpos _ _ _ _ r1 r0 rgt0 phase k2vale)
        as [m tdef].
       exists m.
       rewrite tdef. reflexivity. 

    ++ apply Rnot_lt_le in n.

       assert (0 < x₁² - (2 * r - y₁) * y₁) as arggt0.
       setr (x₁² + (2 * r - y₁) * (-y₁)).
       apply Rplus_le_lt_0_compat. 
       apply Rle_0_sqr.
       apply Rmult_lt_0_compat. assumption. lra.
      
       specialize (posroot_odd_Q4_rpos
                     _ _ _ _ n r0 rgt0 phase k2vale)
         as [m tdef].
       exists m.
       rewrite tdef. reflexivity.

  + apply Rnot_lt_le in n.
    inversion_clear n as [zlty1 | zley1].

    ++ destruct (Rlt_dec (2*r - y₁) 0).
       +++ apply (posroot_odd_Q1Q2top_rpos
                         _ _ _ _ r0 zlty1 rgt0 phase k2vale).
       +++ apply Rnot_lt_le in n.
           inversion_clear n as [zltxarg | zeqxarg].
           ++++ destruct (Rlt_dec x₁ 0).
                apply (posroot_odd_Q2_rpos
                              _ _ _ _ r0 zltxarg zlty1 rgt0 phase k2vale).


                apply Rnot_lt_le in n.
                apply (posroot_odd_Q1_rpos _ _ _ _
                                           n zltxarg zlty1 rgt0 phase k2vale).

           ++++ symmetry in zeqxarg.
                exfalso. tauto.

    ++ clear cond.
       rewrite <- zley1.
       fieldrewrite (2 * r - 0) (2 * r).
       fieldrewrite (x₁² - 2 * r * 0) (x₁²).
       destruct (Rlt_dec 0 x₁).
       rewrite sqrt_Rsqr; [|left; assumption].
       fieldrewrite (x₁ + x₁) (2 * x₁).

       fieldrewrite (2 * x₁ / (2 * r)) (x₁ / r). intro. lra.
       symmetry in zley1.
       apply (posroot_odd_xaxispos_rpos _ _ _ _ zley1 r0 rgt0 phase k2vale).

       apply Rnot_lt_le in n.
       rewrite sqrt_Rsqr_abs.
       assert (x₁ + Rabs x₁ = 0) as id.
       inversion_clear n as [zltx1 | zeqx1].
       rewrite Rabs_left; [| assumption]. field.
       rewrite zeqx1. rewrite Rabs_R0. field.
       rewrite id. clear id.
       fieldrewrite (0 / (2 * r)) 0. intro; lra.
       rewrite atan_0. rewrite Rmult_0_r.
       cut (exists m : Z, θ = IZR (2 * m) * PI). intro rmz.
       inversion_clear rmz as [m td].
       exists m. rewrite (Rplus_0_l (IZR (2 * m) * PI)). assumption.

       eapply posroot_odd_xaxisnpos_rpos; try symmetry; eassumption.
Qed.



Lemma negroot_even_rpos :
  forall x₁ y₁ r θ
         (cond : ~ (2 * r - y₁ = 0))
         (rgt0 : 0 < r)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))/(2 * r - y₁))  + 
          IZR (2 * m) * PI.
Proof.
  intros until 3. intros k2vale.

  destruct (Rlt_dec y₁ 0).
  + assert (0 < 2 * r - y₁) as denpos.
    apply (Rplus_lt_reg_r y₁).
    apply (Rlt_trans _ 0); lra. 

    destruct (Rlt_dec x₁ 0).
    ++ specialize (negroot_even_Q3_rpos _ _ _ _ r1 r0 rgt0 phase k2vale)
        as [m tdef].
       exists m.
       rewrite tdef. reflexivity. 

    ++ apply Rnot_lt_le in n.

       assert (0 < x₁² - (2 * r - y₁) * y₁) as arggt0.
       setr (x₁² + (2 * r - y₁) * (-y₁)).
       apply Rplus_le_lt_0_compat. 
       apply Rle_0_sqr.
       apply Rmult_lt_0_compat. assumption. lra.
      
       specialize (negroot_even_Q4_rpos
                     _ _ _ _ n r0 rgt0 phase k2vale)
         as [m tdef].
       exists m.
       rewrite tdef. reflexivity.

  + apply Rnot_lt_le in n.
    inversion_clear n as [zlty1 | zley1].

    ++ destruct (Rlt_dec (2*r - y₁) 0).
       +++ apply (negroot_even_Q1Q2top_rpos
                         _ _ _ _ r0 zlty1 rgt0 phase k2vale).
       +++ apply Rnot_lt_le in n.
           inversion_clear n as [zltxarg | zeqxarg].
           ++++ destruct (Rlt_dec x₁ 0).
                apply (negroot_even_Q2_rpos
                              _ _ _ _ r0 zltxarg zlty1 rgt0 phase k2vale).


                apply Rnot_lt_le in n.
                apply (negroot_even_Q1_rpos _ _ _ _
                                           n zltxarg zlty1 rgt0 phase k2vale).

           ++++ symmetry in zeqxarg.
                exfalso. tauto.

    ++ clear cond.
       rewrite <- zley1.
       autorewrite with null.
       destruct (Rlt_dec 0 x₁).
       rewrite sqrt_Rsqr; [|left; assumption].
       fieldrewrite (x₁ - x₁) (0).
       rewrite <- RmultRinv.
       arn.
       rewrite atan_0.
       arn.
       assert (exists m : Z, θ = IZR (2 * m) * PI) as prime. {
         symmetry in zley1.
         apply (negroot_even_xaxispos_rpos _ _ _ _ zley1 r0 rgt0 phase k2vale). }
       destruct prime as [n prm].
       exists n.
       arn.
       assumption.

       apply Rnot_lt_le in n.
       rewrite sqrt_Rsqr_abs.
       assert (x₁ - Rabs x₁ = 2 * x₁) as id. {
       inversion_clear n as [zltx1 | zeqx1].
       rewrite Rabs_left; [| assumption]. field.
       rewrite zeqx1. rewrite Rabs_R0. field. }
       rewrite id. clear id.
       fieldrewrite (2 * x₁ / (2 * r)) (x₁ / r). intro; lra.
       eapply negroot_even_xaxisnpos_rpos; try symmetry; eassumption.
Qed.


Lemma posroot_odd_rneg :
  forall x₁ y₁ r θ
         (cond : ~ (2 * r - y₁ = 0))
         (rgt0 : r < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))/(2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 3. intro kdef.
  assert (0 < (-r)) as rgt0'. lra.
  assert (~((2 *(- r) -(- y₁) = 0))) as cond'.
  intro. apply cond. 
  rewrite <- Ropp_0. setl (-(2*(-r) - (-y₁))).
  rewrite H. reflexivity.
  
  assert ((x₁ - r * sin θ <= 0 /\ y₁ - r * (1 - cos θ) = 0) \/
          (~ (x₁ - r * sin θ <= 0 /\ y₁ - r * (1 - cos θ) = 0)))
    as [on |noton]. {
    destruct (Rle_dec (x₁ - r * sin θ) 0).
    destruct (Req_dec (y₁ - r * (1 - cos θ)) 0) as [yeq |yne].
    left; split; assumption.
    right. intro cnt. inversion_clear cnt as [xst yst].
    apply yne; assumption.
    right. intro cnt. inversion_clear cnt as [xst yst].
    apply n; assumption. }
  inversion_clear on as [xls yat].
  unfold κ₂ in kdef. rewrite yat in kdef.
  inversion_clear xls as [cst |ycst].
  specialize (atan2_PI _ cst) as kval.
  inversion_clear kdef as [n at2d].
  rewrite kval in at2d.

  rewrite plus_IZR, mult_IZR in at2d.
  assert (θ = 0 + 2 * IZR (-n) * PI) as tdef. {
    apply (Rplus_eq_reg_r ((2 * IZR n +1)* PI)).
    rewrite opp_IZR. setr PI. symmetry. assumption. }
  rewrite tdef in yat, cst.
  rewrite cos_period1, cos_0,Rminus_eq_0,Rmult_0_r,Rminus_0_r in yat.
  rewrite sin_period1, sin_0,Rmult_0_r,Rminus_0_r in cst.
  assert (x₁ + sqrt (x₁² - (2 * r - y₁) * y₁) = 0) as yz.
  rewrite yat.
  fieldrewrite (x₁² - (2 * r - 0) * 0) (x₁²).
  rewrite sqrt_Rsqr_abs.
  rewrite Rabs_left; [|assumption]. field. rewrite yz. clear yz.
  rewrite yat. fieldrewrite (2*r - 0) (2*r).
  assert (2*r < 0) as trlt0; try lra.
  fieldrewrite (0 / (2 * r)) 0. intro; lra.
  rewrite (atan_0), tdef.
  exists (-n)%Z.
  rewrite opp_IZR,mult_IZR, opp_IZR. field.

  exfalso.
  apply (straight_std_impl_ineq) in phase.
  assert (y₁ = r * (1-cos θ)) as xdef.
  apply (Rplus_eq_reg_r (-r*(1-cos θ))). setr 0. rewrite <- yat. field.
  assert (x₁ = r * sin θ) as ydef.
  apply (Rplus_eq_reg_r (-r*sin θ)). setr 0. rewrite <- ycst. field.
  rewrite ydef, xdef in phase.

  assert (r² < r²) as cont. {
  rewrite <- Rmult_1_l. rewrite Rmult_comm, <- (sin2_cos2 θ).
  setr ((r *sin θ)² + (r *cos θ)²).
  rewrite (Rsqr_neg (r * cos θ)).
  apply (Rlt_le_trans _ (x₁² + (- (r * cos θ))²)).
  fieldrewrite (- (r * cos θ)) (r * (1- cos θ) - r).
  rewrite ydef. assumption.
  rewrite ydef. right. reflexivity. } lra.
           
  
  apply straight_symmetry in phase.
  inversion_clear kdef as [n k2def].
  rewrite k2_symmetry in k2def; [|assumption].

  assert (exists m, κ₂ x₁ (- y₁) (- r) (- θ) = (-θ) + IZR (2 * m + 1) * PI) as k2def'. {
    exists (-n-1)%Z.
    rewrite plus_IZR, mult_IZR, minus_IZR, opp_IZR in *.
    apply (Rmult_eq_reg_l (-1)). setl (- κ₂ x₁ (- y₁) (- r) (- θ)).
    rewrite k2def. field. intro. lra. }
  rewrite Ropp_0 in *.
  specialize (posroot_odd_rpos _ _ _ _ cond' rgt0' phase k2def') as [p tdef].

  apply Ropp_eq_compat in tdef.
  rewrite Ropp_involutive in tdef.
  rewrite tdef.

  fieldrewrite (x₁² - (2 * - r - - y₁) * - y₁) (x₁² - (2 * r - y₁) * y₁).
  fieldrewrite (2 * - r - - y₁) (-(2 * r - y₁)).

  exists (-p)%Z.
  rewrite mult_IZR, mult_IZR, opp_IZR.
  fieldrewrite ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / - (2 * r - y₁))
               (- ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  assumption.
  rewrite atan_opp.
  field.
Qed.
  

Lemma negroot_even_rneg :
  forall x₁ y₁ r θ
         (cond : ~ (2 * r - y₁ = 0))
         (rgt0 : r < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))/(2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros until 3. intro kdef.
  assert (0 < (-r)) as rgt0'. lra.
  assert (~((2 *(- r) -(- y₁) = 0))) as cond'.
  intro. apply cond. 
  rewrite <- Ropp_0. setl (-(2*(-r) - (-y₁))).
  rewrite H. reflexivity.
  
  assert ((x₁ - r * sin θ <= 0 /\ y₁ - r * (1 - cos θ) = 0) \/
          (~ (x₁ - r * sin θ <= 0 /\ y₁ - r * (1 - cos θ) = 0)))
    as [on |noton]. {
    destruct (Rle_dec (x₁ - r * sin θ) 0).
    destruct (Req_dec (y₁ - r * (1 - cos θ)) 0) as [yeq |yne].
    left; split; assumption.
    right. intro cnt. inversion_clear cnt as [xst yst].
    apply yne; assumption.
    right. intro cnt. inversion_clear cnt as [xst yst].
    apply n; assumption. }
  inversion_clear on as [xls yat].
  unfold κ₂ in kdef. rewrite yat in kdef.
  inversion_clear xls as [cst |ycst].
  specialize (atan2_PI _ cst) as kval.
  inversion_clear kdef as [n at2d].
  rewrite kval in at2d.

  rewrite mult_IZR in at2d.
  assert (θ = PI + 2 * IZR (-n) * PI) as tdef. {
    apply (Rplus_eq_reg_r ((2 * IZR n)* PI)).
    rewrite opp_IZR.
    setr PI.
    symmetry.
    assumption. }

  rewrite tdef in yat, cst.
  rewrite cos_period1 in yat.
  rewrite sin_period1 in cst.
  autorewrite with null in *.
  assert (2 * r - y₁ = 0); try lra.

  exfalso.
  apply (straight_std_impl_ineq) in phase.
  assert (y₁ = r * (1-cos θ)) as xdef.
  apply (Rplus_eq_reg_r (-r*(1-cos θ))). setr 0. rewrite <- yat. field.
  assert (x₁ = r * sin θ) as ydef.
  apply (Rplus_eq_reg_r (-r*sin θ)). setr 0. rewrite <- ycst. field.
  rewrite ydef, xdef in phase.

  assert (r² < r²) as cont. {
  rewrite <- Rmult_1_l. rewrite Rmult_comm, <- (sin2_cos2 θ).
  setr ((r *sin θ)² + (r *cos θ)²).
  rewrite (Rsqr_neg (r * cos θ)).
  apply (Rlt_le_trans _ (x₁² + (- (r * cos θ))²)).
  fieldrewrite (- (r * cos θ)) (r * (1- cos θ) - r).
  rewrite ydef. assumption.
  rewrite ydef. right. reflexivity. } lra.
  
  apply straight_symmetry in phase.
  inversion_clear kdef as [n k2def].
  rewrite k2_symmetry in k2def; [|assumption].

  assert (exists m, κ₂ x₁ (- y₁) (- r) (- θ) = (-θ) + IZR (2 * m) * PI) as k2def'. {
    exists (-n)%Z.
    rewrite mult_IZR, opp_IZR in *.
    apply (Rmult_eq_reg_l (-1)). setl (- κ₂ x₁ (- y₁) (- r) (- θ)).
    rewrite k2def. field. intro. lra. }
  rewrite Ropp_0 in *.
  specialize (negroot_even_rpos _ _ _ _ cond' rgt0' phase k2def') as [p tdef].

  apply Ropp_eq_compat in tdef.
  rewrite Ropp_involutive in tdef.
  rewrite tdef.

  fieldrewrite (x₁² - (2 * - r - - y₁) * - y₁) (x₁² - (2 * r - y₁) * y₁).
  fieldrewrite (2 * - r - - y₁) (-(2 * r - y₁)).
  assert (- (2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))/(- (2 * r - y₁)))
             + IZR (2 * p) * PI)=
          2 * - atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))/(- (2 * r - y₁)))
          + - IZR (2 * p) * PI) as id.
  field. rewrite id. clear id.

  exists (-p)%Z.
  rewrite mult_IZR, mult_IZR, opp_IZR.
  fieldrewrite ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / - (2 * r - y₁))
               (- ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁)) / (2 * r - y₁))).
  assumption.
  rewrite atan_opp.
  field.
Qed.


(*
commit af0b1141bb60267821b50f07f3d33912ea628b91
Author: Yanni <Yanni.Kouskoulas@jhuapl.edu>
Date:   Thu Mar 7 15:40:44 2019 -0500

temp commit before reverting posroot_odd_Q2

commit a26c5aff36a3d97b6eb946217b3ec1df7237e384
Author: Yanni <Yanni.Kouskoulas@jhuapl.edu>
Date:   Wed Mar 20 11:05:24 2019 -0400

posroot_odd_rpos qed

commit aaa0af2b50ca4d216144484e952417d26ca32379
Author: Yanni <Yanni.Kouskoulas@jhuapl.edu>
Date:   Thu Mar 21 17:47:23 2019 -0400

posroot_odd qed

commit 0d95404707bf54a6ca5233327372ab601595fd66
Author: Yanni Kouskoulas <Yanni.Kouskoulas@jhuapl.edu>
Date:   Mon Jan 27 17:22:38 2020 -0500

negroot_even_Q1_rpos qed.

commit 16adbdec3d29cb45fb341c46b951fae1d4ec10a9
Author: Yanni Kouskoulas <Yanni.Kouskoulas@jhuapl.edu>
Date:   Tue Feb 4 00:28:08 2020 -0500

negroot_even_rpos qed.

                                   
*)


Lemma posroot_odd_Q3negarm_rneg :
  forall x₁ y₁ r θ
         (x1quad :  x₁ < 0)
         (y1quad : 2*r - y₁ = 0)
         (y1pos : y₁ < 0)
         (rgt0 : r < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan (r / x₁) + IZR (2 * m) * PI.
Proof.
  intros until 5. intro kdef.
  assert (0 < (-r)) as rgt0'. lra.
  assert (2 *(- r) -(- y₁) = 0) as y1quad'.
  rewrite <- Ropp_0. setl (-(2*r - y₁)).
  apply Ropp_eq_compat. assumption.

  assert (0 < (-y₁)) as y1gt0. lra.

  apply straight_symmetry in phase.
  
  assert ((x₁ - r * sin θ <= 0 /\ y₁ - r * (1 - cos θ) = 0) \/
          (~ (x₁ - r * sin θ <= 0 /\ y₁ - r * (1 - cos θ) = 0)))
    as [on |noton]. {
    destruct (Rle_dec (x₁ - r * sin θ) 0).
    destruct (Req_dec (y₁ - r * (1 - cos θ)) 0) as [yeq |yne].
    left; split; assumption.
    right. intro cnt. inversion_clear cnt as [xst yst].
    apply yne; assumption.
    right. intro cnt. inversion_clear cnt as [xst yst].
    apply n; assumption. }

  inversion_clear on as [xls yat].
  unfold κ₂ in kdef. rewrite yat in kdef.
  inversion_clear xls as [cst |ycst].

  exfalso.
  specialize (atan2_PI _ cst) as kval.
  inversion_clear kdef as [n at2d].
  rewrite kval in at2d.

  rewrite plus_IZR, mult_IZR in at2d.
  assert (θ = 0 + 2 * IZR (-n) * PI) as tdef. {
    apply (Rplus_eq_reg_r ((2 * IZR n +1)* PI)).
    rewrite opp_IZR. setr PI. symmetry. assumption. }
  rewrite tdef in yat, cst.
  rewrite cos_period1, cos_0,Rminus_eq_0,Rmult_0_r,Rminus_0_r in yat.
  rewrite sin_period1, sin_0,Rmult_0_r,Rminus_0_r in cst.

  clear - y1pos yat. lra.

  exfalso.
  rewrite Ropp_0 in phase.
  apply (straight_std_impl_ineq) in phase.
  assert (y₁ = r * (1-cos θ)) as xdef. {
    apply (Rplus_eq_reg_r (-r*(1-cos θ))). setr 0. rewrite <- yat. field. }
  assert (x₁ = r * sin θ) as ydef. {
    apply (Rplus_eq_reg_r (-r*sin θ)). setr 0. rewrite <- ycst. field. }
  rewrite ydef, xdef in phase.

  assert (r² < r²) as cont. {
    rewrite <- Rmult_1_l. rewrite Rmult_comm, <- (sin2_cos2 θ).
    setr ((r *sin θ)² + (r *cos θ)²).
    rewrite (Rsqr_neg (r * cos θ)).
    apply (Rlt_le_trans _ (x₁² + (- (r * cos θ))²)).
    fieldrewrite (- (r * cos θ)) ((r * (1- cos θ) - r)).
    rewrite (Rsqr_neg (r * (1 - cos θ) - r)). 
    fieldrewrite (- (r * (1 - cos θ) - r)) (- (r * (1 - cos θ)) - - r).
    rewrite ydef. rewrite Rsqr_neg. assumption.
    rewrite ydef. right. reflexivity. }
  lra.
  
  rewrite Ropp_0 in phase.

  inversion_clear kdef as [n k2def].
  rewrite k2_symmetry in k2def; [|assumption].

  assert (exists m, κ₂ x₁ (- y₁) (- r) (- θ) = (-θ) + IZR (2 * m + 1) * PI) as k2def'. {
    exists (-n-1)%Z.
    rewrite plus_IZR, mult_IZR, minus_IZR, opp_IZR in *.
    apply (Rmult_eq_reg_l (-1)). setl (- κ₂ x₁ (- y₁) (- r) (- θ)).
    rewrite k2def. field. intro. lra. }
    
  specialize (posroot_odd_Q2negarm_rpos _ _ _ _ x1quad y1quad' y1gt0 rgt0' phase k2def')
    as ntd.
  inversion_clear ntd as [m ntdef].
  rewrite Ropp_div, atan_opp in ntdef.
  apply Ropp_eq_compat in ntdef.
  rewrite Ropp_involutive in ntdef.
  exists (-m)%Z.
  rewrite ntdef.
  rewrite mult_IZR, mult_IZR, opp_IZR.
  field.
Qed.

Lemma negroot_even_Q3negarm_rneg :
  forall x₁ y₁ r θ
         (x1quad :  x₁ < 0)
         (y1quad : 2*r - y₁ = 0)
         (y1pos : y₁ < 0)
         (rgt0 : r < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = PI + IZR (2 * m) * PI.
Proof.
  intros until 5. intro kdef.
  assert (0 < (-r)) as rgt0'. lra.
  assert (2 *(- r) -(- y₁) = 0) as y1quad'.
  rewrite <- Ropp_0. setl (-(2*r - y₁)).
  apply Ropp_eq_compat. assumption.

  assert (0 < (-y₁)) as y1gt0. lra.

  apply straight_symmetry in phase.
  
  assert ((x₁ - r * sin θ <= 0 /\ y₁ - r * (1 - cos θ) = 0) \/
          (~ (x₁ - r * sin θ <= 0 /\ y₁ - r * (1 - cos θ) = 0)))
    as [on |noton]. {
    destruct (Rle_dec (x₁ - r * sin θ) 0).
    destruct (Req_dec (y₁ - r * (1 - cos θ)) 0) as [yeq |yne].
    left; split; assumption.
    right. intro cnt. inversion_clear cnt as [xst yst].
    apply yne; assumption.
    right. intro cnt. inversion_clear cnt as [xst yst].
    apply n; assumption. }

  inversion_clear on as [xls yat].
  unfold κ₂ in kdef.
  rewrite yat in kdef.
  inversion_clear xls as [cst |ycst].

  + specialize (atan2_PI _ cst) as kval.
    inversion_clear kdef as [n at2d].
    rewrite kval in at2d.
    
    rewrite mult_IZR in at2d.
    assert (θ = PI + 2 * IZR (-n) * PI) as tdef. {
      apply (Rplus_eq_reg_r ((2 * IZR n)* PI)).
      rewrite opp_IZR. setr PI. symmetry. assumption. }
    rewrite tdef in yat, cst.
    rewrite cos_period1 in yat.
    rewrite sin_period1 in cst.
    autorewrite with null in *.

    exists (-n)%Z.
    rewrite mult_IZR.
    assumption.

  + exfalso.
    rewrite Ropp_0 in phase.
    apply (straight_std_impl_ineq) in phase.
    assert (y₁ = r * (1-cos θ)) as xdef. {
      apply (Rplus_eq_reg_r (-r*(1-cos θ))). setr 0. rewrite <- yat. field. }
    assert (x₁ = r * sin θ) as ydef. {
      apply (Rplus_eq_reg_r (-r*sin θ)). setr 0. rewrite <- ycst. field. }
    rewrite ydef, xdef in phase.
    
    assert (r² < r²) as cont. {
      rewrite <- Rmult_1_l. rewrite Rmult_comm, <- (sin2_cos2 θ).
      setr ((r *sin θ)² + (r *cos θ)²).
      rewrite (Rsqr_neg (r * cos θ)).
      apply (Rlt_le_trans _ (x₁² + (- (r * cos θ))²)).
      fieldrewrite (- (r * cos θ)) ((r * (1- cos θ) - r)).
      rewrite (Rsqr_neg (r * (1 - cos θ) - r)). 
      fieldrewrite (- (r * (1 - cos θ) - r)) (- (r * (1 - cos θ)) - - r).
      rewrite ydef. rewrite Rsqr_neg. assumption.
      rewrite ydef. right. reflexivity. }
    lra.
  + rewrite Ropp_0 in phase.
    
    inversion_clear kdef as [n k2def].
    rewrite k2_symmetry in k2def; [|assumption].
    
    assert (exists m, κ₂ x₁ (- y₁) (- r) (- θ) = (-θ) + IZR (2 * m) * PI) as k2def'. {
      exists (-n)%Z.
      rewrite mult_IZR, opp_IZR in *.
      apply (Rmult_eq_reg_l (-1)). setl (- κ₂ x₁ (- y₁) (- r) (- θ)).
      rewrite k2def. field. intro. lra. }
    
    specialize (negroot_even_Q2negarm_rpos _ _ _ _ x1quad y1quad' y1gt0 rgt0' phase k2def')
      as ntd.
    inversion_clear ntd as [m ntdef].
    rewrite <- (Ropp_involutive θ), ntdef.
    exists (-(m+1))%Z.
    rewrite mult_IZR, mult_IZR, opp_IZR, plus_IZR.
    field.
Qed.

Lemma posroot_odd_negarm :
  forall x₁ y₁ r θ
         (cond : (2 * r - y₁ = 0))
         (rgt0 : r <> 0)
         (x1lt0 : x₁ < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan (r/x₁) + IZR (2 * m) * PI.
Proof.
  intros until 3. intro k2def.
  rename cond into trmy1eq0.

  destruct (Rlt_dec r 0).
  + eapply posroot_odd_Q3negarm_rneg; try assumption.
    lra.
    
  + apply Rnot_lt_le in n.
    inversion_clear n as [zltr |req0]; [|exfalso; auto].
    eapply posroot_odd_Q2negarm_rpos; try assumption.
    lra.
Qed.

Lemma negroot_even_negarm :
  forall x₁ y₁ r θ
         (cond : (2 * r - y₁ = 0))
         (rgt0 : r <> 0)
         (x1lt0 : x₁ < 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = PI + IZR (2 * m) * PI.
Proof.
  intros until 3. intro k2def.
  rename cond into trmy1eq0.

  destruct (Rlt_dec r 0).
  + eapply negroot_even_Q3negarm_rneg; try assumption.
    lra.
    
  + apply Rnot_lt_le in n.
    inversion_clear n as [zltr |req0]; [|exfalso; auto].
    eapply negroot_even_Q2negarm_rpos; try assumption.
    lra.
Qed.


Lemma posroot_odd_posarm :
  forall x₁ y₁ r θ
         (cond : (2 * r - y₁ = 0))
         (rgt0 : r <> 0)
         (x1lt0 : 0 < x₁)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z), θ = IZR (2 * m + 1) * PI.
Proof.
  intros until 4. intro k2def.
  rename cond into trmy1eq0.

  destruct (Rlt_dec r 0).
  + eapply posroot_odd_Q4posarm_rneg; try eassumption.
    lra.
        
  + apply Rnot_lt_le in n.
    inversion_clear n as [zltr |req0]; [|exfalso; auto].
    eapply posroot_odd_Q1posarm_rpos. apply x1lt0. eassumption.
    lra. assumption. assumption. assumption.
Qed.

Lemma negroot_even_posarm :
  forall x₁ y₁ r θ
         (cond : (2 * r - y₁ = 0))
         (rgt0 : r <> 0)
         (x1lt0 : 0 < x₁)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z), θ = 2 * atan (r/x₁) + IZR (2 * m) * PI.
Proof.
  intros until 4. intro k2def.
  rename cond into trmy1eq0.

  destruct (Rlt_dec r 0).
  + eapply negroot_even_Q4posarm_rneg; try eassumption.
    lra.
        
  + apply Rnot_lt_le in n.
    inversion_clear n as [zltr |req0]; [|exfalso; auto].
    eapply negroot_even_Q1posarm_rpos. apply x1lt0. eassumption.
    lra. assumption. assumption. assumption.
Qed.


Lemma posroot_odd_noarm :
  forall x₁ y₁ r θ
         (cond : ~ (2 * r - y₁ = 0))
         (rgt0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))/(2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros.
  destruct (Rlt_dec r 0).
  apply posroot_odd_rneg; try assumption.
  apply Rnot_lt_le in n.
  destruct n as [zltr |req0].
  apply posroot_odd_rpos; try assumption.
  exfalso. apply rgt0. subst. reflexivity.
Qed.

Lemma negroot_even_noarm :
  forall x₁ y₁ r θ
         (cond : ~ (2 * r - y₁ = 0))
         (rgt0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    exists (m:Z),
      θ = 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))/(2 * r - y₁)) + 
          IZR (2 * m) * PI.
Proof.
  intros.
  destruct (Rlt_dec r 0).
  apply negroot_even_rneg; try assumption.
  apply Rnot_lt_le in n.
  destruct n as [zltr |req0].
  apply negroot_even_rpos; try assumption.
  exfalso. apply rgt0. subst. reflexivity.
Qed.

(* end hide *)

Lemma posroot_odd :
  forall x₁ y₁ r θ
         (rgt0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    (~ (2 * r - y₁ = 0) /\
    exists (m:Z),
      θ = 2 * atan ((x₁ + sqrt (x₁² - (2 * r - y₁) * y₁))/(2 * r - y₁)) +
          IZR (2 * m) * PI) \/
    ((2 * r - y₁ = 0) /\ 0 < x₁ /\
     exists (m:Z),
       θ = IZR (2 * m + 1) * PI) \/
    ((2 * r - y₁ = 0) /\ x₁ < 0 /\
     exists (m:Z),
       θ = 2 * atan (r/x₁) +
           IZR (2 * m) * PI).
Proof.
  intros until 2. intro k2leg.
  destruct (Req_dec (2 * r - y₁) 0) as [arm | noarm].
  destruct (Rlt_dec 0 x₁).
  right; left; split; [try assumption | split; try assumption].
  eapply posroot_odd_posarm; try eassumption.
  apply Rnot_lt_le in n.
  destruct n as [x1lt0 | x1eq0].
  right; right; split; [try assumption | split; try assumption].
  eapply posroot_odd_negarm; try eassumption.
  apply (straight_std_impl_ineq) in phase.
  rewrite x1eq0 in phase.
  assert (y₁ = 2 * r) as y1def. lra.
  rewrite y1def in phase. clear - phase. unfold Rsqr in phase. lra.
  left; split; [try assumption|].
  apply posroot_odd_noarm; try assumption.
Qed.


Lemma negroot_even :
  forall x₁ y₁ r θ
         (rgt0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    (~ (2 * r - y₁ = 0) /\
    exists (m:Z),
      θ = 2 * atan ((x₁ - sqrt (x₁² - (2 * r - y₁) * y₁))/(2 * r - y₁)) +
          IZR (2 * m) * PI) \/
    ((2 * r - y₁ = 0) /\ 0 < x₁ /\
     exists (m:Z),
       θ = 2 * atan (r / x₁) +
           IZR (2 * m) * PI) \/
    ((2 * r - y₁ = 0) /\ x₁ < 0 /\
     exists (m:Z),
       θ = IZR (2 * m + 1) * PI).
Proof.
  intros until 2. intro k2leg.
  destruct (Req_dec (2 * r - y₁) 0) as [arm | noarm].
  destruct (Rlt_dec 0 x₁).
  right; left; split; [try assumption | split; try assumption].
  eapply negroot_even_posarm; try eassumption.
  apply Rnot_lt_le in n.
  destruct n as [x1lt0 | x1eq0].
  right; right; split; [try assumption | split; try assumption].
  assert (exists m, θ = PI + IZR (2 * m) * PI) as [m mvar]. {
    eapply negroot_even_negarm; try eassumption. }
  exists m.
  rewrite plus_IZR, mvar.
  field.
  apply (straight_std_impl_ineq) in phase.
  rewrite x1eq0 in phase.
  assert (y₁ = 2 * r) as y1def. lra.
  rewrite y1def in phase. clear - phase. unfold Rsqr in phase. lra.
  left; split; [try assumption|].
  apply negroot_even_noarm; try assumption.
Qed.




Lemma theta2_odd :
  forall x₁ y₁ r θ
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n + 1) * PI) ->
    (exists (m:Z), θ = θ2 x₁ y₁ r + IZR (2 * m) * PI).
Proof.
  intros until 2.
  intro k2zeqz2.

  specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as nO.
  specialize (posroot_odd _ _ _ _ rne0 phase k2zeqz2) as rootvals.

  unfold θ2.

  destruct (total_order_T 0 (2 * r - y₁))  as [[zltarm |zeqarm] |zgtarm].
  + destruct rootvals as [[noa [m thdef]] |[[aeq0 rest] |[aeq0 rest]]];
      try (exfalso; clear - zltarm aeq0; lra).

    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exists m.
                rewrite thdef, <- zeqy1, Rmult_0_r, Rminus_0_r, Rminus_0_r.
                rewrite sqrt_Rsqr; [|left; assumption].
                fieldrewrite ((x₁ + x₁) / (2 * r)) (x₁ / r). auto.
                reflexivity.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exfalso. apply nO; split; lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exists (m-1)%Z.
                rewrite thdef.
                rewrite mult_IZR, mult_IZR, minus_IZR.
                field.
                +++++ exists (m-1)%Z.
                rewrite <- zeqy1, Rmult_0_r, Rminus_0_r, Rminus_0_r in thdef.
                rewrite sqrt_Rsqr_abs, Rabs_left, Rplus_opp_r,
                zero_num, atan_0, Rmult_0_r in thdef; try auto.
                rewrite mult_IZR, minus_IZR, thdef, mult_IZR.
                field.
       +++ exfalso. apply rne0. auto.
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exists m.
                rewrite thdef, <- zeqy1, Rmult_0_r, Rminus_0_r, Rminus_0_r.
                rewrite sqrt_Rsqr; [|left; assumption].
                fieldrewrite ((x₁ + x₁) / (2 * r)) (x₁ / r). auto.
                reflexivity.
                +++++ exists (m+1)%Z.
                rewrite thdef.
                rewrite mult_IZR, mult_IZR, plus_IZR.
                field.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exfalso. apply nO; split; lra.
                +++++ exists (m+1)%Z.
                rewrite thdef.
                rewrite mult_IZR, mult_IZR, plus_IZR.
                field.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exfalso.
                rewrite <- zeqy1, Rminus_0_r in zltarm.
                clear - zltarm zgtr.
                lra.
                +++++ exists (m+1)%Z. rewrite thdef, mult_IZR, mult_IZR, plus_IZR.
                field.
  + destruct rootvals as [[noa rest] | armcases];
      try (exfalso; clear - zeqarm noa; auto).

    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           destruct armcases as
               [[arm [zltx12 [m tdef]]]| [arm [x1lt0 [m tdef]]]];
             [| clear - zltx1 x1lt0; lra].
           rewrite plus_IZR, mult_IZR in tdef.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists m. rewrite mult_IZR, tdef. lra.
                +++++ exfalso. rewrite <- zeqy1 in zeqarm. clear - zeqarm zltr. lra.
                +++++ clear - zeqarm zltr zgty1. lra.
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
                rewrite <- zeqarm, Rmult_0_r in phase1.
                clear - phase1.
                lra.
                +++++ exfalso. apply nO; split; lra.
                +++++ exfalso. clear - zeqarm zltr zgty1. lra.
           ++++ destruct armcases as [[arm [zltx1 [m tdef]]]| [arm [x1lt0 [m tdef]]]];
                  [clear - zltx1 zgtx1; lra|].
                rewrite mult_IZR in tdef.

                destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ symmetry in zeqarm.
                apply Rminus_diag_uniq_sym in zeqarm.
                rewrite zeqarm.
                fieldrewrite (2 * r / (2 * x₁)) (r / x₁);
                  [intro x1eq0; rewrite x1eq0 in zgtx1; lra|].
                exists (m-1)%Z.
                rewrite mult_IZR, minus_IZR, tdef.
                lra.
                +++++ exfalso.
                rewrite <- zeqy1, Rminus_0_r in zeqarm.
                clear - zeqarm zltr.
                lra.
                +++++ exfalso.
                clear - zeqarm zltr zgty1.
                lra.
       +++ exfalso. apply rne0. auto.
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exfalso; clear - zeqarm zgtr zlty1; lra.
                +++++ exfalso; clear - zeqarm zgtr zeqy1; lra.
                +++++ destruct armcases as [[arm [zltx12 [m tdef]]]
                                           | [arm [x1lt0 [m tdef]]]];
                  [|clear - x1lt0 zltx1; lra].
                exists (m+1)%Z.
                rewrite tdef, mult_IZR, plus_IZR, plus_IZR, mult_IZR.
                field.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exfalso. clear - zgtr zlty1 zeqarm. lra.
                +++++ exfalso. apply nO; split; lra.
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
                rewrite <- zeqarm, Rmult_0_r in phase1.
                clear - phase1.
                lra.
           ++++ destruct armcases as [[arm [zltx1 [m tdef]]]
                                     | [arm [x1lt0 [m tdef]]]];
                  [clear - zgtx1 zltx1; lra|].
                destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exfalso. clear - zeqarm zgtr zlty1. lra.
                +++++ exfalso. rewrite <- zeqy1, Rminus_0_r in zeqarm.
                apply rne0.
                clear - zeqarm.
                lra.
                +++++ symmetry in zeqarm.
                apply Rminus_diag_uniq_sym in zeqarm.
                rewrite zeqarm.
                fieldrewrite (2 * r / (2 * x₁)) (r / x₁);
                  [intro x1eq0; rewrite x1eq0 in zgtx1; lra|].
                exists (m+1)%Z.
                rewrite mult_IZR, tdef, mult_IZR, plus_IZR.
                lra.
  + destruct rootvals as [[noa [m thdef]] |[[aeq0 rest] |[aeq0 rest]]];
    try (exfalso; rewrite aeq0 in zgtarm; clear - zgtarm; lra).
    rewrite mult_IZR in thdef.
    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists (m-1)%Z.
                rewrite mult_IZR, minus_IZR, thdef.
                field.
                +++++ exfalso.
                rewrite <- zeqy1, Rminus_0_r in zgtarm.
                clear - zltr zgtarm.
                lra.
                +++++ exists m. rewrite mult_IZR. assumption.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists (m-1)%Z.
                rewrite mult_IZR, minus_IZR, thdef.
                field.
                +++++ exfalso.
                rewrite <- zeqy1, Rminus_0_r in zgtarm.
                clear - zltr zgtarm.
                lra.
                +++++ exists m. rewrite mult_IZR. assumption.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists (m-1)%Z.
                rewrite mult_IZR, minus_IZR, thdef.
                field.
                +++++ exfalso.
                rewrite <- zeqy1, Rminus_0_r in zgtarm.
                clear - zltr zgtarm.
                lra.
                +++++ exists m. rewrite mult_IZR. assumption.
       +++ exfalso. apply rne0. auto.
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists m. rewrite mult_IZR. assumption.
                +++++ exists m.
                rewrite thdef, <- zeqy1, Rmult_0_r, Rminus_0_r, Rminus_0_r.
                rewrite sqrt_Rsqr; [|left; assumption].
                fieldrewrite ((x₁ + x₁) / (2 * r)) (x₁ / r). auto.
                rewrite mult_IZR.
                reflexivity.
                +++++ exists m. rewrite mult_IZR. assumption.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  try (exists m; rewrite mult_IZR; assumption).
                +++++ exfalso. apply nO; split; lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists m; rewrite mult_IZR; assumption.
                +++++ exists (m+1)%Z.
                rewrite <- zeqy1, Rmult_0_r, Rminus_0_r, Rminus_0_r in thdef.
                rewrite sqrt_Rsqr_abs, Rabs_left, Rplus_opp_r,
                zero_num, atan_0, Rmult_0_r in thdef; auto.
                rewrite mult_IZR, plus_IZR, thdef.
                field.
                +++++ exists (m+1)%Z. rewrite mult_IZR, plus_IZR, thdef. field.
Qed.


Lemma theta1_even :
  forall x₁ y₁ r θ
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x₁ y₁),
    (exists (n:Z), κ₂ x₁ y₁ r θ = θ + IZR (2 * n) * PI) ->
    (exists (m:Z), θ = θ1 x₁ y₁ r + IZR (2 * m) * PI).
Proof.
Proof.
  intros until 2.
  intro k2zeqz2.

  specialize (straight_not_stationary2 _ _ _ _ _ _ phase) as nO.
  specialize (negroot_even _ _ _ _ rne0 phase k2zeqz2) as rootvals.

  unfold θ1.

  destruct (total_order_T 0 (2 * r - y₁))  as [[zltarm |zeqarm] |zgtarm].
  + destruct rootvals as [[noa [m thdef]] |[[aeq0 rest] |[aeq0 rest]]];
      try (exfalso; clear - zltarm aeq0; lra).

    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exists m.
                rewrite thdef, <- zeqy1, Rmult_0_r, Rminus_0_r, Rminus_0_r.
                rewrite sqrt_Rsqr; [|left; assumption].
                fieldrewrite ((x₁ - x₁) / (2 * r)) (0). auto.
                rewrite atan_0.
                arn.
                reflexivity.
                +++++ rewrite thdef.
                exists (m-1)%Z.
                rewrite mult_IZR, mult_IZR, minus_IZR.
                field.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exfalso. apply nO; split; lra.
                +++++ rewrite thdef.
                exists (m-1)%Z.
                rewrite mult_IZR, mult_IZR, minus_IZR.
                field.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exists (m-1)%Z.
                rewrite thdef.
                rewrite mult_IZR, mult_IZR, minus_IZR.
                field.
                +++++ exists (m-1)%Z.
                rewrite thdef.
                rewrite mult_IZR, mult_IZR, minus_IZR.
                field.
                +++++ exists (m-1)%Z.
                rewrite thdef.
                rewrite mult_IZR, mult_IZR, minus_IZR.
                field.
       +++ exfalso. apply rne0. auto.
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exists (m+1)%Z.
                rewrite thdef.
                rewrite mult_IZR, mult_IZR, plus_IZR.
                field.
                +++++ exists (m)%Z.
                rewrite thdef.
                rewrite <- zeqy1.
                arn.
                rewrite sqrt_Rsqr; try lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exfalso. apply nO; split; lra.
                +++++ exfalso. apply nO; split; lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  eauto.
                +++++ exists (m+1)%Z. rewrite thdef, mult_IZR, mult_IZR, plus_IZR.
                field.
                +++++ exists (m+1)%Z. rewrite thdef, mult_IZR, mult_IZR, plus_IZR.
                field.
  + destruct rootvals as [[noa rest] | armcases];
      try (exfalso; clear - zeqarm noa; auto).

    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           destruct armcases as
               [[arm [zltx12 [m tdef]]]| [arm [x1lt0 [m tdef]]]];
             [| clear - zltx1 x1lt0; lra].
           rewrite mult_IZR in tdef.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists m. rewrite mult_IZR, tdef.
                symmetry in zeqarm.
                apply Rminus_diag_uniq_sym in zeqarm.
                rewrite zeqarm.
                fieldrewrite (2 * r / (2 * x₁)) (r / x₁).
                lra.
                field.
                +++++ exfalso. rewrite <- zeqy1 in zeqarm. clear - zeqarm zltr. lra.
                +++++ clear - zeqarm zltr zgty1. lra.
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
                rewrite <- zeqarm, Rmult_0_r in phase1.
                clear - phase1.
                lra.
                +++++ exfalso. apply nO; split; lra.
                +++++ exfalso. clear - zeqarm zltr zgty1. lra.
           ++++ destruct armcases as [[arm [zltx1 [m tdef]]]| [arm [x1lt0 [m tdef]]]];
                  [clear - zltx1 zgtx1; lra|].
                rewrite plus_IZR, mult_IZR in tdef.

                destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ symmetry in zeqarm.
                apply Rminus_diag_uniq_sym in zeqarm.
                exists m.
                rewrite tdef, mult_IZR.
                field.
                +++++ exfalso.
                rewrite <- zeqy1, Rminus_0_r in zeqarm.
                clear - zeqarm zltr.
                lra.
                +++++ exfalso.
                clear - zeqarm zltr zgty1.
                lra.
       +++ exfalso. apply rne0. auto.
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exfalso; clear - zeqarm zgtr zlty1; lra.
                +++++ exfalso; clear - zeqarm zgtr zeqy1; lra.
                +++++ destruct armcases as [[arm [zltx12 [m tdef]]]
                                           | [arm [x1lt0 [m tdef]]]];
                  [|clear - x1lt0 zltx1; lra].
                exists (m)%Z.
                rewrite tdef, mult_IZR.
                symmetry in zeqarm.
                apply Rminus_diag_uniq_sym in zeqarm.
                rewrite zeqarm.
                fieldrewrite (2 * r / (2 * x₁)) (r / x₁).
                lra.
                field.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exfalso. clear - zgtr zlty1 zeqarm. lra.
                +++++ exfalso. apply nO; split; lra.
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
                rewrite <- zeqarm, Rmult_0_r in phase1.
                clear - phase1.
                lra.
           ++++ destruct armcases as [[arm [zltx1 [m tdef]]]
                                     | [arm [x1lt0 [m tdef]]]];
                  [clear - zgtx1 zltx1; lra|].
                destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exfalso. clear - zeqarm zgtr zlty1. lra.
                +++++ exfalso. rewrite <- zeqy1, Rminus_0_r in zeqarm.
                apply rne0.
                clear - zeqarm.
                lra.
                +++++ symmetry in zeqarm.
                apply Rminus_diag_uniq_sym in zeqarm.
                exists (m+1)%Z.
                rewrite tdef, mult_IZR, plus_IZR, mult_IZR, plus_IZR.
                field.
  + destruct rootvals as [[noa [m thdef]] |[[aeq0 rest] |[aeq0 rest]]];
    try (exfalso; rewrite aeq0 in zgtarm; clear - zgtarm; lra).
    rewrite mult_IZR in thdef.
    ++ destruct (total_order_T 0 r) as [[zltr |zeqr] |zgtr].
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists (m)%Z.
                rewrite mult_IZR,  thdef.
                field.
                +++++ exfalso.
                rewrite <- zeqy1, Rminus_0_r in zgtarm.
                clear - zltr zgtarm.
                lra.
                +++++ exists (m-1)%Z. rewrite mult_IZR.
                rewrite thdef, minus_IZR.
                field.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists (m)%Z.
                rewrite mult_IZR, thdef.
                field.
                +++++ exfalso.
                rewrite <- zeqy1, Rminus_0_r in zgtarm.
                clear - zltr zgtarm.
                lra.
                +++++ exists (m-1)%Z. rewrite mult_IZR, thdef, minus_IZR.
                field.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists (m)%Z.
                rewrite mult_IZR, thdef.
                field.
                +++++ exfalso.
                rewrite <- zeqy1, Rminus_0_r in zgtarm.
                clear - zltr zgtarm.
                lra.
                +++++ exists (m-1)%Z. rewrite mult_IZR, minus_IZR, thdef.
                field.
       +++ exfalso. apply rne0. auto.
       +++ destruct (total_order_T 0 x₁) as [[zltx1 |zeqx1] |zgtx1].
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists (m+1)%Z. rewrite mult_IZR, plus_IZR, thdef.
                field.
                +++++ exists (m)%Z.
                rewrite thdef.
                rewrite <- zeqy1.
                arn.
                rewrite mult_IZR.
                rewrite sqrt_Rsqr; try lra.
                rewrite Rminus_eq_0.
                rewrite <- RmultRinv.
                arn.
                rewrite atan_0.
                arn.
                reflexivity.
                +++++ exists m. rewrite mult_IZR. assumption.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1];
                  try (exists m; rewrite mult_IZR; assumption).
                +++++ exists (m+1)%Z.
                rewrite mult_IZR, plus_IZR, thdef.
                field.
                +++++ exfalso.
                apply nO.
                split; lra.
           ++++ destruct (total_order_T 0 y₁) as [[zlty1 |zeqy1] |zgty1].
                +++++ exists (m+1)%Z.
                rewrite mult_IZR, plus_IZR, thdef.
                field.
                +++++ exists (m+1)%Z.
                rewrite mult_IZR, plus_IZR, thdef.
                field.
                +++++ exists (m+1)%Z. rewrite mult_IZR, plus_IZR, thdef. field.
Qed.

(* begin hide *)
Ltac cne0 :=
  let xDnn := fresh "xDnn" in
  let c := fresh "c" in 
  match goal with
  | num : 0 < ?x + ?D,
    zgta : 0 < 2 * ?r - ?y,
    phase : straight ?r 0 0 0 ?x ?y |-
    cos (atan ((?x + ?D) / (2 * ?r - ?y))) <> 0 =>
    rewrite <- atan2_atan_Q1; [|assumption| lra];
    rewrite atan2_cos_id; try assumption;
    repeat rewrite <- Rsqr_pow2;
    intro c;
    rewrite <- signeq0_eqv in c;
    rewrite sign_eq_pos_den in c;
    [ rewrite signeq0_eqv in c;lra|];
    apply sqrt_lt_R0;
    apply Rplus_lt_le_0_compat;
    [ apply Rsqr_pos_lt; lra|
      left; apply Rsqr_pos_lt; lra]
  | num : 0 < ?x + ?D,
    zgta : 0 > 2 * ?r - ?y,
    phase : straight ?r 0 0 0 ?x ?y |-
    cos (atan ((?x + ?D) / (2 * ?r - ?y))) <> 0 =>
    fieldrewrite (atan ((x + D) / (2 * r - y)))
                 ((atan ((x + D) / (2 * r - y)) + PI) - PI);
    rewrite <- atan2_atan_Q2; try assumption;
    rewrite <- cos_neg;
    fieldrewrite (- (atan2 (x + D) (2 * r - y) - PI))
                 (- atan2 (x + D) (2 * r - y) + PI);
    rewrite neg_cos;
    rewrite <- cos_neg, Ropp_involutive;
    rewrite atan2_cos_id; try assumption;
    repeat rewrite <- Rsqr_pow2;
    intro c;
    rewrite <- Ropp_0 in c;
    apply Ropp_eq_compat in c;
    repeat rewrite Ropp_involutive in c;
    rewrite <- signeq0_eqv in c;
    rewrite sign_eq_pos_den in c;
    [ rewrite signeq0_eqv in c;lra|];
    apply sqrt_lt_R0;
    apply Rplus_lt_le_0_compat;
    [ apply Rsqr_pos_lt; lra|apply Rle_0_sqr]
  | num : ?x + ?D < 0,
    zgta : 0 < 2 * ?r - ?y,
    phase : straight ?r 0 0 0 ?x ?y |-
    cos (atan ((?x + ?D) / (2 * ?r - ?y))) <> 0 =>
    rewrite <- atan2_atan_Q4; try lra;
    rewrite atan2_cos_id; try assumption;
    repeat rewrite <- Rsqr_pow2;
    intro c;
    rewrite <- signeq0_eqv in c;
    rewrite sign_eq_pos_den in c;
    [ rewrite signeq0_eqv in c;lra|];
    apply sqrt_lt_R0;
    apply Rplus_lt_le_0_compat;
    [ apply Rsqr_pos_lt; lra|
      left; apply Rsqr_pos_lt; lra]
  | num : ?x + ?D < 0,
    zgta : 0 > 2 * ?r - ?y,
    phase : straight ?r 0 0 0 ?x ?y |-
    cos (atan ((?x + ?D) / (2 * ?r - ?y))) <> 0 =>
    fieldrewrite (atan ((x + D) / (2 * r - y)))
                 ((atan ((x + D) / (2 * r - y)) - PI) + PI);
    rewrite <- atan2_atan_Q3; try assumption;
    rewrite neg_cos;
    apply Ropp_neq_0_compat;
    rewrite atan2_cos_id; try assumption;
    repeat rewrite <- Rsqr_pow2;
    intro c;
    rewrite <- signeq0_eqv in c;
    rewrite sign_eq_pos_den in c;
    [ rewrite signeq0_eqv in c;lra|];
    apply sqrt_lt_R0;
    apply Rplus_lt_le_0_compat;
    [ apply Rsqr_pos_lt; lra|apply Rle_0_sqr]
  | _ => idtac
  end.

Ltac t1t2L :=
  let D := fresh "D" in
  match goal with
  | phase : straight ?r 0 0 0 ?x ?y,
            t1eqt2 : 2 * atan ((?x - sqrt (?x² - (2 * ?r - ?y) * ?y))
                                 / (2 * ?r - ?y)) =
                     2 * atan ((?x + sqrt (?x² - (2 * ?r - ?y) * ?y))
                                 / (2 * ?r - ?y))
             + IZR (2 * ?n) * PI |- _ =>
    set (D := sqrt (x² - (2 * r - y) * y)) in *;
    assert (atan ((x - D) / (2 * r - y)) =
            atan ((x + D) / (2 * r - y)) + IZR n * PI) as teq;
    [ apply (Rmult_eq_reg_l 2); [|lra];
      rewrite Rmult_plus_distr_l, t1eqt2, mult_IZR;
      field |];
    apply (f_equal tan) in teq;
    assert (~ (2 * r - y = 0 /\ x + D = 0)) as tn0;
    [ intros [a0 xD]; lra | ];
    rewrite tan_period in teq;
    [ repeat rewrite atan_right_inv in teq;
      apply (Rmult_eq_compat_r (2 * r - y)) in teq;
      assert (- D = D) as contra;
      [ apply (Rplus_eq_reg_l x);
        setl ((x - D) / (2 * r - y) * (2 * r - y)); try lra;
        setr ((x + D) / (2 * r - y) * (2 * r - y)); try lra|];
      assert (D <> 0) as Dne0;
      [unfold D; apply straightcond in phase|lra];
      assert (0 < x² - (2 * r - y) * y) as ps;
      [ rewrite Rmult_minus_distr_r;
        unfold Rsqr at 2 in phase; lra|
        apply sqrt_lt_R0 in ps; lra] |]
  end.

(* end hide *)
Lemma theta1_ne_theta2 :
  forall x y r n (rne0 : r <> 0)
    (phase : straight r 0 0 0 x y),
    θ1 x y r <> θ2 x y r + IZR (2 * n) * PI.
Proof.
  intros.
  intro t1eqt2.
  unfold θ1,θ2 in *.
  destruct (total_order_T 0 r) as [[zltr|zeqr]|zgtr].
  + destruct (total_order_T 0 x) as [[zltx|zeqx]|zgtx].
    ++ destruct (total_order_T 0 y) as [[zlty|zeqy]|zgty].
       +++ destruct (total_order_T 0 (2 * r - y)) as [[zlta|zeqa]|zgta].
           ++++ t1t2L.
                assert (0 < x + D) as num. {
                specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
                  change (0 <= D) in xDnn.
                lra. }
                cne0.
           ++++ specialize (atan_bound (y / (2 * x))) as [abl abu].
                apply (Rmult_lt_compat_l 2) in abl; try lra.
                apply (Rmult_lt_compat_l 2) in abu; try lra.
                assert (2 * (- PI / 2) = -PI) as id. field.
                rewrite id in abl. clear id.
                assert (2 * (PI / 2) = PI) as id. field.
                rewrite id in abu. clear id.
                rewrite t1eqt2, mult_IZR in abl, abu.
                destruct n.
                - rewrite Rmult_0_r, Rmult_0_l, Rplus_0_r in abl, abu.
                  lra.
                - specialize (IZRposge1 p) as pge1.
                  specialize PI_RGT_0 as pigt0.
                  clear - abu pge1 pigt0.
                  assert (PI < PI + 2 * IZR (Z.pos p) * PI) as ctra.
                  apply (Rmult_lt_reg_r (/PI)).
                  apply Rinv_0_lt_compat; lra.
                  setl 1. lra.
                  setr (1 + 2 * IZR (Z.pos p)). lra.
                  lra.
                  lra.
                - specialize (IZRneglen1 p) as nle1.
                  specialize PI_RGT_0 as pigt0.
                  clear - abl nle1 pigt0.
                  assert (PI + 2 * IZR (Z.neg p) * PI <= - PI) as ctra.
                  apply (Rmult_le_reg_r (/PI)).
                  apply Rinv_0_lt_compat; lra.
                  setr (-1). lra.
                  setl (1 + 2 * IZR (Z.neg p)). lra.
                  lra.
                  lra.
           ++++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                      / (2 * r - y))) in *.
                assert (Q + 2 * 1 * PI + IZR (2 * n) * PI =
                        Q + IZR (2 * (n+1)) * PI) as id. {
                  repeat rewrite mult_IZR.
                  rewrite plus_IZR.
                  field. }
                rewrite id in t1eqt2.
                unfold Q in *. clear Q id.
                t1t2L.
                assert (0 < x + D) as xDgt0. {
                  specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
                    change (0 <= D) in xDnn;
                    lra. }
                cne0.
       +++ specialize PI_RGT_0 as pigt0.
           assert (atan (x / r) = 0 + IZR ( -n) * PI)
             as at2d. {
             rewrite Rplus_0_l.
             apply (Rmult_eq_reg_l 2); [|lra].
             apply (Rplus_eq_reg_r (IZR (2 * n) * PI)).
             rewrite <- t1eqt2.
             rewrite opp_IZR, mult_IZR.
             field. }
           clear t1eqt2. rename at2d into t1eqt2.
           apply (f_equal tan) in t1eqt2.
           rewrite atan_right_inv, tan_period, tan_0 in t1eqt2;
             [|rewrite cos_0 ; discrR].
           assert (x = 0) as xeq0. {
           apply (Rmult_eq_reg_r (/r));
             [|apply Rinv_neq_0_compat; lra].
           setr 0. lra. setl (x / r). lra.
           assumption. }
           rewrite xeq0 in zltx.
           clear - zltx.
           lra.
       +++ rename t1eqt2 into eq.
           assert (2 * atan ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y)) =
                   2 * atan ((x + sqrt (x² - (2 * r - y) * y)) / (2 * r - y))
                   + IZR (2 * (n - 1)) * PI) as t1eqt2. {
             rewrite mult_IZR, minus_IZR.
             apply (Rplus_eq_reg_r (2*1*PI)).
             rewrite eq, mult_IZR.
             field. }
           t1t2L.
           destruct (total_order_T 0 (2 * r - y))
             as [[zlta|zeqa]|zgta]; try lra.
           assert (0 < x + D) as num. { 
           specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn.
           change (0 <= D) in xDnn.
           lra. }
           cne0.
    ++ destruct (total_order_T 0 y) as [[zlty|zeqy]|zgty].
       +++ destruct (total_order_T 0 (2 * r - y)) as [[zlta|zeqa]|zgta].
           ++++ clear t1eqt2.
                apply straightcond in phase.
                rewrite <- zeqx, Rsqr_0, Rplus_0_l in phase.
                assert (2 * r - y < 0) as esahp.
                apply (Rmult_lt_reg_r y); try assumption.
                rewrite (Rmult_minus_distr_r), Rmult_0_l.
                apply (Rplus_lt_reg_r (y²)).
                rewrite Rplus_0_l.
                setl (2 * r * y).
                assumption.
                lra.
           ++++   apply straightcond in phase.
                  rewrite <- zeqx in phase.
                  autorewrite with null in *.
                  unfold Rsqr in phase.
                  symmetry in zeqa.
                  apply Rminus_diag_uniq_sym in zeqa.
                  assert (2 * r < 2 * r) as cnt. {
                    rewrite <- zeqa at 2.
                    apply (Rmult_lt_reg_r y); try lra. }
                  lra.

           ++++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                      / (2 * r - y))) in *.
                assert (Q + 2 * 1 * PI + IZR (2 * n) * PI =
                        Q + IZR (2 * (n+1)) * PI) as id. {
                  repeat rewrite mult_IZR.
                  rewrite plus_IZR.
                  field. }
                rewrite id in t1eqt2. unfold Q in *. clear Q id.
                t1t2L.
                assert (0 < x + D). {
                  specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
                    change (0 <= D) in xDnn.
                  destruct xDnn as [zltD |zeqD].
                  lra.
                  exfalso.
                  unfold D in zeqD.
                  rewrite <- sqrt_0 in zeqD.
                  apply sqrt_inj in zeqD.
                  rewrite <- zeqx, Rsqr_0, Rminus_0_l, <- Ropp_0 in zeqD.
                  apply Ropp_eq_compat in zeqD.
                  repeat rewrite Ropp_involutive in zeqD.
                  symmetry in zeqD.
                  apply Rmult_integral in zeqD.
                  destruct zeqD; lra.
                  right. reflexivity.
                  rewrite <- zeqx, Rsqr_0, Rminus_0_l.
                  setr (-(2*r-y)*y).
                  apply Rmult_le_pos; [lra | left; assumption]. }
                cne0.
       +++ apply straightcond in phase.
           clear t1eqt2.
           rewrite <- zeqx, <- zeqy, Rsqr_0,
                   Rplus_0_r, Rmult_0_r in phase.
           clear - phase.
           lra.
       +++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           set (R := 2 * atan ((x - sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           rename t1eqt2 into eq.
           assert (R = Q + IZR (2 * (n-1)) * PI) as t1eqt2. {
             rewrite mult_IZR, minus_IZR.
             apply (Rplus_eq_reg_r (2*1*PI)).
             rewrite eq, mult_IZR. field. }
           unfold R, Q in *.
           clear eq R Q.
           t1t2L.
           destruct (total_order_T 0 (2 * r - y))
             as [[zlta|zeqa]|zgta]; try lra.
           assert (0 < x + D). {
             specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
               change (0 <= D) in xDnn.
             destruct xDnn as [zltD |zeqD].
             lra.
             exfalso.
             unfold D in zeqD.
             rewrite <- sqrt_0 in zeqD.
             apply sqrt_inj in zeqD.
             rewrite <- zeqx, Rsqr_0, Rminus_0_l, <- Ropp_0 in zeqD.
             apply Ropp_eq_compat in zeqD.
             repeat rewrite Ropp_involutive in zeqD.
             symmetry in zeqD.
             apply Rmult_integral in zeqD.
             destruct zeqD; lra.
             right. reflexivity.
             rewrite <- zeqx, Rsqr_0, Rminus_0_l.
             setr ((2*r-y)*- y).
             apply Rmult_le_pos; [left; assumption|lra]. }
           cne0.
    ++ destruct (total_order_T 0 y) as [[zlty|zeqy]|zgty].
       +++ destruct (total_order_T 0 (2 * r - y)) as [[zlta|zeqa]|zgta].
           ++++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                      / (2 * r - y))) in *.
                set (R := 2 * atan ((x - sqrt (x² - (2 * r - y) * y))
                                      / (2 * r - y))) in *.
                rename t1eqt2 into eq.
                assert (R = Q + IZR (2 * n) * PI) as id. {
                  apply (Rplus_eq_reg_r (2 * 1 * PI)).
                  lrag eq. }
                unfold R, Q in *.
                clear R Q eq.
                t1t2L.
                assert (x + D < 0) as xDlt0. {
                  specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
                    change (0 <= D) in xDnn.
                  apply (Rplus_lt_reg_r (-x)).
                  setl D. setr (-x).
                  rewrite <- (Rabs_right D), <- (Rabs_left x); try lra.
                  apply Rsqr_lt_abs_0.
                  unfold D.
                  rewrite Rsqr_sqrt.
                  apply (Rplus_lt_reg_r (-x²)).
                  setr (-0). setl (- ((2*r-y)*y)).
                  apply Ropp_lt_contravar.
                  apply Rmult_lt_0_compat; try assumption.
                  left.
                  apply straightcond in phase.
                  clear - phase.
                  rewrite Rmult_minus_distr_r.
                  apply (Rplus_lt_reg_r (2 * r * y)).
                  rewrite Rplus_0_l.
                  setr (x² + y²). assumption.
                }
                cne0.
           ++++ specialize PI_RGT_0 as pigt0.
                assert (atan (y / (2 * x)) = PI / 2 + IZR (-n-1) * PI)
                  as at2d. {
                  apply (Rmult_eq_reg_l 2); [|lra].
                  apply (Rplus_eq_reg_r (2 * 1 * PI + IZR (2 * n) * PI)).
                  rewrite <- Rplus_assoc, <- t1eqt2.
                  rewrite mult_IZR, minus_IZR, opp_IZR.
                  field. }
                specialize (atan_bound (y / (2 * x))) as [lb ub].
                rewrite at2d in ub,lb.
                destruct (-n - 1)%Z.
                - lra.
                - specialize (IZRposge1 p) as ps.
                  clear - ps ub pigt0.
                  apply (Rmult_lt_compat_l 2) in ub; [|lra].
                  assert (1 + 2 * IZR (Z.pos p) < 1) as id. {
                    apply (Rmult_lt_reg_r PI); try assumption.
                    rewrite Rmult_plus_distr_r.
                    setl (2 * (PI / 2 + IZR (Z.pos p) * PI)).
                    setr (2 * (PI / 2)).
                    assumption. }
                  lra.
                - specialize (IZRneglen1 p) as ps.
                  clear - ps lb pigt0.
                  apply (Rmult_lt_compat_l 2) in lb; [|lra].
                  assert (-1 < 1 + 2 * IZR (Z.neg p)) as id. {
                    apply (Rmult_lt_reg_r PI); try assumption.
                    rewrite Rmult_plus_distr_r.
                    setr (2 * (PI / 2 + IZR (Z.neg p) * PI)).
                    setl (2 * (- PI / 2)).
                    assumption. }
                  lra.
           ++++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                      / (2 * r - y))) in *.
                assert (Q + 2 * 1 * PI + IZR (2 * n) * PI =
                        Q + IZR (2 * (n+1)) * PI) as id. {
                  repeat rewrite mult_IZR.
                  rewrite plus_IZR.
                  field. }
                rewrite id in t1eqt2. unfold Q in *. clear Q id.
                t1t2L.
                assert (0 < x + D) as zltxD. {
                  specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
                    change (0 <= D) in xDnn.
                  apply (Rplus_lt_reg_r (-x)).
                  setr D. setl (-x).
                  rewrite <- (Rabs_right D), <- (Rabs_left x); try lra.
                  apply Rsqr_lt_abs_0.
                  unfold D.
                  rewrite Rsqr_sqrt.
                  apply (Rplus_lt_reg_r (-x²)).
                  setl 0. setr (-(2*r-y)*y).
                  apply Rmult_lt_0_compat; [lra | assumption].
                  left.
                  apply straightcond in phase.
                  clear - phase.
                  rewrite Rmult_minus_distr_r.
                  apply (Rplus_lt_reg_r (2 * r * y)).
                  rewrite Rplus_0_l.
                  setr (x² + y²). assumption.
                }
                cne0.
       +++ set (Q := ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))) in *.
           rename t1eqt2 into eq.
           assert (atan Q = 0 + IZR n * PI) as t1eqt2. {
             apply (Rmult_eq_reg_l 2); [|lra].
             apply (Rplus_eq_reg_r (2 * 1 * PI)).
             rewrite eq, mult_IZR.
             field. }
           clear eq.
           apply (f_equal tan) in t1eqt2.
           rewrite atan_right_inv, tan_period, tan_0 in t1eqt2;
             [|rewrite cos_0 ; discrR].
           unfold Q in t1eqt2.
           clear Q.
           rename t1eqt2 into c.
           rewrite <- signeq0_eqv in c.
           rewrite sign_eq_pos_den in c;
             [ rewrite signeq0_eqv in c|].
           rewrite <- zeqy, Rmult_0_r, Rminus_0_r, Rsqr_neg, sqrt_Rsqr in c;
           lra.
           lra.
       +++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           set (R := 2 * atan ((x - sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           rename t1eqt2 into eq.
           assert (R = Q + IZR (2 * (n-1)) * PI) as id. {
             apply (Rplus_eq_reg_r (2 * 1 * PI)).
             rewrite Z.mul_sub_distr_l.
             rewrite minus_IZR.
             rewrite (mult_IZR 2 1).
             lrag eq. }
           unfold R, Q in *.
           clear R Q eq.
           t1t2L.
           destruct (total_order_T 0 (2 * r - y))
             as [[zlta|zeqa]|zgta]; try lra.
           assert (0 < x + D). {
             apply (Rplus_lt_reg_r (-x)).
             setl (-x). setr D.
             unfold D.
             rewrite Rsqr_neg.
             rewrite <- (sqrt_Rsqr (-x)) at 1; [|lra].
             apply sqrt_lt_1.
             apply Rle_0_sqr.
             apply Rplus_le_le_0_compat.
             apply Rle_0_sqr.
             setr ((2 * r - y) * - y).
             apply Rmult_le_pos.
             left; assumption.
             left; lra.
             rewrite <- Rsqr_neg.
             apply (Rplus_lt_reg_r (- x²)).
             setl 0.
             setr ((2 * r - y) * - y).
             apply Rmult_lt_0_compat.
             assumption.
             lra. }
           cne0.
  + clear - rne0 zeqr. lra.
  + destruct (total_order_T 0 x) as [[zltx|zeqx]|zgtx].
    ++ destruct (total_order_T 0 y) as [[zlty|zeqy]|zgty].
       +++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           set (R := 2 * atan ((x - sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           rename t1eqt2 into eq.
           assert (R = Q + IZR (2 * (n+1)) * PI) as id. {
             apply (Rplus_eq_reg_r (- 2 * 1 * PI)).
             setl (R - 2 * 1 * PI).
             rewrite Z.mul_add_distr_l.
             rewrite plus_IZR.
             rewrite (mult_IZR 2 1).
             lrag eq. }
           unfold R, Q in *.
           clear R Q eq.
           t1t2L.
           destruct (total_order_T 0 (2 * r - y))
             as [[zlta|zeqa]|zgta]; try lra.
           assert (0 < x + D). {
                  specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
                    change (0 <= D) in xDnn.
                  lra. }             
           cne0.
       +++ specialize PI_RGT_0 as pigt0.
           symmetry in t1eqt2.
           rewrite Rplus_comm, mult_IZR in t1eqt2.
           apply Rplus_opp_r_uniq in t1eqt2.
           specialize (atan_bound (x/r)) as [atlb atub].
           apply (Rmult_lt_compat_l 2) in atlb; try lra.
           apply (Rmult_lt_compat_l 2) in atub; try lra.
           rewrite t1eqt2 in atlb, atub.
           assert (IZR n = 0) as IZRneq0. {
             assert (- 1 < - 2 * IZR n) as oltIZRn. {
               apply (Rmult_lt_reg_r PI); try lra. }
             assert (- 2 * IZR n < 1) as IZRnlto. {
               apply (Rmult_lt_reg_r PI); try lra. }
             rewrite <- mult_IZR in oltIZRn.
             rewrite <- mult_IZR in IZRnlto.
             destruct n.
             reflexivity.
             apply lt_IZR in oltIZRn.
             apply lt_IZR in IZRnlto.
             lia.
             apply lt_IZR in oltIZRn.
             apply lt_IZR in IZRnlto.
             lia. }
           rewrite IZRneq0 in *.
           autorewrite with null in *.
           clear IZRneq0 atub atlb.
           apply Rmult_integral in t1eqt2.
           destruct t1eqt2 as [ctr |atn0]; try lra.
           assert (x/r < 0) as xrlt0. {
             rewrite <- RmultRinv.
             setl (- (x * / - r)).
             assumption.
             setr (-0).
             apply Ropp_lt_contravar.
             zltab.
             lra. }
           apply atan_increasing in xrlt0.
           rewrite atan_0, atn0 in xrlt0.
           lra.
       +++ destruct (total_order_T 0 (2 * r - y)) as [[zlta|zeqa]|zgta].
           ++++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                      / (2 * r - y))) in *.
                assert (Q - 2 * 1 * PI + IZR (2 * n) * PI =
                        Q + IZR (2 * (n-1)) * PI) as id. {
                  repeat rewrite mult_IZR.
                  rewrite minus_IZR.
                  field. }
                rewrite id in t1eqt2.
                unfold Q in *. clear Q id.
                t1t2L.
                assert (0 < x + D) as xDgt0. {
                  specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
                    change (0 <= D) in xDnn;
                    lra. }
                cne0.
           ++++ specialize PI_RGT_0 as pigt0.
                assert (atan (y / (2 * x)) = PI / 2 + IZR (n-1) * PI)
                  as at2d. {
                  apply (Rmult_eq_reg_l 2); [|lra].
                  rewrite Rmult_plus_distr_l, t1eqt2.
                  rewrite mult_IZR, minus_IZR.
                  field. }
                specialize (atan_bound (y / (2 * x))) as [lb ub].
                rewrite at2d in ub,lb.
                destruct (n - 1)%Z.
                - lra.
                - specialize (IZRposge1 p) as ps.
                  clear - ps ub pigt0.
                  apply (Rmult_lt_compat_l 2) in ub; [|lra].
                  assert (1 + 2 * IZR (Z.pos p) < 1) as id. {
                    apply (Rmult_lt_reg_r PI); try assumption.
                    rewrite Rmult_plus_distr_r.
                    setl (2 * (PI / 2 + IZR (Z.pos p) * PI)).
                    setr (2 * (PI / 2)).
                    assumption. }
                  lra.
                - specialize (IZRneglen1 p) as ps.
                  clear - ps lb pigt0.
                  apply (Rmult_lt_compat_l 2) in lb; [|lra].
                  assert (-1 < 1 + 2 * IZR (Z.neg p)) as id. {
                    apply (Rmult_lt_reg_r PI); try assumption.
                    rewrite Rmult_plus_distr_r.
                    setr (2 * (PI / 2 + IZR (Z.neg p) * PI)).
                    setl (2 * (- PI / 2)).
                    assumption. }
                  lra.
           ++++ t1t2L.
                assert (0 < x + D) as xDgt0. {
                  specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
                    change (0 <= D) in xDnn;
                    lra. }
                cne0.
    ++ destruct (total_order_T 0 y) as [[zlty|zeqy]|zgty].
       +++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           set (R := 2 * atan ((x - sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           rename t1eqt2 into eq.
           assert (R = Q + IZR (2 * (n+1)) * PI) as id. {
             apply (Rplus_eq_reg_r (- 2 * 1 * PI)).
             rewrite Z.mul_add_distr_l.
             rewrite plus_IZR.
             rewrite (mult_IZR 2 1).
             lrag eq. }
           unfold R, Q in *.
           clear R Q eq.
           t1t2L.
           destruct (total_order_T 0 (2 * r - y))
             as [[zlta|zeqa]|zgta]; try lra.
           assert (0 < x + D) as zltxD. {
             specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
               change (0 <= D) in xDnn.
             destruct xDnn as [zltD | zeqD].
             lra.
             exfalso.
             unfold D in zeqD.
             rewrite <- sqrt_0 in zeqD.
             apply sqrt_inj in zeqD.
             rewrite <- zeqx, Rsqr_0, Rminus_0_l, <- Ropp_0 in zeqD.
             apply Ropp_eq_compat in zeqD.
             repeat rewrite Ropp_involutive in zeqD.
             symmetry in zeqD.
             apply Rmult_integral in zeqD.
             destruct zeqD; lra.
             right. reflexivity.
             rewrite <- zeqx, Rsqr_0, Rminus_0_l.
             setr (- (2*r-y)*y).
             apply Rmult_le_pos; [lra |left; assumption]. }
           cne0.
       +++ apply straightcond in phase.
           rewrite <- zeqx, <- zeqy, Rsqr_0, Rmult_0_r,
               Rplus_0_r in phase.
           clear - phase.
           lra.
       +++ destruct (total_order_T 0 (2 * r - y)) as [[zlta|zeqa]|zgta].
           ++++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                      / (2 * r - y))) in *.
                assert (Q - 2 * 1 * PI + IZR (2 * n) * PI =
                        Q + IZR (2 * (n-1)) * PI) as id. {
                  repeat rewrite mult_IZR.
                  rewrite minus_IZR.
                  field. }
                rewrite id in t1eqt2.
                unfold Q in *. clear Q id.
                t1t2L.
                assert (0 < x + D) as xDgt0. {
                  specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
                    change (0 <= D) in xDnn.
                  destruct xDnn as [zltD |zeqD].
                  lra.
                  exfalso.
                  unfold D in zeqD.
                  rewrite <- sqrt_0 in zeqD.
                  apply sqrt_inj in zeqD.
                  rewrite <- zeqx, Rsqr_0, Rminus_0_l, <- Ropp_0 in zeqD.
                  apply Ropp_eq_compat in zeqD.
                  repeat rewrite Ropp_involutive in zeqD.
                  symmetry in zeqD.
                  apply Rmult_integral in zeqD.
                  destruct zeqD; lra.
                  right. reflexivity.
                  rewrite <- zeqx, Rsqr_0, Rminus_0_l.
                  setr ((2*r-y)*- y).
                  apply Rmult_le_pos; [left; assumption|lra].  }
                cne0.
           ++++ apply straightcond in phase.
                rewrite <- zeqx in phase.
                autorewrite with null in *.
                unfold Rsqr in phase.
                symmetry in zeqa.
                apply Rminus_diag_uniq_sym in zeqa.
                assert (2 * r < 2 * r) as cnt. {
                  rewrite <- zeqa at 1.
                  apply (Rmult_lt_reg_r (-y)); try lra. }
                lra.
                
           ++++ t1t2L.
                assert (0 < x + D) as xDgt0. {
                  specialize (sqrt_pos (x² - (2 * r - y) * y)) as xDnn;
                    change (0 <= D) in xDnn.
                  destruct xDnn as [zltD |zeqD].
                  lra.
                  exfalso.
                  unfold D in zeqD.
                  rewrite <- sqrt_0 in zeqD.
                  apply sqrt_inj in zeqD.
                  rewrite <- zeqx, Rsqr_0, Rminus_0_l, <- Ropp_0 in zeqD.
                  apply Ropp_eq_compat in zeqD.
                  repeat rewrite Ropp_involutive in zeqD.
                  symmetry in zeqD.
                  apply straightcond in phase.
                  rewrite <- zeqx, Rsqr_0, Rplus_0_l in phase.
                  assert (2 * r * y = y²) as contr. {
                    apply (Rplus_eq_reg_r (- y²)).
                    setr 0. setl ((2 * r - y) * y).
                    assumption. }
                  rewrite contr in phase.
                  clear - phase.
                  lra.
                  right. reflexivity.
                  left.
                  apply straightcond in phase.
                  clear - phase.
                  rewrite Rmult_minus_distr_r.
                  apply (Rplus_lt_reg_r (2 * r * y)).
                  rewrite Rplus_0_l.
                  setr (x² + y²). assumption. }
                cne0.
    ++ destruct (total_order_T 0 y) as [[zlty|zeqy]|zgty].
       +++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           set (R := 2 * atan ((x - sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           rename t1eqt2 into eq.
           assert (R = Q + IZR (2 * (n+1)) * PI) as id. {
             apply (Rplus_eq_reg_r (- 2 * 1 * PI)).
             rewrite Z.mul_add_distr_l.
             rewrite plus_IZR.
             rewrite (mult_IZR 2 1).
             lrag eq. }
           unfold R, Q in *.
           clear R Q eq.
           t1t2L.
           destruct (total_order_T 0 (2 * r - y))
             as [[zlta|zeqa]|zgta]; try lra.
           assert (0 < x + D) as zltxD. {
             apply (Rplus_lt_reg_r (-x)).
             setl (-x). setr D.
             unfold D.
             rewrite <- (sqrt_Rsqr (-x)); [|left; lra].
             apply sqrt_lt_1.
             apply Rle_0_sqr.
             left.
             apply straightcond in phase.
             clear - phase.
             rewrite Rmult_minus_distr_r.
             apply (Rplus_lt_reg_r (2 * r * y)).
             rewrite Rplus_0_l.
             setr (x² + y²). assumption.
             rewrite <- Rsqr_neg.
             apply (Rplus_lt_reg_r (-x*x)).
             setl 0. setr ((- (2*r-y)*y)).
             apply Rmult_lt_0_compat; lra. }
           cne0.
       +++ set (Q := ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y))) in *.
           rename t1eqt2 into eq.
           assert (atan Q = 0 + IZR n * PI) as t1eqt2. {
             apply (Rmult_eq_reg_l 2); [|lra].
             apply (Rplus_eq_reg_r (- 2 * 1 * PI)).
             setl (2 * atan Q - 2 * 1 * PI).
             rewrite eq.
             rewrite mult_IZR.
             field. }
           clear eq.
           destruct (total_order_T 0 (2 * r - y))
             as [[zlta|zeqa]|zgta]; try lra.
           apply (f_equal tan) in t1eqt2.
           rewrite atan_right_inv, tan_period, tan_0 in t1eqt2;
             [|rewrite cos_0 ; discrR].
           unfold Q in t1eqt2.
           clear Q.
           rename t1eqt2 into c.
           rewrite <- Ropp_0 in c.
           assert ((x - sqrt (x² - (2 * r - y) * y)) / (2 * r - y) =
                   - ((x - sqrt (x² - (2 * r - y) * y)) / - (2 * r - y)))
             as id. field. lra. rewrite id in c. clear id.
           apply Ropp_eq_compat in c.
           repeat rewrite Ropp_involutive in c.
           rewrite <- signeq0_eqv in c.
           rewrite sign_eq_pos_den in c;
             [ rewrite signeq0_eqv in c|].
           rewrite <- zeqy, Rmult_0_r, Rminus_0_r, Rsqr_neg, sqrt_Rsqr in c;
           lra.
           lra.
       +++ destruct (total_order_T 0 (2 * r - y)) as [[zlta|zeqa]|zgta].
           ++++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                      / (2 * r - y))) in *.
                assert (Q - 2 * 1 * PI + IZR (2 * n) * PI =
                        Q + IZR (2 * (n-1)) * PI) as id. {
                  repeat rewrite mult_IZR.
                  rewrite minus_IZR.
                  field. }
                rewrite id in t1eqt2. unfold Q in *. clear Q id.
                t1t2L.
                assert (0 < x + D) as zltxD. {
                  apply (Rplus_lt_reg_r (-x)).
                  setl (-x). setr D.
                  unfold D.
                  rewrite <- (sqrt_Rsqr (-x)); [|left; lra].
                  apply sqrt_lt_1.
                  apply Rle_0_sqr.
                  left.
                  apply straightcond in phase.
                  clear - phase.
                  rewrite Rmult_minus_distr_r.
                  apply (Rplus_lt_reg_r (2 * r * y)).
                  rewrite Rplus_0_l.
                  setr (x² + y²). assumption.
                  rewrite <- Rsqr_neg.
                  apply (Rplus_lt_reg_r (-x*x)).
                  setl 0. setr (((2*r-y)*- y)).
                  apply Rmult_lt_0_compat; lra. }
                cne0. 
           ++++ specialize PI_RGT_0 as pigt0.
                assert (atan (y / (2 * x)) = PI / 2 + IZR (-n) * PI)
                  as at2d. {
                  apply (Rmult_eq_reg_l 2); [|lra].
                  apply (Rplus_eq_reg_r (- 2 * 1 * PI + IZR (2 * n) * PI)).
                  symmetry.
                  repeat rewrite mult_IZR in *.
                  rewrite opp_IZR.
                  lrag t1eqt2.  }
                specialize (atan_bound (y / (2 * x))) as [lb ub].
                rewrite at2d in ub,lb.
                destruct (-n)%Z.
                - lra.
                - specialize (IZRposge1 p) as ps.
                  clear - ps ub pigt0.
                  apply (Rmult_lt_compat_l 2) in ub; [|lra].
                  assert (1 + 2 * IZR (Z.pos p) < 1) as id. {
                    apply (Rmult_lt_reg_r PI); try assumption.
                    rewrite Rmult_plus_distr_r.
                    setl (2 * (PI / 2 + IZR (Z.pos p) * PI)).
                    setr (2 * (PI / 2)).
                    assumption. }
                  lra.
                - specialize (IZRneglen1 p) as ps.
                  clear - ps lb pigt0.
                  apply (Rmult_lt_compat_l 2) in lb; [|lra].
                  assert (-1 < 1 + 2 * IZR (Z.neg p)) as id. {
                    apply (Rmult_lt_reg_r PI); try assumption.
                    rewrite Rmult_plus_distr_r.
                    setr (2 * (PI / 2 + IZR (Z.neg p) * PI)).
                    setl (2 * (- PI / 2)).
                    assumption. }
                  lra.
           ++++ set (Q := 2 * atan ((x + sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
                set (R := 2 * atan ((x - sqrt (x² - (2 * r - y) * y))
                                 / (2 * r - y))) in *.
           rename t1eqt2 into eq.
           assert (R = Q + IZR (2 * n) * PI) as id. {
             apply (Rplus_eq_reg_r (- 2 * 1 * PI)).
             lrag eq. }
           unfold R, Q in *.
           clear R Q eq.
           t1t2L.
           assert (x + D < 0) as zltxD. {
             apply (Rplus_lt_reg_r (-x)).
             setr (-x). setl D.
             unfold D.
             rewrite <- (sqrt_Rsqr (-x)); [|left; lra].
             apply sqrt_lt_1.

             apply straightcond in phase.
             clear - phase.
             rewrite Rmult_minus_distr_r.
             left.
             apply (Rplus_lt_reg_r (2 * r * y)).
             lrag phase.
             apply Rle_0_sqr.
             rewrite <- Rsqr_neg.
             apply (Rplus_lt_reg_r (- x * x)).
             setr (-0). setl (- (- (2*r-y) * - y)).
             apply Ropp_lt_contravar.
             apply Rmult_lt_0_compat; lra. }
           cne0.
Qed.
  

Lemma k2_theta1_even :
  forall x y r
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x y),
    exists q, κ₂ x y r (θ1 x y r) = (θ1 x y r) + 2 * IZR q * PI.
Proof.
  intros.
  assert (exists m, κ₂ x y r (θ1 x y r) = θ1 x y r + IZR m * PI) as [m k2d].
  apply (theta1_theta2_k2 0%Z); try assumption.
  left. field.
  destruct (Zeven_odd_dec m).
  + apply Zeven_ex in z as [n mdef].
    exists n.
    rewrite <- mult_IZR.
    rewrite <- mdef.
    assumption.
  + exfalso.
    generalize z; intro zodd.
    apply Zodd_ex in z as [n mdef].
    rewrite mdef in *.
    clear mdef m.
    assert (exists m,  κ₂ x y r (θ1 x y r) =
                       θ1 x y r + IZR (2 * m + 1) * PI) as k2d2. {
      exists n. assumption. }
    apply theta2_odd in k2d2; try assumption.
    clear - k2d2 phase rne0.
    destruct k2d2 as [n k2d].
    apply (theta1_ne_theta2 _ _ _ n rne0 phase).
    assumption.
Qed.

Lemma k2_theta2_odd :
  forall x y r
         (rne0 : r <> 0)
         (phase : straight r 0 0 0 x y),
    (exists n : Z, κ₂ x y r (θ2 x y r) =
                   (θ2 x y r) + IZR (2 * n + 1) * PI).
Proof.
  intros.
  assert (exists m, κ₂ x y r (θ2 x y r) = θ2 x y r + IZR m * PI) as [m k2d].
  apply (theta1_theta2_k2 0%Z); try assumption.
  right. field.
  destruct (Zeven_odd_dec m).
  + exfalso.
    generalize z; intro zeven.
    apply Zeven_ex in z as [n mdef].
    rewrite mdef in *.
    clear mdef m.
    assert (exists m,  κ₂ x y r (θ2 x y r) =
                       θ2 x y r + IZR (2 * m) * PI) as k2d2. {
      exists n. assumption. }
    apply theta1_even in k2d2; try assumption.
    clear - k2d2 phase rne0.
    destruct k2d2 as [n k2d].
    apply (theta1_ne_theta2 _ _ _ (-n)%Z rne0 phase).
    rewrite k2d, mult_IZR, mult_IZR, opp_IZR.
    field.
  + apply Zodd_ex in z as [n mdef].
    exists n.
    rewrite <- mdef.
    assumption.
Qed.

