import Foundation.RiemannSixthFarAnnulus
/-! Full fixed-neighborhood signed Gaussian asymptotics for actual A6
saddles, combining the central piece with both signed annuli exactly. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarGaussianFixed
open RiemannSixthFarAnnulus RiemannSixthFarGaussianLimit RiemannQuarticErrorLimits
open RiemannSixthFarRemainder RiemannSixthFarGaussianLocal
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight

private theorem actual_weight_continuousOn (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x)
    (w v : ℂ) (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (z : ℂ)
    (R : ℝ) (hR : R < 1/16) :
    ContinuousOn (fun s : ℝ => weight 3 t z (v+(s : ℂ))) (Icc (-R) R) := by
  intro s h
  have hd := horizontal_neighbor_domain t x ht hx w v hr hi hs hp hv s
    ((abs_le.mpr h).trans hR.le)
  have hk := RiemannThetaComplexKernel.kernelComplex_analyticAt (v+(s : ℂ))
    (by linarith [hd.2.1])
  have hw : AnalyticAt ℂ (weight 3 t z) (v+(s : ℂ)) := by
    unfold weight
    apply AnalyticAt.mul
    · fun_prop
    · exact hk
  have hc : ContinuousAt (fun a : ℝ => weight 3 t z (v+(a : ℂ))) s :=
    ContinuousAt.comp (g := weight 3 t z) (f := fun a : ℝ => v+(a : ℂ))
      hw.continuousAt (by fun_prop)
  exact hc.continuousWithinAt

theorem actual_neighborhood_split (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x)
    (w v : ℂ) (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (z : ℂ)
    (r R : ℝ) (hr0 : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1/16) :
    (∫ s : ℝ in -R..R, weight 3 t z (v+(s : ℂ)))=
      (∫ s : ℝ in -r..r, weight 3 t z (v+(s : ℂ)))+
      (∫ s : ℝ in r..R, weight 3 t z (v+((-s : ℝ) : ℂ)))+
      (∫ s : ℝ in r..R, weight 3 t z (v+(s : ℂ))) := by
  let f := fun s : ℝ => weight 3 t z (v+(s : ℂ))
  have hc := actual_weight_continuousOn t x ht hx w v hr hi hs hp hv z R hR
  have hf (a b : ℝ) (ha : a ∈ Icc (-R) R) (hb : b ∈ Icc (-R) R) :
      IntervalIntegrable f volume a b :=
    (hc.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have hR0 : 0 ≤ R := hr0.trans hrR
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hf (-R) (-r) ⟨le_rfl,by linarith⟩ ⟨by linarith,by linarith⟩)
    (hf (-r) r ⟨by linarith,by linarith⟩ ⟨by linarith,hrR⟩)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hf (-R) r ⟨le_rfl,by linarith⟩ ⟨by linarith,hrR⟩)
    (hf r R ⟨by linarith,hrR⟩ ⟨by linarith,le_rfl⟩)
  have hneg := intervalIntegral.integral_comp_neg (a := r) (b := R) f
  change (∫ s : ℝ in -R..R, f s)=(∫ s : ℝ in -r..r, f s)+
    (∫ s : ℝ in r..R, f (-s))+(∫ s : ℝ in r..R, f s)
  linear_combination -h2-h1-hneg

theorem eventually_uniform_fixed_gaussian_error (R η : ℝ) (hR0 : 0 < R)
    (hR : R ≤ 1/8192) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      4096 ≤ w.re → |w.im| ≤ 1/2 → 10000*(t*(‖w‖+1)^5+1) ≤ x →
      modelDerivative 3 t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope 3 t v= -(Complex.I*z) →
      ‖(∫ s : ℝ in -R..R, weight 3 t z (v+(s : ℂ)))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  filter_upwards [eventually_uniform_local_gaussian_error (η/4) (by positivity),
    eventually_uniform_relative_annulus R (η/4) hR0 hR (by positivity),
    eventually_ge_atTop (10000 : ℝ),
    centralRadius_tendsto_zero.eventually (gt_mem_nhds hR0)] with x hlocal hann hx hradius
  intro t ht w v hr hi hp hs hv z hz
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 5]
  have hspl := actual_neighborhood_split t x ht (by linarith) w v (by linarith) hi hs hp0 hv z
    (centralRadius x) R (Real.rpow_pos_of_pos (by linarith : 0 < x) _).le hradius.le (by linarith)
  have hc := hlocal t ht w v hr hi hp hs hv z hz
  have hl := hann t ht w v hr hi hp hs hv z hz (-1) (by norm_num)
  have hu := hann t ht w v hr hi hp hs hv z hz 1 (by norm_num)
  simp only [neg_one_mul,one_mul] at hl hu
  let D := weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2))
  let C := ∫ s : ℝ in -(centralRadius x)..centralRadius x, weight 3 t z (v+(s : ℂ))
  let L := ∫ s : ℝ in centralRadius x..R, weight 3 t z (v+((-s : ℝ) : ℂ))
  let U := ∫ s : ℝ in centralRadius x..R, weight 3 t z (v+(s : ℂ))
  change ‖C/D-1‖ ≤ η/4 at hc
  change ‖L/D‖ ≤ η/4 at hl
  change ‖U/D‖ ≤ η/4 at hu
  rw [hspl]
  change ‖(C+L+U)/D-1‖ ≤ η
  have hid : (C+L+U)/D-1=(C/D-1)+L/D+U/D := by ring
  rw [hid]
  have h1 := norm_add_le (C/D-1) (L/D)
  have h2 := norm_add_le ((C/D-1)+L/D) (U/D)
  linarith

theorem fixed_relative_limit_for_saddle_family (t : ℝ) (ht : 1 ≤ t)
    (R : ℝ) (hR0 : 0 < R) (hR : R ≤ 1/8192) (w v z : ℝ → ℂ)
    (hdata : ∀ᶠ x : ℝ in atTop, 4096 ≤ (w x).re ∧ |(w x).im| ≤ 1/2 ∧
      10000*(t*(‖w x‖+1)^5+1) ≤ x ∧ modelDerivative 3 t (w x)= -(Complex.I*(x : ℂ)) ∧
      ‖v x-w x‖ ≤ 1/x ∧ complexSlope 3 t (v x)= -(Complex.I*z x)) :
    Tendsto (fun x : ℝ =>
      (∫ s : ℝ in -R..R, weight 3 t (z x) (v x+(s : ℂ)))/
        (weight 3 t (z x) (v x)*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) (v x)*(s : ℂ)^2/2))))
      atTop (nhds (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [eventually_uniform_fixed_gaussian_error R (η/2) hR0 hR (by positivity),hdata]
    with x herror hdatax
  obtain ⟨hr,hi,hp,hs,hv,hstat⟩ := hdatax
  have h := herror t ht (w x) (v x) hr hi hp hs hv (z x) hstat
  have hlt := lt_of_le_of_lt h (by linarith : η/2 < η)
  simpa only [dist_eq_norm] using hlt

theorem exists_uniform_actual_fixed_gaussian (R : ℝ) (hR0 : 0 < R) (hR : R ≤ 1/8192) :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ t u x : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x →
      ∃ w : ℂ, 10000 ≤ x ∧ 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
        10000*(t*(‖w‖+1)^5+1) ≤ x ∧ modelDerivative 3 t w = -(Complex.I*(x : ℂ)) ∧
        ∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ 1 → ∃ v : ℂ,
          v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*z) ∧
          1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ weight 3 t z v ≠ 0 ∧
          weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 ∧
          ‖(∫ s : ℝ in -(R)..R, weight 3 t z (v+(s : ℂ)))/
            (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  obtain ⟨K,hK,hconstruct⟩ := RiemannSixthUniformFarSaddles.exists_uniform_actual_far_frequency_disks
  refine ⟨K,hK,?_⟩
  intro η hη
  obtain ⟨X,hX⟩ := eventually_atTop.mp (eventually_uniform_fixed_gaussian_error R η hR0 hR hη)
  refine ⟨X,?_⟩
  intro t u x ht hu hstat hx
  have hxK := (le_max_right X (K*RiemannQuarticTransitionSaddle.realScale u)).trans hx
  have hxX := (le_max_left X (K*RiemannQuarticTransitionSaddle.realScale u)).trans hx
  obtain ⟨w,hxlarge,hr,hi,hp,hs,hroots⟩ := hconstruct t u x ht hu hstat hxK
  refine ⟨w,hxlarge,hr,hi,hp,hs,?_⟩
  intro z hz
  obtain ⟨v,⟨hv,hvstat⟩,_⟩ := hroots z hz
  have hd := RiemannSixthFarAnalyticBranch.corrected_saddle_geometry
    t x ht hxlarge w hr hi hp hs v hv
  have hvdist : ‖v-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hn := gaussian_normalization_lower t x ht hxlarge w v (by linarith) hi hp hs hvdist
  have hG : (∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 := by
    intro h
    rw [h,norm_zero,mul_zero] at hn
    norm_num at hn
  have hW : weight 3 t z v ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hd.2.2
  exact ⟨v,hv,hvstat,hd.1,hd.2.1,hW,mul_ne_zero hW hG,
    hX x hxX t ht w v (by linarith) hi hp hs hvdist z hvstat⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarGaussianFixed
