import Foundation.RiemannQuarticFarAnnulus
/-! Fixed horizontal neighborhoods of actual far Xi saddles.
Exact interval splitting combines the shrinking central approximation with
both signed actual annuli. Farther contour pieces remain separate. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarGaussianFixed
open RiemannQuarticFarAnnulus RiemannQuarticFarGaussianLimit RiemannQuarticErrorLimits
open RiemannQuarticFarRemainder RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch
open RiemannQuarticFrequencyBranch

private theorem actual_weight_continuousOn (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x)
    (w v : ℂ) (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (z : ℂ)
    (R : ℝ) (hR : R < 1/16) :
    ContinuousOn (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) (Icc (-R) R) := by
  intro s h
  have hd := horizontal_neighbor_domain t x ht hx w v hr hi hs hp hv s
    ((abs_le.mpr h).trans hR.le)
  have hk := RiemannThetaComplexKernel.kernelComplex_analyticAt (v+(s : ℂ))
    (by linarith [hd.2.1])
  have hw : AnalyticAt ℂ (saddleWeight t z) (v+(s : ℂ)) := by
    unfold saddleWeight
    apply AnalyticAt.mul
    · fun_prop
    · exact hk
  have hc : ContinuousAt (fun a : ℝ => saddleWeight t z (v+(a : ℂ))) s :=
    ContinuousAt.comp (g := saddleWeight t z) (f := fun a : ℝ => v+(a : ℂ))
      hw.continuousAt (by fun_prop)
  exact hc.continuousWithinAt

theorem actual_neighborhood_split (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x)
    (w v : ℂ) (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (z : ℂ)
    (r R : ℝ) (hr0 : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1/16) :
    (∫ s : ℝ in -R..R, saddleWeight t z (v+(s : ℂ)))=
      (∫ s : ℝ in -r..r, saddleWeight t z (v+(s : ℂ)))+
      (∫ s : ℝ in r..R, saddleWeight t z (v+((-s : ℝ) : ℂ)))+
      (∫ s : ℝ in r..R, saddleWeight t z (v+(s : ℂ))) := by
  let f := fun s : ℝ => saddleWeight t z (v+(s : ℂ))
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
      64 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ x →
      modelDerivative t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope t v= -(Complex.I*z) →
      ‖(∫ s : ℝ in -R..R, saddleWeight t z (v+(s : ℂ)))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  filter_upwards [eventually_uniform_local_gaussian_error (η/4) (by positivity),
    eventually_uniform_relative_annulus R (η/4) hR0 hR (by positivity),
    eventually_ge_atTop (10000 : ℝ),
    centralRadius_tendsto_zero.eventually (gt_mem_nhds hR0)] with x hlocal hann hx hradius
  intro t ht w v hr hi hp hs hv z hz
  have ht0 : 0 ≤ t := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hspl := actual_neighborhood_split t x ht (by linarith) w v (by linarith) hi hs hp0 hv z
    (centralRadius x) R (Real.rpow_pos_of_pos (by linarith : 0 < x) _).le hradius.le (by linarith)
  have hc := hlocal t ht w v hr hi hp hs hv z hz
  have hl := hann t ht w v hr hi hp hs hv z hz (-1) (by norm_num)
  have hu := hann t ht w v hr hi hp hs hv z hz 1 (by norm_num)
  simp only [neg_one_mul,one_mul] at hl hu
  let D := saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
  let C := ∫ s : ℝ in -(centralRadius x)..centralRadius x, saddleWeight t z (v+(s : ℂ))
  let L := ∫ s : ℝ in centralRadius x..R, saddleWeight t z (v+((-s : ℝ) : ℂ))
  let U := ∫ s : ℝ in centralRadius x..R, saddleWeight t z (v+(s : ℂ))
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

theorem eventually_actual_fixed_gaussian (t : ℝ) (ht : 1 ≤ t) (R η : ℝ)
    (hR0 : 0 < R) (hR : R ≤ 1/8192) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∃ w v : ℂ,
      modelDerivative t w= -(Complex.I*(x : ℂ)) ∧ complexSlope t v= -(Complex.I*(x : ℂ)) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ RiemannThetaComplexKernel.kernelComplex v ≠ 0 ∧
      ‖(∫ s : ℝ in -R..R, saddleWeight t (x : ℂ) (v+(s : ℂ)))/
        (saddleWeight t (x : ℂ) v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  filter_upwards [eventually_controlled_far_saddles t ht,
    eventually_uniform_fixed_gaussian_error R η hR0 hR hη] with x hdata herror
  obtain ⟨hx,w,v,hr,hi,hp,hs,hv,hstat,hvre,hvim,hkn⟩ := hdata
  exact ⟨w,v,hs,hstat,hvre,hvim,hkn,herror t ht w v (by linarith) hi hp hs hv (x : ℂ) hstat⟩

theorem fixed_relative_limit_for_saddle_family (t : ℝ) (ht : 1 ≤ t)
    (R : ℝ) (hR0 : 0 < R) (hR : R ≤ 1/8192) (w v z : ℝ → ℂ)
    (hdata : ∀ᶠ x : ℝ in atTop, 64 ≤ (w x).re ∧ |(w x).im| ≤ 1/2 ∧
      100*(t*(‖w x‖+1)^3+1) ≤ x ∧ modelDerivative t (w x)= -(Complex.I*(x : ℂ)) ∧
      ‖v x-w x‖ ≤ 1/x ∧ complexSlope t (v x)= -(Complex.I*z x)) :
    Tendsto (fun x : ℝ =>
      (∫ s : ℝ in -R..R, saddleWeight t (z x) (v x+(s : ℂ)))/
        (saddleWeight t (z x) (v x)*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) (v x)*(s : ℂ)^2/2))))
      atTop (nhds (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [eventually_uniform_fixed_gaussian_error R (η/2) hR0 hR (by positivity),hdata]
    with x herror hdatax
  obtain ⟨hr,hi,hp,hs,hv,hstat⟩ := hdatax
  have h := herror t ht (w x) (v x) hr hi hp hs hv (z x) hstat
  have hlt := lt_of_le_of_lt h (by linarith : η/2 < η)
  simpa only [dist_eq_norm] using hlt

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarGaussianFixed
