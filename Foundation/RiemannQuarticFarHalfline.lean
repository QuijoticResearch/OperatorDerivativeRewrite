import Foundation.RiemannQuarticFarLeftAnnulus
/-! Exact assembly of actual horizontal half-line saddle integrals.
This controls one arithmetic horizontal contribution under the explicit
far-saddle hypotheses, not zeros of the full opposite-frequency pair. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarHalfline
open RiemannQuarticFarLeftAnnulus RiemannQuarticFarLeftCompact RiemannQuarticFarRightTail
open RiemannQuarticFarGaussianLimit RiemannQuarticFarGaussianFixed RiemannQuarticFarCorrection
open RiemannQuarticNaturalContour RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch
open RiemannQuarticFrequencyBranch

theorem horizontal_decomposition (t : ℝ) (z v : ℂ) (hh : |v.im| < Real.pi/8) (R : ℝ)
    (hRight : IntegrableOn (fun s : ℝ => saddleWeight t z (v+(s : ℂ))) (Ioi R)) :
    (∫ s : ℝ in Ioi 0, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))=
      (∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))+
      (∫ s : ℝ in -1..-R, saddleWeight t z (v+(s : ℂ)))+
      (∫ s : ℝ in -R..R, saddleWeight t z (v+(s : ℂ)))+
      (∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ))) := by
  let a := v.re
  let F := fun s : ℝ => saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let f := fun s : ℝ => saddleWeight t z (v+(s : ℂ))
  have hfun : f=(fun s : ℝ => F (s+a)) := by
    funext s
    dsimp [f,F,a]
    rw [Complex.ofReal_add]
    congr 1
    apply Complex.ext <;> simp <;> ring
  have hc : Continuous f := by
    rw [hfun]
    exact (shifted_weight_continuous t z v.im hh).comp (continuous_id.add_const a)
  have hIndicator : (fun s : ℝ => (Ioi (0 : ℝ)).indicator F (s+a))=(Ioi (-a)).indicator f := by
    funext s
    by_cases h : s ∈ Ioi (-a)
    · have h' : s+a ∈ Ioi (0 : ℝ) := by change -a < s at h; change 0 < s+a; linarith
      rw [indicator_of_mem h',indicator_of_mem h]
      exact (congrFun hfun s).symm
    · have h' : s+a ∉ Ioi (0 : ℝ) := by
        intro h'
        apply h
        change -a < s
        change 0 < s+a at h'
        linarith
      rw [indicator_of_notMem h',indicator_of_notMem h]
  have hshift : (∫ s : ℝ, (Ioi (0 : ℝ)).indicator F (s+a)) =
      (∫ s : ℝ, (Ioi (0 : ℝ)).indicator F s) :=
    integral_add_right_eq_self (fun s : ℝ => (Ioi (0 : ℝ)).indicator F s) a
  rw [hIndicator] at hshift
  simp only [integral_indicator measurableSet_Ioi] at hshift
  have hfirst : (∫ s : ℝ in -a..-1, f s)=(∫ s : ℝ in 0..a-1, F s) := by
    rw [hfun]
    have h := intervalIntegral.integral_comp_add_right (a := -a) (b := (-1 : ℝ)) F a
    simpa only [neg_add_cancel,show (-1 : ℝ)+a=a-1 by ring] using h
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) (-a) (-1)) (hc.intervalIntegrable (μ := volume) (-1) (-R))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) (-a) (-R)) (hc.intervalIntegrable (μ := volume) (-R) R)
  have h3 := intervalIntegral.integral_interval_add_Ioi' (hc.intervalIntegrable (μ := volume) (-a) R) hRight
  change (∫ s : ℝ in Ioi 0, F s)=(∫ s : ℝ in 0..a-1, F s)+
    (∫ s : ℝ in -1..-R, f s)+(∫ s : ℝ in -R..R, f s)+(∫ s : ℝ in Ioi R, f s)
  linear_combination -hshift-h3-h2-h1+hfirst

theorem eventually_uniform_horizontal_gaussian_error (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ x →
      modelDerivative t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope t v= -(Complex.I*z) → |z.im| ≤ 1 →
      IntegrableOn (fun s : ℝ => saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
      ‖(∫ s : ℝ in Ioi 0, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  let R : ℝ := 1/8192
  have hR : 0 < R := by norm_num [R]
  filter_upwards [eventually_uniform_relative_left_compact (η/8) (by positivity),
    eventually_uniform_relative_left_annulus R (η/8) hR (by norm_num [R]) (by positivity),
    eventually_uniform_fixed_gaussian_error R (η/8) hR (by norm_num [R]) (by positivity),
    eventually_uniform_relative_right_tail R (η/8) hR (by positivity),
    eventually_ge_atTop (10000 : ℝ),eventually_ge_atTop (100000000/R)]
    with x hcompact hleft hcenter hright hx hxR
  intro t ht w v hr hi hp hs hv z hz hzim
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hgeom := corrected_saddle_geometry t x ht hx w v hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have he := arithmetic_error_frequency_bound t x ht hx w hp hs
  have heR : 100000000/x ≤ R := by
    apply (div_le_iff₀ hx0).mpr
    have hm := (div_le_iff₀ hR).mp hxR
    nlinarith
  have hw3 : 16 ≤ w.re^3 := by
    have hw2 : 1 ≤ w.re^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hw2 (by linarith : 0 ≤ w.re)]
  have hwt : w.re^3 ≤ t*w.re^3 := by nlinarith
  have hsmall : 30005*Real.exp (-4*w.re+4) ≤ (t*w.re^3/16)*R := by
    have hm := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ t*w.re^3/16) hR.le
    linarith
  have htail := (actual_right_tail_bound t x ht (by linarith) w v (by linarith) hi hs hp0 hv z hz R hR hsmall).1
  refine ⟨shifted_weight_integrable t z v.im hgeom.2.1,?_⟩
  have hsplit := horizontal_decomposition t z v hgeom.2.1 R htail
  have hC := hcompact t ht w v hr hi hp hs hv z hz hzim
  have hL := hleft t ht w v hr hi hp hs hv z hz
  have hM := hcenter t ht w v (by linarith) hi hp hs hv z hz
  have hT := hright t ht w v (by linarith) hi hp hs hv z hz
  let D := saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
  let C := ∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let L := ∫ s : ℝ in -1..-R, saddleWeight t z (v+(s : ℂ))
  let M := ∫ s : ℝ in -R..R, saddleWeight t z (v+(s : ℂ))
  let T := ∫ s : ℝ in Ioi R, saddleWeight t z (v+(s : ℂ))
  change ‖C/D‖ ≤ η/8 at hC
  change ‖L/D‖ ≤ η/8 at hL
  change ‖M/D-1‖ ≤ η/8 at hM
  change ‖T/D‖ ≤ η/8 at hT
  rw [hsplit]
  change ‖(C+L+M+T)/D-1‖ ≤ η
  rw [show (C+L+M+T)/D-1=C/D+L/D+(M/D-1)+T/D by ring]
  have h1 := norm_add_le (C/D) (L/D)
  have h2 := norm_add_le (C/D+L/D) (M/D-1)
  have h3 := norm_add_le (C/D+L/D+(M/D-1)) (T/D)
  linarith

theorem eventually_actual_horizontal_gaussian (t : ℝ) (ht : 1 ≤ t) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∃ w v : ℂ,
      modelDerivative t w= -(Complex.I*(x : ℂ)) ∧ complexSlope t v= -(Complex.I*(x : ℂ)) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ RiemannThetaComplexKernel.kernelComplex v ≠ 0 ∧
      IntegrableOn (fun s : ℝ => saddleWeight t (x : ℂ) ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
      ‖(∫ s : ℝ in Ioi 0, saddleWeight t (x : ℂ) ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (saddleWeight t (x : ℂ) v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ ≤ η := by
  filter_upwards [eventually_controlled_far_saddles t ht,eventually_uniform_horizontal_gaussian_error η hη]
    with x hdata herror
  obtain ⟨hx,w,v,hr,hi,hp,hs,hv,hstat,hvre,hvim,hkn⟩ := hdata
  exact ⟨w,v,hs,hstat,hvre,hvim,hkn,herror t ht w v hr hi hp hs hv (x : ℂ) hstat (by simp)⟩

theorem horizontal_relative_limit_for_saddle_family (t : ℝ) (ht : 1 ≤ t) (w v z : ℝ → ℂ)
    (hdata : ∀ᶠ x : ℝ in atTop, 120020 ≤ (w x).re ∧ |(w x).im| ≤ 1/2 ∧
      100*(t*(‖w x‖+1)^3+1) ≤ x ∧ modelDerivative t (w x)= -(Complex.I*(x : ℂ)) ∧
      ‖v x-w x‖ ≤ 1/x ∧ complexSlope t (v x)= -(Complex.I*z x) ∧ |(z x).im| ≤ 1) :
    Tendsto (fun x : ℝ =>
      (∫ s : ℝ in Ioi 0, saddleWeight t (z x) ((s : ℂ)+((v x).im : ℂ)*Complex.I))/
        (saddleWeight t (z x) (v x)*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) (v x)*(s : ℂ)^2/2))))
      atTop (nhds (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [eventually_uniform_horizontal_gaussian_error (η/2) (by positivity),hdata]
    with x herror hdatax
  obtain ⟨hr,hi,hp,hs,hv,hstat,hzim⟩ := hdatax
  have h := (herror t ht (w x) (v x) hr hi hp hs hv (z x) hstat hzim).2
  have hlt := lt_of_le_of_lt h (by linarith : η/2 < η)
  simpa only [dist_eq_norm] using hlt

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarHalfline
