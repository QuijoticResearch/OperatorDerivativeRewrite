import Foundation.CauchyPoissonFeller
/-! Actual Poisson-kernel concentration and strong continuity on C(Circle, complex).
The compact quadratic modulus applies to every continuous observable. Time is
nonnegative and the pole satisfies |q| < 1. Closed-generator identification,
path construction and entropy results are separate obligations. -/
noncomputable section
open Complex MeasureTheory ProbabilityTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonConcentration
open CauchyPoissonFlow CauchyPoissonKernelComposition CauchyPoissonMarkovKernel CauchyPoissonFeller

theorem poleLaw_coordinate (v : ℂ) (hv : ‖v‖ < 1) :
    (∫ θ, circleMap (0:ℂ) 1 θ ∂poleLaw v) = v := by
  rw [integral_poleLaw_complex v hv, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity)]
  simp only [poleWeight, mul_smul]
  rw [intervalIntegral.integral_smul]
  exact (show DiffContOnCl ℂ (fun z : ℂ => z) (Metric.ball 0 1) from
    differentiable_id.diffContOnCl).circleAverage_poissonKernel_smul (by simpa using hv)

theorem kernel_coordinate (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (z : Circle) :
    (∫ w : Circle, (w:ℂ) ∂kernel q t z) = evolution q t z := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    simp [kernel_zero, Kernel.id_apply, evolution_zero]
  · rw [kernel_positive_apply q t h z,
      integral_map Circle.exp.continuous.measurable.aemeasurable
        (show Continuous (fun w : Circle => (w:ℂ)) by fun_prop).aestronglyMeasurable]
    simpa only [circle_exp_coe] using poleLaw_coordinate _ (evolution_strict_disk q t hq h z (by simp))

theorem circle_distance_sq (w z : Circle) :
    ‖(w:ℂ)-(z:ℂ)‖^2 = 2 - 2 * ((starRingEnd ℂ (z:ℂ)) * (w:ℂ)).re := by
  have hw := Complex.sq_norm (w:ℂ)
  have hz := Complex.sq_norm (z:ℂ)
  simp only [Circle.norm_coe, one_pow] at hw hz
  rw [Complex.sq_norm]
  simp only [normSq_apply, sub_re, sub_im, mul_re, conj_re, conj_im] at *
  nlinarith

theorem kernel_distance_sq (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (z : Circle) :
    (∫ w : Circle, ‖(w:ℂ)-(z:ℂ)‖^2 ∂kernel q t z) =
      2 - 2 * ((starRingEnd ℂ (z:ℂ)) * evolution q t z).re := by
  let := kernel_markov q t hq ht
  have hi := observable_integrable q t hq ht
    (⟨fun w : Circle => (starRingEnd ℂ (z:ℂ)) * (w:ℂ), by fun_prop⟩ : C(Circle,ℂ)) z
  simp only [ContinuousMap.coe_mk] at hi
  simp_rw [circle_distance_sq]
  change (∫ w : Circle, (2:ℝ) - 2 * RCLike.re ((starRingEnd ℂ (z:ℂ)) * (w:ℂ)) ∂kernel q t z) = _
  rw [integral_sub (integrable_const (2:ℝ)) (hi.re.const_mul 2), integral_const_mul,
    integral_re hi, integral_const_mul, kernel_coordinate q t hq ht z]
  simp

theorem joint_evolution_continuous (q : ℝ) (hq : |q| < 1) :
    Continuous (fun p : {t : ℝ // 0 ≤ t} × Circle => evolution q p.1 p.2) := by
  unfold evolution flow
  apply Continuous.div (by unfold numerator decay; fun_prop) (by unfold denominator decay; fun_prop)
  intro p
  exact denominator_ne_zero q _ hq (decay_range q p.1 hq p.1.property).1
    (decay_range q p.1 hq p.1.property).2 p.2 (by simp)

def displacement (q : ℝ) (hq : |q| < 1) (t : {t : ℝ // 0 ≤ t}) : C(Circle,ℂ) :=
  ⟨fun z => evolution q t z - (z:ℂ),
    (evolution_circle_continuous q t hq t.property).sub (by fun_prop)⟩

theorem displacement_continuous (q : ℝ) (hq : |q| < 1) : Continuous (displacement q hq) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (joint_evolution_continuous q hq).sub (by fun_prop)

theorem displacement_norm_tendsto (q : ℝ) (hq : |q| < 1) :
    Filter.Tendsto (fun t : {t : ℝ // 0 ≤ t} => ‖displacement q hq t‖)
      (𝓝 ⟨0,le_rfl⟩) (𝓝 0) := by
  have hz : displacement q hq ⟨0,le_rfl⟩ = 0 := by ext z; simp [displacement,evolution_zero]
  simpa only [hz,norm_zero] using ((displacement_continuous q hq).norm.continuousAt (x := ⟨0,le_rfl⟩)).tendsto

theorem kernel_distance_sq_bound (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (z : Circle) :
    (∫ w : Circle, ‖(w:ℂ)-(z:ℂ)‖^2 ∂kernel q t z) ≤
      2 * ‖displacement q hq ⟨t,ht⟩‖ := by
  rw [kernel_distance_sq q t hq ht]
  have hz := circle_distance_sq z z
  simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hz
  have he : 2 - 2 * ((starRingEnd ℂ (z:ℂ)) * evolution q t z).re =
      2 * ((starRingEnd ℂ (z:ℂ)) * ((z:ℂ)-evolution q t z)).re := by
    simp only [mul_sub,sub_re]
    linarith
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ‖(starRingEnd ℂ (z:ℂ)) * ((z:ℂ)-evolution q t z)‖ := Complex.re_le_norm _
    _ = ‖evolution q t z - (z:ℂ)‖ := by rw [norm_mul]; simp [norm_sub_rev]
    _ ≤ ‖displacement q hq ⟨t,ht⟩‖ := (displacement q hq ⟨t,ht⟩).norm_coe_le_norm z

theorem observable_quadratic_modulus (f : C(Circle,ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w z : Circle,
      ‖f w-f z‖ ≤ ε + C * ‖(w:ℂ)-(z:ℂ)‖^2 := by
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  refine ⟨2*‖f‖/δ^2, by positivity, ?_⟩
  intro w z
  by_cases hw : dist w z < δ
  · have hf := hd hw
    rw [dist_eq_norm] at hf
    exact hf.le.trans (le_add_of_nonneg_right (by positivity))
  · have hh : δ^2 ≤ ‖(w:ℂ)-(z:ℂ)‖^2 := by
      have hh : δ ≤ ‖(w:ℂ)-(z:ℂ)‖ := by
        have hh : δ ≤ dist (w:ℂ) (z:ℂ) := le_of_not_gt hw
        simpa only [dist_eq_norm] using hh
      nlinarith [norm_nonneg ((w:ℂ)-(z:ℂ))]
    have hbound : ‖f w-f z‖ ≤ 2*‖f‖ := by
      calc
        _ ≤ ‖f w‖+‖f z‖ := norm_sub_le _ _
        _ ≤ ‖f‖+‖f‖ := add_le_add (f.norm_coe_le_norm w) (f.norm_coe_le_norm z)
        _ = 2*‖f‖ := by ring
    have hc := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*‖f‖/δ^2 by positivity)
    have hcancel : (2*‖f‖/δ^2)*δ^2 = 2*‖f‖ := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hδ))
    rw [hcancel] at hc
    linarith

theorem operator_error_bound (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (f : C(Circle,ℂ)) (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hf : ∀ w z : Circle, ‖f w-f z‖ ≤ ε + C * ‖(w:ℂ)-(z:ℂ)‖^2) :
    ‖operator q t hq ht f-f‖ ≤ ε + C * (2 * ‖displacement q hq ⟨t,ht⟩‖) := by
  let := kernel_markov q t hq ht
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  have hi := (observable_integrable q t hq ht f z).sub (integrable_const (f z))
  have hd : Integrable (fun w : Circle => ‖(w:ℂ)-(z:ℂ)‖^2) (kernel q t z) :=
    (show Continuous (fun w : Circle => ‖(w:ℂ)-(z:ℂ)‖^2) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (operator q t hq ht f-f) z = ∫ w, (f w-f z) ∂kernel q t z := by
    rw [integral_sub (observable_integrable q t hq ht f z) (integrable_const (f z))]
    simp [operator_apply]
  rw [he]
  calc
    _ ≤ ∫ w, ‖f w-f z‖ ∂kernel q t z := norm_integral_le_integral_norm _
    _ ≤ ∫ w : Circle, ε + C * ‖(w:ℂ)-(z:ℂ)‖^2 ∂kernel q t z :=
      integral_mono hi.norm ((integrable_const ε).add (hd.const_mul C)) (fun w => hf w z)
    _ = ε + C * (∫ w : Circle, ‖(w:ℂ)-(z:ℂ)‖^2 ∂kernel q t z) := by
      rw [integral_add (integrable_const ε) (hd.const_mul C),integral_const_mul]
      simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (kernel_distance_sq_bound q t hq ht z) hC)

theorem operator_strong_continuity_zero (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) :
    Filter.Tendsto (fun t : {t : ℝ // 0 ≤ t} => operator q t hq t.property f)
      (𝓝 ⟨0,le_rfl⟩) (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C,hC,hf⟩ := observable_quadratic_modulus f (ε/2) (by positivity)
  have hl : Filter.Tendsto (fun t : {t : ℝ // 0 ≤ t} => C*(2*‖displacement q hq t‖))
      (𝓝 ⟨0,le_rfl⟩) (𝓝 0) := by
    simpa using ((displacement_norm_tendsto q hq).const_mul 2).const_mul C
  have hev := (Metric.tendsto_nhds.mp hl) (ε/2) (by positivity)
  filter_upwards [hev] with t ht
  rw [dist_eq_norm]
  have hb := operator_error_bound q t hq t.property f (ε/2) C (by positivity) hC hf
  have hh : C*(2*‖displacement q hq t‖) < ε/2 := by
    simpa [Real.dist_eq,abs_of_nonneg hC] using ht
  linarith

theorem operator_increment_bound (q t h : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (hh : 0 ≤ h)
    (f : C(Circle,ℂ)) :
    ‖operator q (t+h) hq (add_nonneg ht hh) f - operator q t hq ht f‖ ≤
      ‖operator q h hq hh f-f‖ := by
  rw [operator_add q t h hq ht hh]
  change ‖operator q t hq ht (operator q h hq hh f) - operator q t hq ht f‖ ≤ _
  rw [← map_sub]
  calc
    _ ≤ ‖operator q t hq ht‖ * ‖operator q h hq hh f-f‖ := (operator q t hq ht).le_opNorm _
    _ ≤ 1 * ‖operator q h hq hh f-f‖ := mul_le_mul_of_nonneg_right
      (operator_contraction q t hq ht) (norm_nonneg _)
    _ = _ := one_mul _

theorem operator_time_difference_bound (q s t : ℝ) (hq : |q| < 1) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : C(Circle,ℂ)) :
    ‖operator q s hq hs f - operator q t hq ht f‖ ≤
      ‖operator q |s-t| hq (abs_nonneg _) f-f‖ := by
  rcases le_total t s with h | h
  · have hh := operator_increment_bound q t (s-t) hq ht (sub_nonneg.mpr h) f
    simpa only [add_sub_cancel,abs_of_nonneg (sub_nonneg.mpr h)] using hh
  · have hh := operator_increment_bound q s (t-s) hq hs (sub_nonneg.mpr h) f
    have habs : |s-t| = t-s := abs_sub_comm s t |>.trans (abs_of_nonneg (sub_nonneg.mpr h))
    simpa only [add_sub_cancel,habs,norm_sub_rev] using hh

theorem operator_strong_continuity (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) :
    Continuous (fun t : {t : ℝ // 0 ≤ t} => operator q t hq t.property f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let delta : {t : ℝ // 0 ≤ t} → {t : ℝ // 0 ≤ t} := fun s => ⟨|s.val-t.val|,abs_nonneg _⟩
  have hd : Continuous delta := by continuity
  have hz : delta t = ⟨0,le_rfl⟩ := by ext; simp [delta]
  have hl := (operator_strong_continuity_zero q hq f).comp
    (show Filter.Tendsto delta (𝓝 t) (𝓝 ⟨0,le_rfl⟩) by simpa only [hz] using (hd.continuousAt (x := t)).tendsto)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev := Metric.tendsto_nhds.mp hl ε hε
  filter_upwards [hev] with s hs
  rw [dist_eq_norm] at hs ⊢
  exact (operator_time_difference_bound q s t hq s.property t.property f).trans_lt hs

end OperatorDerivativeRewrite.Foundation.CauchyPoissonConcentration
