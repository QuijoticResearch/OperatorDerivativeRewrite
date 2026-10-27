import Foundation.CauchyPoissonDualAverage
/-! Explicit continuous strictly positive densities of actual positive-time
forward laws relative to the invariant circle law. Measure equality, the
Radon--Nikodym representative and integral pairings are identified. No time
derivative, strong density-generator domain or entropy-production rate is asserted. -/
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonForwardDensity
open CauchyPoissonFlow CauchyPoissonKernelComposition CauchyPoissonMarkovKernel CauchyPoissonFeller

def circleWeight (v : ℂ) (w : Circle) : ℝ := (2*Real.pi)⁻¹ * poissonKernel 0 v w

theorem circleWeight_positive (v : ℂ) (hv : ‖v‖ < 1) (w : Circle) :
    0 < circleWeight v w :=
  mul_pos (by positivity) (poisson_positive v w hv (by simp))

theorem circleWeight_angle (v : ℂ) (θ : ℝ) : circleWeight v (Circle.exp θ) = poleWeight v θ := by
  unfold circleWeight poleWeight
  congr 2
  simp [circleMap]

def ratio (q t : ℝ) (z w : Circle) : ℝ :=
  circleWeight (evolution q t z) w / circleWeight q w

theorem ratio_positive (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) (z w : Circle) :
    0 < ratio q t z w :=
  div_pos (circleWeight_positive _ (evolution_strict_disk q t hq ht z (by simp)) w)
    (circleWeight_positive q (by simpa using hq) w)

theorem joint_circleWeight_continuous (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    Continuous (fun p : Circle × Circle => circleWeight (evolution q t p.1) p.2) := by
  have he : Continuous (fun p : Circle × Circle => evolution q t p.1) :=
    (evolution_circle_continuous q t hq ht.le).comp continuous_fst
  unfold circleWeight poissonKernel
  apply Continuous.const_mul
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  apply pow_ne_zero 2
  apply norm_ne_zero_iff.mpr
  simp only [sub_zero]
  intro hh
  have hn := congrArg norm (sub_eq_zero.mp hh)
  simp only [Circle.norm_coe] at hn
  exact (ne_of_lt (evolution_strict_disk q t hq ht p.1 (by simp))) hn.symm

theorem circleWeight_continuous (v : ℂ) (hv : ‖v‖ < 1) : Continuous (circleWeight v) := by
  unfold circleWeight poissonKernel
  apply Continuous.const_mul
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro w
  apply pow_ne_zero 2
  apply norm_ne_zero_iff.mpr
  simp only [sub_zero]
  intro hh
  have hn := congrArg norm (sub_eq_zero.mp hh)
  simp only [Circle.norm_coe] at hn
  exact (ne_of_lt hv) hn.symm

theorem ratio_continuous (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    Continuous (fun p : Circle × Circle => ratio q t p.1 p.2) :=
  (joint_circleWeight_continuous q t hq ht).div
    ((circleWeight_continuous q (by simpa using hq)).comp continuous_snd)
    (fun p => ne_of_gt (circleWeight_positive q (by simpa using hq) p.2))

theorem ratio_weight (q t : ℝ) (hq : |q| < 1) (z : Circle) (θ : ℝ) :
    ratio q t z (Circle.exp θ) * poleWeight q θ = poleWeight (evolution q t z) θ := by
  unfold ratio
  rw [circleWeight_angle,circleWeight_angle]
  exact div_mul_cancel₀ _ (ne_of_gt (poleWeight_positive q (by simpa using hq) θ))


theorem kernel_density (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) (z : Circle) :
    (invariantLaw q).withDensity (fun w => ENNReal.ofReal (ratio q t z w)) = kernel q t z := by
  have hr : Measurable (fun w => ENNReal.ofReal (ratio q t z w)) :=
    ENNReal.measurable_ofReal.comp (((ratio_continuous q t hq ht).comp
      (continuous_const.prodMk continuous_id)).measurable)
  ext B hB
  rw [withDensity_apply _ hB,← lintegral_indicator hB]
  rw [invariantLaw,lintegral_map (hr.indicator hB) Circle.exp.continuous.measurable]
  have hd := lintegral_withDensity_eq_lintegral_mul (volume.restrict (Ioc 0 (2*Real.pi)))
    (ENNReal.measurable_ofReal.comp (poleWeight_continuous q (by simpa using hq)).measurable)
    ((hr.indicator hB).comp Circle.exp.continuous.measurable)
  simp only [Function.comp_def] at hd
  rw [poleLaw,hd]
  rw [kernel_positive_apply q t ht z,Measure.map_apply Circle.exp.continuous.measurable hB,
    poleLaw,withDensity_apply _ (Circle.exp.continuous.measurable hB),
    ← lintegral_indicator (Circle.exp.continuous.measurable hB)]
  apply lintegral_congr
  intro θ
  by_cases hθ : Circle.exp θ ∈ B
  · simp only [Pi.mul_apply,indicator_of_mem hθ,indicator_of_mem (show θ ∈ Circle.exp ⁻¹' B from hθ)]
    rw [← ENNReal.ofReal_mul (poleWeight_positive q (by simpa using hq) θ).le,mul_comm,
      ratio_weight q t hq z θ]
  · simp [hθ]


def density (q t : ℝ) (μ : Measure Circle) (w : Circle) : ℝ := ∫ z, ratio q t z w ∂μ

theorem ratio_integrable (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (w : Circle) :
    Integrable (fun z => ratio q t z w) μ :=
  ((ratio_continuous q t hq ht).comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem density_continuous (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] : Continuous (density q t μ) := by
  have hc : Continuous (Function.uncurry (fun w z : Circle => ratio q t z w)) :=
    Continuous.comp (g := fun p : Circle × Circle => ratio q t p.1 p.2)
      (f := fun p : Circle × Circle => (p.2,p.1))
      (ratio_continuous q t hq ht) (continuous_snd.prodMk continuous_fst)
  have h := continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ
  change Continuous (fun w => ∫ z, ratio q t z w ∂μ)
  simpa only [Measure.restrict_univ] using h

theorem density_positive (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (w : Circle) : 0 < density q t μ w := by
  apply (integral_pos_iff_support_of_nonneg (fun z => (ratio_positive q t hq ht z w).le)
    (ratio_integrable q t hq ht μ w)).mpr
  have he : Function.support (fun z => ratio q t z w) = univ := by
    ext z
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (ratio_positive q t hq ht z w)
  rw [he]
  simp


theorem forward_density (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (invariantLaw q).withDensity (fun w => ENNReal.ofReal (density q t μ w)) =
      (kernel q t) ∘ₘ μ := by
  let := invariantLaw_probability q hq
  ext B hB
  rw [withDensity_apply _ hB,Measure.bind_apply hB (kernel q t).aemeasurable]
  calc
    _ = ∫⁻ w in B, ∫⁻ z, ENNReal.ofReal (ratio q t z w) ∂μ ∂invariantLaw q := by
      apply lintegral_congr
      intro w
      exact ofReal_integral_eq_lintegral_ofReal (ratio_integrable q t hq ht μ w)
        (Eventually.of_forall (fun z => (ratio_positive q t hq ht z w).le))
    _ = ∫⁻ z, ∫⁻ w in B, ENNReal.ofReal (ratio q t z w) ∂invariantLaw q ∂μ := by
      apply lintegral_lintegral_swap
      exact (ENNReal.measurable_ofReal.comp
        ((ratio_continuous q t hq ht).comp continuous_swap).measurable).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [← withDensity_apply _ hB,kernel_density q t hq ht z]


theorem density_rnDeriv (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    ((kernel q t) ∘ₘ μ).rnDeriv (invariantLaw q) =ᵐ[invariantLaw q]
      fun w => ENNReal.ofReal (density q t μ w) := by
  let := invariantLaw_probability q hq
  rw [← forward_density q t hq ht μ]
  exact Measure.rnDeriv_withDensity _
    (ENNReal.measurable_ofReal.comp (density_continuous q t hq ht μ).measurable)

theorem density_integral_pairing (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (f : Circle → ℂ) :
    (∫ w, f w ∂(kernel q t) ∘ₘ μ) =
      ∫ w, density q t μ w • f w ∂invariantLaw q := by
  have he := integral_withDensity_eq_integral_toReal_smul (μ := invariantLaw q)
    (ENNReal.measurable_ofReal.comp (density_continuous q t hq ht μ).measurable)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f
  simp only [Function.comp_def,ENNReal.toReal_ofReal (density_positive q t hq ht μ _).le] at he
  rw [← forward_density q t hq ht μ]
  exact he

end OperatorDerivativeRewrite.Foundation.CauchyPoissonForwardDensity
