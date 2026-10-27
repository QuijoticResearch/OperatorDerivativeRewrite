import Foundation.CauchyPoissonEntropy
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
/-! Actual residual transition kernel for the drifted circle Poisson flow.
The density is normalized only under the stated minorization and epsilon < 1.
This module proves a fixed-positive-time invariant Markov splitting; it asserts
neither a residual semigroup nor an entropy decay rate. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonResidualKernel
open CauchyPoissonFlow CauchyPoissonKernelComposition CauchyPoissonMarkovKernel CauchyPoissonEntropy

def residualWeight (q t ε : ℝ) (z : Circle) (θ : ℝ) : ℝ :=
  (poleWeight (evolution q t z) θ-ε*poleWeight q θ)/(1-ε)

theorem residualWeight_measurable (q t ε : ℝ) :
    Measurable (fun p : Circle × ℝ => ENNReal.ofReal (residualWeight q t ε p.1 p.2)) := by
  unfold residualWeight poleWeight evolution flow numerator denominator poissonKernel
  fun_prop

theorem residualWeight_nonneg (q t ε : ℝ) (hε : ε < 1)
    (h : ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi), ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ)
    (z : Circle) (θ : ℝ) (hθ : θ ∈ Icc 0 (2*Real.pi)) : 0 ≤ residualWeight q t ε z θ :=
  div_nonneg (sub_nonneg.mpr (h z θ hθ)) (sub_pos.mpr hε).le

theorem residualWeight_integrable (q t ε : ℝ) (hq : |q| < 1) (ht : 0 < t) (z : Circle) :
    Integrable (residualWeight q t ε z) (volume.restrict (Ioc 0 (2*Real.pi))) :=
  ((poleWeight_integrable _ (evolution_strict_disk q t hq ht z (by simp))).sub
    ((poleWeight_integrable q (by simpa using hq)).const_mul ε)).div_const _

theorem residualWeight_mass (q t ε : ℝ) (hq : |q| < 1) (ht : 0 < t) (hε : ε < 1) (z : Circle) :
    (∫ θ in Ioc 0 (2*Real.pi), residualWeight q t ε z θ) = 1 := by
  unfold residualWeight
  rw [integral_div,integral_sub (poleWeight_integrable _ (evolution_strict_disk q t hq ht z (by simp)))
    ((poleWeight_integrable q (by simpa using hq)).const_mul ε),integral_const_mul,
    poleWeight_mass _ (evolution_strict_disk q t hq ht z (by simp)),poleWeight_mass q (by simpa using hq),mul_one]
  exact div_self (ne_of_gt (sub_pos.mpr hε))

def residualAngle (q t ε : ℝ) : Kernel Circle ℝ :=
  (Kernel.const Circle (volume.restrict (Ioc 0 (2*Real.pi)))).withDensity
    (fun z θ => ENNReal.ofReal (residualWeight q t ε z θ))

theorem residualAngle_apply (q t ε : ℝ) (z : Circle) :
    residualAngle q t ε z = (volume.restrict (Ioc 0 (2*Real.pi))).withDensity
      (fun θ => ENNReal.ofReal (residualWeight q t ε z θ)) := by
  rw [residualAngle,Kernel.withDensity_apply _ (residualWeight_measurable q t ε)]
  rfl

theorem residualAngle_markov (q t ε : ℝ) (hq : |q| < 1) (ht : 0 < t) (hε : ε < 1)
    (h : ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi), ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ) :
    IsMarkovKernel (residualAngle q t ε) := by
  constructor
  intro z
  constructor
  rw [residualAngle_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (residualWeight_integrable q t ε hq ht z)]
  · rw [residualWeight_mass q t ε hq ht hε z]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact residualWeight_nonneg q t ε hε h z θ ⟨hθ.1.le,hθ.2⟩

def residualKernel (q t ε : ℝ) : Kernel Circle Circle := (residualAngle q t ε).map Circle.exp

theorem residualKernel_markov (q t ε : ℝ) (hq : |q| < 1) (ht : 0 < t) (hε : ε < 1)
    (h : ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi), ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ) :
    IsMarkovKernel (residualKernel q t ε) := by
  let := residualAngle_markov q t ε hq ht hε h
  exact Kernel.IsMarkovKernel.map _ Circle.exp.continuous.measurable


theorem residual_density_split (q t ε : ℝ) (hq : |q| < 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (h : ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi), ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ)
    (z : Circle) (θ : ℝ) (hθ : θ ∈ Icc 0 (2*Real.pi)) :
    ENNReal.ofReal ε * ENNReal.ofReal (poleWeight q θ)+
      ENNReal.ofReal (1-ε)*ENNReal.ofReal (residualWeight q t ε z θ)=
      ENNReal.ofReal (poleWeight (evolution q t z) θ) := by
  rw [← ENNReal.ofReal_mul hε0,← ENNReal.ofReal_mul (sub_pos.mpr hε1).le,
    ← ENNReal.ofReal_add (mul_nonneg hε0 (poleWeight_positive q (by simpa using hq) θ).le)
      (mul_nonneg (sub_pos.mpr hε1).le (residualWeight_nonneg q t ε hε1 h z θ hθ))]
  congr 1
  unfold residualWeight
  field_simp [ne_of_gt (sub_pos.mpr hε1)]
  ring

theorem residualAngle_split (q t ε : ℝ) (hq : |q| < 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (h : ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi), ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ)
    (z : Circle) :
    ENNReal.ofReal ε • poleLaw q+ENNReal.ofReal (1-ε) • residualAngle q t ε z = poleLaw (evolution q t z) := by
  rw [residualAngle_apply]
  change ENNReal.ofReal ε • (volume.restrict (Ioc 0 (2*Real.pi))).withDensity (fun θ : ℝ => ENNReal.ofReal (poleWeight q θ)) + _ = _
  rw [← withDensity_smul' (ENNReal.ofReal ε) (fun θ : ℝ => ENNReal.ofReal (poleWeight q θ)) ENNReal.ofReal_ne_top,
    ← withDensity_smul' (ENNReal.ofReal (1-ε)) (fun θ : ℝ => ENNReal.ofReal (residualWeight q t ε z θ)) ENNReal.ofReal_ne_top]
  erw [← withDensity_add_left ((ENNReal.measurable_ofReal.comp (poleWeight_continuous q (by simpa using hq)).measurable).const_smul (ENNReal.ofReal ε))]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  exact residual_density_split q t ε hq hε0 hε1 h z θ ⟨hθ.1.le,hθ.2⟩

theorem residualKernel_split (q t ε : ℝ) (hq : |q| < 1) (ht : 0 < t) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (h : ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi), ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ)
    (z : Circle) :
    ENNReal.ofReal ε • invariantLaw q+ENNReal.ofReal (1-ε) • residualKernel q t ε z = kernel q t z := by
  have hh := congrArg (Measure.map Circle.exp) (residualAngle_split q t ε hq hε0 hε1 h z)
  rw [Measure.map_add _ _ Circle.exp.continuous.measurable,
    Measure.map_smul _ Circle.exp.continuous.measurable.aemeasurable,
    Measure.map_smul _ Circle.exp.continuous.measurable.aemeasurable] at hh
  simpa only [invariantLaw,residualKernel,Kernel.map_apply _ Circle.exp.continuous.measurable,
    kernel_positive_apply q t ht] using hh


theorem forward_split (q t ε : ℝ) (hq : |q| < 1) (ht : 0 < t) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (h : ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi), ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    ENNReal.ofReal ε • invariantLaw q+ENNReal.ofReal (1-ε) • ((residualKernel q t ε) ∘ₘ μ) =
      (kernel q t) ∘ₘ μ := by
  ext B hB
  have hi := lintegral_congr (μ := μ)
    (fun z => congrArg (fun ν : Measure Circle => ν B) (residualKernel_split q t ε hq ht hε0 hε1 h z))
  simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul] at hi
  rw [lintegral_add_left measurable_const,lintegral_const,
    lintegral_const_mul _ ((residualKernel q t ε).measurable_coe hB)] at hi
  simpa only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one,
    Measure.bind_apply hB (residualKernel q t ε).aemeasurable,
    Measure.bind_apply hB (kernel q t).aemeasurable] using hi


theorem residualKernel_invariant (q t ε : ℝ) (hq : |q| < 1) (ht : 0 < t) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (h : ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi), ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ) :
    (residualKernel q t ε) ∘ₘ invariantLaw q = invariantLaw q := by
  let := invariantLaw_probability q hq
  have hs := forward_split q t ε hq ht hε0 hε1 h (invariantLaw q)
  rw [invariant_comp q t hq ht.le] at hs
  have hc : ENNReal.ofReal ε + ENNReal.ofReal (1-ε) = 1 := by
    rw [← ENNReal.ofReal_add hε0 (sub_pos.mpr hε1).le]
    norm_num
  have he : ENNReal.ofReal ε • invariantLaw q + ENNReal.ofReal (1-ε) • invariantLaw q = invariantLaw q := by
    rw [← add_smul,hc,one_smul]
  let : IsFiniteMeasure (ENNReal.ofReal ε • invariantLaw q) := ⟨by simp⟩
  have heq := (Measure.add_right_inj (ENNReal.ofReal ε • invariantLaw q) _ _).mp (hs.trans he.symm)
  have hi := congrArg (fun ν : Measure Circle => (ENNReal.ofReal (1-ε))⁻¹ • ν) heq
  simpa only [smul_smul,ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hε1))) ENNReal.ofReal_ne_top,one_smul] using hi

theorem strict_density_minorization (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi),
      ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ := by
  obtain ⟨a,ha,h⟩ := density_minorization q t hq ht
  let ε := min a 1 / 2
  have hε : 0 < ε := div_pos (lt_min ha (by norm_num)) (by norm_num)
  have hεa : ε ≤ a := le_trans (half_le_self (le_of_lt (lt_min ha (by norm_num)))) (min_le_left _ _)
  have hε1 : ε < 1 := by dsimp [ε]; have := min_le_right a (1:ℝ); linarith
  refine ⟨ε,hε,hε1,fun z θ hθ => le_trans ?_ (h z θ hθ)⟩
  exact mul_le_mul_of_nonneg_right hεa (poleWeight_positive q (by simpa using hq) θ).le

theorem invariant_markov_splitting (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ IsMarkovKernel (residualKernel q t ε) ∧
      (∀ z : Circle, ENNReal.ofReal ε • invariantLaw q + ENNReal.ofReal (1-ε) • residualKernel q t ε z = kernel q t z) ∧
      (residualKernel q t ε) ∘ₘ invariantLaw q = invariantLaw q := by
  obtain ⟨ε,hε,hε1,h⟩ := strict_density_minorization q t hq ht
  exact ⟨ε,hε,hε1,residualKernel_markov q t ε hq ht hε1 h,
    residualKernel_split q t ε hq ht hε.le hε1 h,
    residualKernel_invariant q t ε hq ht hε.le hε1 h⟩

end OperatorDerivativeRewrite.Foundation.CauchyPoissonResidualKernel
