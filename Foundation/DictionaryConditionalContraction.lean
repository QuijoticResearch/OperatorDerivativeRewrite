import Foundation.GaussianMehler
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! A retained coordinate is fixed by Gaussian conditioning. Integrating out an
independent coordinate supplies no positive-time damping of its derivative. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.DictionaryConditionalContraction
set_option backward.isDefEq.respectTransparency false

abbrev γ : Measure ℝ := GaussianCore.γ
abbrev μ : Measure (ℝ × ℝ) := γ.prod γ

abbrev observed : MeasurableSpace (ℝ × ℝ) :=
  MeasurableSpace.comap Prod.fst inferInstance

theorem observed_le : observed ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
  measurable_fst.comap_le

def reference (F : ℝ × ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, F (x,y) ∂γ

theorem reference_retained (f : ℝ → ℝ) :
    reference (fun z => f z.1) = f := by
  funext x
  simp [reference]

theorem retained_condexp {f : ℝ → ℝ} (hf : Measurable f) (hi : Integrable f γ) :
    μ[(fun z => f z.1) | observed] = fun z => f z.1 := by
  have hm : @Measurable (ℝ × ℝ) ℝ observed inferInstance Prod.fst :=
    Measurable.of_comap_le le_rfl
  exact condExp_of_stronglyMeasurable observed_le
    (hf.comp hm).stronglyMeasurable (hi.comp_fst γ)

theorem coordinate_integrable : Integrable (fun z : ℝ × ℝ => z.1) μ := by
  exact ((memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by norm_num)).integrable
    (by norm_num)).comp_fst γ

theorem coordinate_condexp : μ[Prod.fst | observed] = Prod.fst := by
  apply retained_condexp measurable_id
  exact (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by norm_num)).integrable
    (by norm_num)

theorem coordinate_centered : (∫ z : ℝ × ℝ, z.1 ∂μ) = 0 := by
  change (∫ z : ℝ × ℝ, z.1 ∂γ.prod γ) = 0
  rw [integral_prod _ coordinate_integrable]
  simp [γ, GaussianCore.γ, integral_id_gaussianReal]

def lowGradientNorm (f : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ x, (deriv f x)^2 ∂γ)

def fullGradientNorm (F : ℝ × ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ z, (deriv (fun x => F (x,z.2)) z.1)^2 +
    (deriv (fun y => F (z.1,y)) z.2)^2 ∂μ)

theorem retained_derivative (f : ℝ → ℝ) (x : ℝ) :
    deriv (reference (fun z => f z.1)) x = deriv f x := by
  rw [reference_retained]

/-- The factor one is attained on the whole retained Sobolev subspace. -/
theorem retained_gradient_equality (f : ℝ → ℝ)
    (hi : Integrable (fun x => (deriv f x)^2) γ) :
    lowGradientNorm (reference (fun z => f z.1)) =
      fullGradientNorm (fun z => f z.1) := by
  rw [reference_retained]
  unfold lowGradientNorm fullGradientNorm
  simp only [deriv_const, zero_pow (by norm_num : 2 ≠ 0), add_zero]
  rw [integral_prod _ (hi.comp_fst γ)]
  simp

theorem coordinate_lowGradientNorm : lowGradientNorm (reference Prod.fst) = 1 := by
  have h : reference Prod.fst = id := reference_retained id
  rw [h]
  simp [lowGradientNorm]

theorem coordinate_fullGradientNorm : fullGradientNorm Prod.fst = 1 := by
  simp [fullGradientNorm]

/-- A centered, smooth, integrable observable defeats every claimed strict factor. -/
theorem no_strict_reference_contraction (q : ℝ) (hq : q < 1) :
    ¬ lowGradientNorm (reference Prod.fst) ≤ q * fullGradientNorm Prod.fst := by
  rw [coordinate_lowGradientNorm, coordinate_fullGradientNorm, mul_one]
  exact not_le.mpr hq

theorem no_positive_time_reference_contraction (ν K t : ℝ)
    (hν : 0 < ν) (hK : K ≠ 0) (ht : 0 < t) :
    ¬ lowGradientNorm (reference Prod.fst) ≤
      Real.exp (-ν*K^2*t) * fullGradientNorm Prod.fst := by
  apply no_strict_reference_contraction
  apply Real.exp_lt_one_iff.mpr
  have hp : 0 < ν*K^2*t := mul_pos (mul_pos hν (sq_pos_of_ne_zero hK)) ht
  nlinarith

/-- Genuine Mehler evolution, unlike conditioning, damps the retained coordinate. -/
theorem mehler_coordinate (t : ℝ) :
    GaussianMehler.mehler t id = fun x => Real.exp (-t)*x := by
  funext x
  unfold GaussianMehler.mehler
  have hi : Integrable (fun y : ℝ => y) γ :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by norm_num)).integrable (by norm_num)
  change (∫ y, Real.exp (-t)*x + Real.sqrt (1-Real.exp (-2*t))*y ∂γ) =
    Real.exp (-t)*x
  rw [integral_add (integrable_const _) (hi.const_mul _)]
  rw [integral_const_mul (Real.sqrt (1-Real.exp (-2*t))) (fun y : ℝ => y)]
  simp [γ, GaussianCore.γ, integral_id_gaussianReal]

theorem mehler_coordinate_gradient (t : ℝ) :
    lowGradientNorm (GaussianMehler.mehler t id) = Real.exp (-t) := by
  rw [mehler_coordinate]
  simp [lowGradientNorm, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos (-t))]

theorem mehler_coordinate_strict (t : ℝ) (ht : 0 < t) :
    lowGradientNorm (GaussianMehler.mehler t id) < lowGradientNorm id := by
  rw [mehler_coordinate_gradient]
  have h : lowGradientNorm id = 1 := by simp [lowGradientNorm]
  rw [h]
  exact Real.exp_lt_one_iff.mpr (by linarith)

end OperatorDerivativeRewrite.Foundation.DictionaryConditionalContraction
