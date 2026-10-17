import Foundation.HigherHeatPowerVariation

/-! Exact centered quartic-variation signed second moments on arbitrary actual finite heat grids. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuarticVariation
open HigherHeatSignedLaws HigherHeatPowerVariation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)

theorem square_sum_integrable (p : ℕ) :
    (incrementLaw 2 (by norm_num) t ht).Integrable (fun x => (powerSum p x)^2) := by
  have he : (fun x : ι → ℝ => (powerSum p x)^2) =
      (fun x => ∑ i, ∑ j, (x i : ℂ)^p * (x j : ℂ)^p) := by
    funext x
    simp only [powerSum, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => pair_integrable t ht p p i j))

theorem quartic_sum_second_moment :
    (∫ᵛ x, (powerSum 4 x)^2 ∂<•incrementLaw 2 (by norm_num) t ht) =
      576*(∑ i, ((t i : ℝ) : ℂ))^2 + 19584*∑ i, ((t i : ℝ) : ℂ)^2 := by
  rw [square_sum_integral]
  have he (i j : ι) :
      (if i = j then moment (t i) (ht i) (4+4)
        else moment (t i) (ht i) 4 * moment (t j) (ht j) 4) =
      576*((t i : ℝ) : ℂ)*((t j : ℝ) : ℂ) +
        if i = j then 19584*((t i : ℝ) : ℂ)^2 else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true, show 4+4=8 from rfl, moment_eight]
      ring
    · simp only [if_neg hij, moment_four]
      ring
  simp_rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem centered_quartic_second_moment :
    (∫ᵛ x, (powerSum 4 x + 24*(∑ i, ((t i : ℝ) : ℂ)))^2
      ∂<•incrementLaw 2 (by norm_num) t ht) = 19584*∑ i, ((t i : ℝ) : ℂ)^2 := by
  let C : ℝ := ∑ i, (t i : ℝ)
  let ν := incrementLaw 2 (by norm_num) t ht
  letI : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have hS : ν.Integrable (fun x => (powerSum 4 x)^2) := square_sum_integrable t ht 4
  have hL : ν.Integrable (fun x => (48*C : ℝ) • powerSum 4 x) :=
    (sum_integrable t ht 4).smul (48*C : ℝ)
  have hC : ν.Integrable (fun _ => ((576*C^2 : ℝ) : ℂ)) :=
    SignedDensityIntegral.bounded_signed_integrable ν _ measurable_const _ (fun _ => le_rfl)
  have he : (fun x : ι → ℝ => (powerSum 4 x + 24*(∑ i, ((t i : ℝ) : ℂ)))^2) =
      (fun x => (powerSum 4 x)^2 + (48*C : ℝ) • powerSum 4 x + ((576*C^2 : ℝ) : ℂ)) := by
    funext x
    simp only [C, Complex.ofReal_sum, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
    ring
  rw [he, VectorMeasure.integral_fun_add (hS.fun_add hL) hC,
    VectorMeasure.integral_fun_add hS hL, VectorMeasure.integral_fun_smul,
    VectorMeasure.integral_const, incrementLaw_mass,
    quartic_sum_second_moment, quartic_sum_mean]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, one_smul,
    Complex.real_smul, C, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

end OperatorDerivativeRewrite.Foundation.HigherHeatQuarticVariation
