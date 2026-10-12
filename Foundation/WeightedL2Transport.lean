import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Multiplication transport for a positive almost-everywhere weighted L² space

The weight is the square of a measurable real function. Multiplication by that
function is a unitary from the weighted space onto ordinary L². Neither the
function nor its reciprocal is required to be bounded.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation.WeightedL2Transport

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (σ : Ω → ℝ)

/-- The measure whose density with respect to `μ` is `σ²`. -/
def weightedMeasure : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (σ ω ^ 2))

theorem weightedMeasure_absolutelyContinuous : weightedMeasure μ σ ≪ μ :=
  withDensity_absolutelyContinuous μ _

theorem absolutelyContinuous_weightedMeasure (hσ : Measurable σ)
    (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0) : μ ≪ weightedMeasure μ σ := by
  apply withDensity_absolutelyContinuous' (hσ.pow_const 2).ennreal_ofReal.aemeasurable
  filter_upwards [hne] with ω hω
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hω))

theorem integrable_weighted_iff (hσ : Measurable σ) (f : Ω → ℝ) :
    Integrable f (weightedMeasure μ σ) ↔ Integrable (fun ω => σ ω ^ 2 * f ω) μ := by
  have hr : ∀ ω, (ENNReal.ofReal (σ ω ^ 2)).toReal = σ ω ^ 2 :=
    fun ω => ENNReal.toReal_ofReal (sq_nonneg (σ ω))
  have H := (integrable_withDensity_iff_integrable_smul'
      (hσ.pow_const 2).ennreal_ofReal (ae_of_all μ fun _ => ENNReal.ofReal_lt_top)
      (g := f))
  change Integrable f (weightedMeasure μ σ) ↔
    Integrable (fun ω => (ENNReal.ofReal (σ ω ^ 2)).toReal * f ω) μ at H
  simp_rw [hr] at H
  exact H

theorem integral_weighted (hσ : Measurable σ) (f : Ω → ℝ) :
    ∫ ω, f ω ∂weightedMeasure μ σ = ∫ ω, σ ω ^ 2 * f ω ∂μ := by
  have hr : ∀ ω, (ENNReal.ofReal (σ ω ^ 2)).toReal = σ ω ^ 2 :=
    fun ω => ENNReal.toReal_ofReal (sq_nonneg (σ ω))
  have H := (integral_withDensity_eq_integral_toReal_smul
      (hσ.pow_const 2).ennreal_ofReal (ae_of_all μ fun _ => ENNReal.ofReal_lt_top) f)
  change (∫ ω, f ω ∂weightedMeasure μ σ) =
    ∫ ω, (ENNReal.ofReal (σ ω ^ 2)).toReal * f ω ∂μ at H
  simp_rw [hr] at H
  exact H

/-- Multiplication genuinely maps weighted L² functions into ordinary L². -/
theorem memLp_mul (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    {u : Ω → ℝ} (hu : MemLp u 2 (weightedMeasure μ σ)) :
    MemLp (fun ω => σ ω * u ω) 2 μ := by
  have hum : AEStronglyMeasurable u μ :=
    hu.aestronglyMeasurable.mono_ac (absolutelyContinuous_weightedMeasure μ σ hσ hne)
  apply (memLp_two_iff_integrable_sq (hσ.aestronglyMeasurable.mul hum)).mpr
  simpa only [Pi.mul_apply, mul_pow] using
    (integrable_weighted_iff μ σ hσ (fun ω => u ω ^ 2)).mp hu.integrable_sq

/-- Division genuinely maps ordinary L² functions into weighted L². -/
theorem memLp_div (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    {v : Ω → ℝ} (hv : MemLp v 2 μ) :
    MemLp (fun ω => v ω / σ ω) 2 (weightedMeasure μ σ) := by
  have hvm := (hv.aestronglyMeasurable.div₀ hσ.aestronglyMeasurable).mono_ac
    (weightedMeasure_absolutelyContinuous μ σ)
  apply (memLp_two_iff_integrable_sq hvm).mpr
  apply (integrable_weighted_iff μ σ hσ _).mpr
  apply hv.integrable_sq.congr
  filter_upwards [hne] with ω hω
  simp only [Pi.div_apply]
  field_simp

/-- The actual L² class of the multiplied function. -/
def multiply (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (u : Lp ℝ 2 (weightedMeasure μ σ)) : Lp ℝ 2 μ :=
  (memLp_mul μ σ hσ hne (Lp.memLp u)).toLp (fun ω => σ ω * u ω)

theorem multiply_coeFn (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (u : Lp ℝ 2 (weightedMeasure μ σ)) :
    multiply μ σ hσ hne u =ᵐ[μ] fun ω => σ ω * u ω :=
  MemLp.coeFn_toLp _

theorem multiply_add (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (u v : Lp ℝ 2 (weightedMeasure μ σ)) :
    multiply μ σ hσ hne (u + v) = multiply μ σ hσ hne u + multiply μ σ hσ hne v := by
  apply Lp.ext
  filter_upwards [multiply_coeFn μ σ hσ hne (u + v),
    multiply_coeFn μ σ hσ hne u, multiply_coeFn μ σ hσ hne v,
    Lp.coeFn_add (multiply μ σ hσ hne u) (multiply μ σ hσ hne v),
    (absolutelyContinuous_weightedMeasure μ σ hσ hne).ae_eq (Lp.coeFn_add u v)]
    with ω huv hu hv hadd hsum
  simp only [Pi.add_apply] at hsum hadd
  rw [huv, hsum, hadd, hu, hv, mul_add]

theorem multiply_smul (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (r : ℝ) (u : Lp ℝ 2 (weightedMeasure μ σ)) :
    multiply μ σ hσ hne (r • u) = r • multiply μ σ hσ hne u := by
  apply Lp.ext
  filter_upwards [multiply_coeFn μ σ hσ hne (r • u),
    multiply_coeFn μ σ hσ hne u, Lp.coeFn_smul r (multiply μ σ hσ hne u),
    (absolutelyContinuous_weightedMeasure μ σ hσ hne).ae_eq (Lp.coeFn_smul r u)]
    with ω hru hu hsmul hscalar
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul hscalar
  rw [hru, hscalar, hsmul, hu]
  ring

private theorem norm_sq_integral (ν : Measure Ω) (u : Lp ℝ 2 ν) :
    ‖u‖ ^ 2 = ∫ ω, u ω ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [Real.inner_apply, pow_two]

theorem norm_multiply (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (u : Lp ℝ 2 (weightedMeasure μ σ)) : ‖multiply μ σ hσ hne u‖ = ‖u‖ := by
  have hs : ‖multiply μ σ hσ hne u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_integral, norm_sq_integral, integral_weighted μ σ hσ]
    apply integral_congr_ae
    filter_upwards [multiply_coeFn μ σ hσ hne u] with ω hω
    rw [hω, mul_pow]
  nlinarith [norm_nonneg (multiply μ σ hσ hne u), norm_nonneg u]

/-- The isometric linear multiplication map. -/
def multiplicationIsometry (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0) :
    Lp ℝ 2 (weightedMeasure μ σ) →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toFun := multiply μ σ hσ hne
  map_add' := multiply_add μ σ hσ hne
  map_smul' := multiply_smul μ σ hσ hne
  norm_map' := norm_multiply μ σ hσ hne

/-- The actual weighted L² class of division by the weight function. -/
def divide (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (v : Lp ℝ 2 μ) : Lp ℝ 2 (weightedMeasure μ σ) :=
  (memLp_div μ σ hσ hne (Lp.memLp v)).toLp (fun ω => v ω / σ ω)

theorem divide_coeFn (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (v : Lp ℝ 2 μ) :
    divide μ σ hσ hne v =ᵐ[weightedMeasure μ σ] fun ω => v ω / σ ω :=
  MemLp.coeFn_toLp _

theorem multiply_divide (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (v : Lp ℝ 2 μ) : multiply μ σ hσ hne (divide μ σ hσ hne v) = v := by
  apply Lp.ext
  filter_upwards [multiply_coeFn μ σ hσ hne (divide μ σ hσ hne v),
    (absolutelyContinuous_weightedMeasure μ σ hσ hne).ae_eq
      (divide_coeFn μ σ hσ hne v), hne] with ω hm hd hω
  rw [hm, hd]
  field_simp

theorem divide_multiply (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (u : Lp ℝ 2 (weightedMeasure μ σ)) :
    divide μ σ hσ hne (multiply μ σ hσ hne u) = u := by
  apply Lp.ext
  filter_upwards [divide_coeFn μ σ hσ hne (multiply μ σ hσ hne u),
    (weightedMeasure_absolutelyContinuous μ σ).ae_eq (multiply_coeFn μ σ hσ hne u),
    (weightedMeasure_absolutelyContinuous μ σ).ae_le hne] with ω hd hm hω
  rw [hd, hm]
  field_simp

theorem multiplicationIsometry_surjective (hσ : Measurable σ)
    (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0) :
    Function.Surjective (multiplicationIsometry μ σ hσ hne) :=
  fun v => ⟨divide μ σ hσ hne v, multiply_divide μ σ hσ hne v⟩

/-- Weighted multiplication is a unitary with no boundedness assumption. -/
def unitary (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0) :
    Lp ℝ 2 (weightedMeasure μ σ) ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (multiplicationIsometry μ σ hσ hne)
    (multiplicationIsometry_surjective μ σ hσ hne)

theorem unitary_coeFn (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (u : Lp ℝ 2 (weightedMeasure μ σ)) :
    unitary μ σ hσ hne u =ᵐ[μ] fun ω => σ ω * u ω :=
  multiply_coeFn μ σ hσ hne u

theorem unitary_symm_eq_divide (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (v : Lp ℝ 2 μ) : (unitary μ σ hσ hne).symm v = divide μ σ hσ hne v := by
  apply (unitary μ σ hσ hne).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (multiply_divide μ σ hσ hne v).symm

theorem unitary_symm_coeFn (hσ : Measurable σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)
    (v : Lp ℝ 2 μ) :
    (unitary μ σ hσ hne).symm v =ᵐ[weightedMeasure μ σ] fun ω => v ω / σ ω := by
  rw [unitary_symm_eq_divide]
  exact divide_coeFn μ σ hσ hne v

end OperatorDerivativeRewrite.Foundation.WeightedL2Transport
