import Foundation.GaussianCore
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Local Gaussian Sobolev bridge

A positive Gaussian density has a positive lower bound on every compact interval.
This transfers Gaussian `L²` control to local Lebesgue `L²`. Consequently an
everywhere genuine derivative with integrable square under the Gaussian measure
is interval integrable, and the ordinary fundamental theorem of calculus applies.
No Sobolev graph approximation or entropy inequality is assumed here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianLocalSobolev

abbrev γ : Measure ℝ := GaussianCore.γ

private theorem pdf_continuous : Continuous (gaussianPDFReal 0 1) := by
  unfold gaussianPDFReal
  fun_prop

/-- A positive lower bound exists even when `Icc a b` is empty. -/
private theorem pdf_lower (a b : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc a b, c ≤ gaussianPDFReal 0 1 x := by
  obtain ⟨c, hc, hbound⟩ := isCompact_Icc.exists_forall_le' pdf_continuous.continuousOn
    (fun x hx => gaussianPDFReal_pos 0 1 x (by norm_num))
  exact ⟨c, hc, hbound⟩

private theorem gaussian_eq_density :
    γ = volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) := by
  rw [γ, GaussianCore.γ, gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rfl

/-- Quantitative domination of Lebesgue measure on a compact interval by γ.
The statement also covers `b < a`, when the restricted measure is zero. -/
theorem exists_local_measure_comparison (a b : ℝ) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ∞ ∧
      (volume.restrict (Icc a b) : Measure ℝ) ≤ C • γ := by
  obtain ⟨c, hc, hpdf⟩ := pdf_lower a b
  let C : ℝ≥0∞ := ENNReal.ofReal (c⁻¹)
  have hCpos : 0 < C := by
    dsimp [C]
    exact ENNReal.ofReal_pos.mpr (inv_pos.mpr hc)
  have hC : C ≠ ∞ := by simp [C]
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      (1 : ℝ≥0∞) ≤ C * gaussianPDF 0 1 x := by
    have hmul : c⁻¹ * c ≤ c⁻¹ * gaussianPDFReal 0 1 x :=
      mul_le_mul_of_nonneg_left (hpdf x hx) (inv_nonneg.mpr hc.le)
    have hreal : (1 : ℝ) ≤ c⁻¹ * gaussianPDFReal 0 1 x := by
      calc (1 : ℝ) = c⁻¹ * c := by field_simp
        _ ≤ c⁻¹ * gaussianPDFReal 0 1 x := hmul
    rw [gaussianPDF_def]
    change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (c⁻¹) * ENNReal.ofReal (gaussianPDFReal 0 1 x)
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
    simpa using ENNReal.ofReal_le_ofReal hreal
  have hlocal : (volume.restrict (Icc a b) : Measure ℝ) ≤
      C • γ.restrict (Icc a b) := by
    calc
      (volume.restrict (Icc a b) : Measure ℝ) =
          (volume.restrict (Icc a b)).withDensity 1 := (withDensity_one).symm
      _ ≤ (volume.restrict (Icc a b)).withDensity
          (fun x => C * gaussianPDF 0 1 x) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact hpoint x hx
      _ = C • γ.restrict (Icc a b) := by
        change (volume.restrict (Icc a b)).withDensity (C • gaussianPDF 0 1) = _
        rw [withDensity_smul C (measurable_gaussianPDF 0 1)]
        rw [← restrict_withDensity measurableSet_Icc]
        rw [gaussian_eq_density]
        rfl
  refine ⟨C, hCpos, hC, hlocal.trans ?_⟩
  apply Measure.le_iff'.2
  simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
  intro s
  gcongr
  exact Measure.restrict_le_self

/-- Gaussian `L²` membership implies local Lebesgue `L²` membership. -/
theorem memLp_two_volume_restrict_Icc_of_memLp_gaussian (a b : ℝ) {h : ℝ → ℝ}
    (hh : MemLp h 2 γ) :
    MemLp h 2 (volume.restrict (Icc a b)) := by
  obtain ⟨C, _, hC, hcmp⟩ := exists_local_measure_comparison a b
  exact hh.of_measure_le_smul hC hcmp

/-- An everywhere supplied derivative is the actual Mathlib derivative. -/
theorem derivative_eq_deriv {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x) : h = deriv f :=
  funext fun x => (hd x).deriv.symm

/-- Gaussian square integrability of an actual derivative implies local
Lebesgue integrability, without a continuity hypothesis on the derivative. -/
theorem intervalIntegrable_derivative_of_gaussian_sq_integrable {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hi : Integrable (fun x => (h x) ^ 2) γ) (a b : ℝ) :
    IntervalIntegrable h volume a b := by
  have heq : h = deriv f := derivative_eq_deriv hd
  have hm : Measurable h := heq ▸ measurable_deriv f
  have hlp : MemLp h 2 γ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hi
  have hloc := memLp_two_volume_restrict_Icc_of_memLp_gaussian (min a b) (max a b) hlp
  have hint : IntegrableOn h (Icc (min a b) (max a b)) volume :=
    hloc.integrable (by norm_num)
  exact (intervalIntegrable_iff').2 (by simpa only [uIcc] using hint)

/-- The actual interval FTC under the original Gaussian square-integrability
and everywhere-derivative hypotheses. -/
theorem integral_derivative_eq_sub_of_gaussian_sq_integrable {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hi : Integrable (fun x => (h x) ^ 2) γ) (a b : ℝ) :
    (∫ x in a..b, h x) = f b - f a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (intervalIntegrable_derivative_of_gaussian_sq_integrable hd hi a b)

end OperatorDerivativeRewrite.Foundation.GaussianLocalSobolev
