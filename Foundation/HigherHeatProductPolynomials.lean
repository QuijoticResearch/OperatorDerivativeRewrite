import Foundation.HigherHeatSignedPolynomialCalculus

/-! Actual unbounded polynomial products under finite independent signed heat increment laws. -/
noncomputable section
open MeasureTheory Polynomial Filter
open scoped NNReal Topology SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatProductPolynomials
open HigherHeatSignedLaws HigherHeatPolynomialRealization SignedAbsoluteIntegration

variable {ι : Type*} [Fintype ι]

def observable (P : ι → Polynomial ℝ) (x : ι → ℝ) : ℂ := ∏ i, (((P i).eval (x i) : ℝ) : ℂ)

theorem observable_measurable (P : ι → Polynomial ℝ) : Measurable (observable P) := by
  unfold observable
  fun_prop

theorem weighted_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (P : ι → Polynomial ℝ) : Integrable
      (fun x => incrementDensity m hm t ht x • observable P x)
      (Measure.pi (fun _ : ι => volume)) := by
  have hi (i : ι) : Integrable (fun x : ℝ =>
      ((realKernel m hm (t i) (ht i) x * (P i).eval x : ℝ) : ℂ)) := by
    have hh : Integrable (fun x : ℝ =>
        (((P i).eval x * realKernel m hm (t i) (ht i) x : ℝ) : ℂ)) :=
      (polynomial_integrable m hm (t i) (ht i) (P i)).ofReal
    simpa only [mul_comm] using hh
  have hh := Integrable.fintype_prod hi
  convert hh using 1
  funext x
  simp only [incrementDensity, observable, Complex.real_smul, Complex.ofReal_prod,
    Complex.ofReal_mul, Finset.prod_mul_distrib]

theorem product_absolute_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (P : ι → Polynomial ℝ) :
    Integrable (observable P)
      (absoluteDensity (Measure.pi (fun _ : ι => volume)) (incrementDensity m hm t ht)) := by
  have hd : Measurable (incrementDensity m hm t ht) := by
    unfold incrementDensity
    fun_prop
  apply (absolute_integrable_iff _ _ hd _).mpr
  apply (weighted_integrable m hm t ht P).norm.mono'
    (hd.norm.smul (observable_measurable P)).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖|incrementDensity m hm t ht x| • observable P x‖ ≤
      ‖incrementDensity m hm t ht x • observable P x‖
    simp only [norm_smul, Real.norm_eq_abs, abs_abs]
    exact le_rfl)

theorem product_signed_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (P : ι → Polynomial ℝ) :
    (incrementLaw m hm t ht).Integrable (observable P) :=
  (signed_integrable_iff _ _ (incrementDensity_integrable m hm t ht) _).mpr
    (product_absolute_integrable m hm t ht P)

theorem product_signed_integral (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (P : ι → Polynomial ℝ) :
    (∫ᵛ x, observable P x ∂<•incrementLaw m hm t ht) =
      ∏ i, (kernelExpectation m hm (t i) (ht i) (P i) : ℂ) := by
  have hd : Measurable (incrementDensity m hm t ht) := by
    unfold incrementDensity
    fun_prop
  rw [incrementLaw, integral_density _ _ (incrementDensity_integrable m hm t ht) hd _
    (product_absolute_integrable m hm t ht P)]
  calc
    _ = ∫ x : ι → ℝ, (∏ i, (((P i).eval (x i) * realKernel m hm (t i) (ht i) (x i) : ℝ) : ℂ))
        ∂Measure.pi (fun _ : ι => volume) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        simp only [incrementDensity, observable, Complex.real_smul, Complex.ofReal_prod,
          Complex.ofReal_mul, Finset.prod_mul_distrib]
        ring)
    _ = ∏ i, ∫ x : ℝ, (((P i).eval x * realKernel m hm (t i) (ht i) x : ℝ) : ℂ) :=
      integral_fintype_prod_eq_prod (μ := fun _ : ι => (volume : Measure ℝ))
        (fun i x => (((P i).eval x * realKernel m hm (t i) (ht i) x : ℝ) : ℂ))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact integral_complex_ofReal

end OperatorDerivativeRewrite.Foundation.HigherHeatProductPolynomials
