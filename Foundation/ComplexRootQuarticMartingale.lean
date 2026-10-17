import Foundation.ComplexRootPoissonPositiveMoments
import Foundation.ComplexRootPoissonDynkinMartingale

/-! A genuine unbounded holomorphic quartic martingale for the compound-root process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Preorder Finset
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootQuarticMartingale
open ComplexRootPoissonTrajectory ComplexRootPoissonKernel ComplexRootPoissonMarginals
open ComplexRootPoissonConditionalCalculus ComplexRootPoissonDynkinMartingale
open ComplexRootPoissonPolynomialDomain ComplexRootPoissonQuarticDrift

theorem kernel_quartic (a : ℝ) (r : ℝ≥0) (z : ℂ) :
    (∫ y : ℂ, y^4 ∂kernel a r z) = z^4-4*(r : ℂ)*(a : ℂ)^4 := by
  have hm : Measurable (fun y : ℂ => z+y) := by fun_prop
  have hpow : Continuous (fun y : ℂ => y^4) := by fun_prop
  rw [kernel_apply, integral_map hm.aemeasurable hpow.aestronglyMeasurable,
    shifted_quartic_integral]

theorem coordinate_quartic_integrable (a : ℝ) (δ : ℝ≥0) (n : ℕ) :
    Integrable (fun ω => (coordinate n ω)^4) (law a δ) := by
  have hi : Integrable (fun z : ℂ => z^4) ((law a δ).map (coordinate n)) := by
    rw [marginal_kernel, kernel_apply]
    simp only [zero_add]
    change Integrable (fun z : ℂ => z^4) ((ComplexRootPoissonLaw.law (n • δ) a).map id)
    rw [Measure.map_id]
    exact power_integrable (n • δ) a 4
  exact (integrable_map_measure (continuous_id.pow 4).aestronglyMeasurable
    (coordinate_measurable n).aemeasurable).mp hi

theorem conditional_quartic (a : ℝ) (δ : ℝ≥0) (n : ℕ) :
    (law a δ)[fun ω => (coordinate (n+1) ω)^4 | past n] =ᵐ[law a δ]
      fun ω => (coordinate n ω)^4-4*(δ : ℂ)*(a : ℂ)^4 := by
  have he := condExp_ae_eq_integral_condDistrib
    (μ := law a δ) (measurable_frestrictLe n)
    (coordinate_measurable (n+1)).aemeasurable
    (continuous_id.pow 4).stronglyMeasurable (coordinate_quartic_integrable a δ (n+1))
  have hk := ae_of_ae_map (measurable_frestrictLe n).aemeasurable (conditional_next a δ n)
  filter_upwards [he, hk] with ω he hk
  calc
    _ = ∫ y : ℂ, y^4 ∂condDistrib (coordinate (n+1)) (frestrictLe n) (law a δ)
        (frestrictLe n ω) := he
    _ = _ := by rw [hk, historyKernel_apply, kernel_quartic]; rfl

theorem quartic_adapted : StronglyAdapted filtration (fun n ω => (coordinate n ω)^4) := by
  intro n
  rw [filtration_eq_past]
  have hm : Measurable (fun h : History n => h ⟨n, by simp⟩) :=
    measurable_pi_apply (X := fun _ : ↥(Iic n) => ℂ) ⟨n, by simp⟩
  have hp : @Measurable Sample (History n) (past n) inferInstance (frestrictLe n) :=
    measurable_iff_comap_le.mpr le_rfl
  exact ((hm.comp hp).pow_const 4).stronglyMeasurable

def process (a : ℝ) (δ : ℝ≥0) (n : ℕ) (ω : Sample) : ℂ :=
  (coordinate n ω)^4+4*(n : ℂ)*(δ : ℂ)*(a : ℂ)^4

theorem process_integrable (a : ℝ) (δ : ℝ≥0) (n : ℕ) :
    Integrable (process a δ n) (law a δ) :=
  (coordinate_quartic_integrable a δ n).add (integrable_const _)

theorem process_adapted (a : ℝ) (δ : ℝ≥0) : StronglyAdapted filtration (process a δ) := by
  intro n
  exact (quartic_adapted n).add stronglyMeasurable_const

theorem process_martingale (a : ℝ) (δ : ℝ≥0) :
    Martingale (process a δ) filtration (law a δ) := by
  apply martingale_nat (process_adapted a δ) (fun n => process_integrable a δ n)
  intro n
  have he := condExp_add (coordinate_quartic_integrable a δ (n+1))
    (integrable_const (μ := law a δ) (4*((n+1 : ℕ) : ℂ)*(δ : ℂ)*(a : ℂ)^4))
    (filtration n)
  have hc := condExp_const (μ := law a δ) (filtration.le n)
    (4*((n+1 : ℕ) : ℂ)*(δ : ℂ)*(a : ℂ)^4)
  have hq := conditional_quartic a δ n
  rw [← filtration_eq_past] at hq
  apply Filter.EventuallyEq.symm
  filter_upwards [he, hq] with ω he hq
  change (law a δ)[fun ω => (coordinate (n+1) ω)^4+
    4*((n+1 : ℕ) : ℂ)*(δ : ℂ)*(a : ℂ)^4 | filtration n] ω = process a δ n ω
  calc
    _ = (law a δ)[fun ω => (coordinate (n+1) ω)^4 | filtration n] ω +
        (law a δ)[fun _ => 4*((n+1 : ℕ) : ℂ)*(δ : ℂ)*(a : ℂ)^4 | filtration n] ω := he
    _ = process a δ n ω := by rw [hc, hq]; simp only [process]; push_cast; ring

end OperatorDerivativeRewrite.Foundation.ComplexRootQuarticMartingale
