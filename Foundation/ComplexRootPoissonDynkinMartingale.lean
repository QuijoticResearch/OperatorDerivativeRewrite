import Foundation.ComplexRootPoissonCompensation
import Mathlib.Probability.Martingale.Centering

/-! Native Dynkin martingales for the genuinely constructed complex jump skeleton. -/
noncomputable section
open MeasureTheory ProbabilityTheory Preorder Finset
open scoped NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonDynkinMartingale
open ComplexRootPoissonTrajectory ComplexRootPoissonSemigroup
open ComplexRootPoissonConditionalCalculus

abbrev filtration : Filtration ℕ (inferInstance : MeasurableSpace Sample) :=
  Filtration.piLE (X := fun _ : ℕ => ℂ)

theorem filtration_eq_past (n : ℕ) : filtration n = past n :=
  Filtration.piLE_eq_comap_frestrictLe n

theorem observable_past (f : ComplexRootTransitionOperator.Test) (n : ℕ) :
    StronglyMeasurable[past n] (fun ω => f (coordinate n ω)) := by
  have hm : Measurable (fun h : History n => h ⟨n, by simp⟩) :=
    measurable_pi_apply (X := fun _ : ↥(Iic n) => ℂ) ⟨n, by simp⟩
  have hp : @Measurable Sample (History n) (past n) inferInstance (frestrictLe n) :=
    measurable_iff_comap_le.mpr le_rfl
  exact (f.continuous.measurable.comp hm).comp hp |>.stronglyMeasurable

theorem observable_adapted (f : ComplexRootTransitionOperator.Test) :
    StronglyAdapted filtration (fun n ω => f (coordinate n ω)) := by
  intro n
  rw [filtration_eq_past]
  exact observable_past f n

def drift (a : ℝ) (δ : ℝ≥0) (f : ComplexRootTransitionOperator.Test)
    (n : ℕ) (ω : Sample) : ℂ :=
  transition a δ f (coordinate n ω) - f (coordinate n ω)

theorem conditional_increment (a : ℝ) (δ : ℝ≥0)
    (f : ComplexRootTransitionOperator.Test) (n : ℕ) :
    (law a δ)[(fun ω => f (coordinate (n+1) ω)) -
      (fun ω => f (coordinate n ω)) | filtration n] =ᵐ[law a δ] drift a δ f n := by
  have hs := condExp_sub (observable_integrable a δ (n+1) f)
    (observable_integrable a δ n f) (filtration n)
  have hp := condExp_of_stronglyMeasurable (μ := law a δ) (filtration.le n)
    (observable_adapted f n) (observable_integrable a δ n f)
  have ht := conditional_transition a δ n f
  rw [← filtration_eq_past] at ht
  filter_upwards [hs, ht] with ω hs ht
  calc
    _ = (law a δ)[fun ω => f (coordinate (n+1) ω) | filtration n] ω -
        (law a δ)[fun ω => f (coordinate n ω) | filtration n] ω := hs
    _ = drift a δ f n ω := by rw [hp, ht]; rfl

def dynkin (a : ℝ) (δ : ℝ≥0) (f : ComplexRootTransitionOperator.Test) : ℕ → Sample → ℂ :=
  martingalePart (fun n ω => f (coordinate n ω)) filtration (law a δ)

theorem dynkin_martingale (a : ℝ) (δ : ℝ≥0) (f : ComplexRootTransitionOperator.Test) :
    Martingale (dynkin a δ f) filtration (law a δ) :=
  martingale_martingalePart (observable_adapted f) (fun n => observable_integrable a δ n f)

theorem predictable_formula (a : ℝ) (δ : ℝ≥0)
    (f : ComplexRootTransitionOperator.Test) (n : ℕ) :
    predictablePart (fun n ω => f (coordinate n ω)) filtration (law a δ) n
      =ᵐ[law a δ] fun ω => ∑ i ∈ range n, drift a δ f i ω := by
  have he := eventuallyEq_sum (s := range n)
    (fun i _ => conditional_increment a δ f i)
  filter_upwards [he] with ω hω
  simpa only [predictablePart, Finset.sum_apply] using hω

theorem dynkin_formula (a : ℝ) (δ : ℝ≥0)
    (f : ComplexRootTransitionOperator.Test) (n : ℕ) :
    dynkin a δ f n =ᵐ[law a δ]
      fun ω => f (coordinate n ω) - ∑ i ∈ range n, drift a δ f i ω := by
  filter_upwards [predictable_formula a δ f n] with ω hω
  change f (coordinate n ω) - _ = _
  rw [hω]

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonDynkinMartingale
