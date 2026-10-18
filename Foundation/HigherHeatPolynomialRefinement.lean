import Foundation.PureOrderPolynomialConditioning
import Foundation.HigherHeatBlockCoarsening
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Funext

/-! Actual unbounded polynomial expectations commute with finite increment coarsening. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialRefinement
open HigherHeatSignedLaws HigherHeatMultivariateMoments HigherHeatBlockCoarsening
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

open Classical in
def blockVariable (p : ι → κ) (i : κ) : MvPolynomial ι ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => p j = i), MvPolynomial.X j

def pullback (p : ι → κ) : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial ι ℝ :=
  MvPolynomial.aeval (blockVariable p)

open Classical in
def coarsen (p : ι → κ) (x : ι → ℝ) (i : κ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => p j = i), x j

omit [Fintype κ] in
theorem coarsen_measurable (p : ι → κ) : Measurable (coarsen p) := by
  classical
  unfold coarsen
  fun_prop

omit [Fintype κ] in
theorem eval_pullback (p : ι → κ) (P : MvPolynomial κ ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (pullback p P) = MvPolynomial.eval (coarsen p x) P := by
  classical
  have he : (MvPolynomial.aeval x).comp (pullback p) = MvPolynomial.aeval (coarsen p x) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [pullback, blockVariable, coarsen]
  exact DFunLike.congr_fun he P

omit [Fintype κ] in
theorem value_pullback (p : ι → κ) (P : MvPolynomial κ ℝ) (x : ι → ℝ) :
    value (pullback p P) x = value P (coarsen p x) := by
  simp only [value, eval_pullback]

theorem pullback_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ j, 0 < t j) (p : ι → κ) (P : MvPolynomial κ ℝ) :
    (incrementLaw m hm t ht).Integrable ((value P) ∘ coarsen p) := by
  have he : value (pullback p P) = (value P) ∘ coarsen p := funext (value_pullback p P)
  rw [← he]
  exact polynomial_integrable m hm t ht _

theorem actual_mean_pullback (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ j, 0 < t j) (p : ι → κ) (hp : Function.Surjective p)
    (P : MvPolynomial κ ℝ) :
    mean m hm t ht (pullback p P) =
      mean m hm (blockTimes p t) (blockTimes_pos p hp t ht) P := by
  have hf : Continuous (value P) := by
    exact Complex.continuous_ofReal.comp (MvPolynomial.continuous_eval P)
  have he : (∫ᵛ y, value P y ∂<•(incrementLaw m hm t ht).map (coarsen p)) =
      (∫ᵛ x, value P (coarsen p x) ∂<•incrementLaw m hm t ht) :=
    VectorMeasure.integral_map (coarsen_measurable p) hf.aestronglyMeasurable
      (pullback_integrable m hm t ht p P)
  have hlaw : (incrementLaw m hm t ht).map (coarsen p) =
      incrementLaw m hm (blockTimes p t) (blockTimes_pos p hp t ht) :=
    block_sum_law m hm p hp t ht
  rw [hlaw] at he
  change (∫ᵛ x, value (pullback p P) x ∂<•incrementLaw m hm t ht) = _
  simp_rw [value_pullback]
  exact he.symm


open Classical in
def sectionLift (p : ι → κ) (r : κ → ι) (y : κ → ℝ) (j : ι) : ℝ :=
  if j = r (p j) then y (p j) else 0

omit [Fintype κ] in
theorem coarsen_section (p : ι → κ) (r : κ → ι) (hr : Function.RightInverse r p)
    (y : κ → ℝ) : coarsen p (sectionLift p r y) = y := by
  classical
  funext k
  calc
    _ = ∑ j ∈ Finset.univ.filter (fun j => p j = k),
        if j = r k then y k else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hpj : p j = k := (Finset.mem_filter.mp hj).2
      simp only [sectionLift, hpj]
    _ = y k := by simp [hr k]

theorem coarsen_surjective (p : ι → κ) (hp : Function.Surjective p) :
    Function.Surjective (coarsen p) := by
  obtain ⟨r, hr⟩ := hp.hasRightInverse
  intro y
  exact ⟨sectionLift p r y, coarsen_section p r hr y⟩

theorem pullback_injective (p : ι → κ) (hp : Function.Surjective p) :
    Function.Injective (pullback p) := by
  intro P Q hPQ
  apply MvPolynomial.funext
  intro y
  obtain ⟨x, hx⟩ := coarsen_surjective p hp y
  have he := congrArg (fun R : MvPolynomial ι ℝ => MvPolynomial.eval x R) hPQ
  simpa only [eval_pullback, hx] using he


end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialRefinement
