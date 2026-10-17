import Foundation.SequentialIncrementIndependence
import Foundation.MarkedTwoTimeHolomorphicTransform

/-! Native independent increments and actual finite-dimensional increment laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedIndependentIncrements
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedConditionalPolynomial MarkedHolomorphicExponential
open MarkedTwoTimeHolomorphicTransform

theorem has_indep_increments (a : ℝ) : HasIndepIncrements (process a) probability :=
  SequentialIncrementIndependence.of_filtration probability (history a) (process a)
    (fun t => (process_adapted a t).measurable) (difference_independent_past a)

def incrementVector {n : ℕ} (a : ℝ) (t : Fin (n+1) → ℝ≥0) (ω : StateSample) : Fin n → ℂ :=
  fun j => increment a (t j.castSucc) (t j.succ) ω

theorem incrementVector_measurable {n : ℕ} (a : ℝ) (t : Fin (n+1) → ℝ≥0) :
    Measurable (incrementVector a t) :=
  measurable_pi_lambda fun j : Fin n => increment_measurable a (t j.castSucc) (t j.succ)

theorem incrementVector_law {n : ℕ} (a : ℝ) (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) :
    probability.map (incrementVector a t) =
      Measure.pi (fun j : Fin n => ComplexRootPoissonLaw.law (t j.succ-t j.castSucc) a) := by
  have hi : iIndepFun (fun j : Fin n => increment a (t j.castSucc) (t j.succ)) probability :=
    has_indep_increments a n t ht
  have he := hi.map_fun_eq_pi_map
    (fun j : Fin n => (increment_measurable a (t j.castSucc) (t j.succ)).aemeasurable)
  change probability.map (incrementVector a t) = _ at he
  rw [he]
  congr 1
  funext j
  exact increment_law a _ _ (ht (Fin.castSucc_le_succ j))

theorem increment_product_integrable {n : ℕ} (a : ℝ) (t : Fin (n+1) → ℝ≥0)
    (ht : Monotone t) (ξ : Fin n → ℝ) :
    Integrable (fun ω => ∏ j : Fin n, futurePhase a (ξ j) (t j.castSucc) (t j.succ) ω)
      probability := by
  have hi := Integrable.fintype_prod (fun j : Fin n =>
    ComplexRootPoissonTransform.exponential_integrable (t j.succ-t j.castSucc) a (ξ j))
  have hm : Measurable (fun z : Fin n → ℂ =>
      ∏ j, Complex.exp (Complex.I*(ξ j : ℂ)*z j)) := by fun_prop
  have hmap : Integrable (fun z : Fin n → ℂ =>
      ∏ j, Complex.exp (Complex.I*(ξ j : ℂ)*z j)) (probability.map (incrementVector a t)) := by
    rw [incrementVector_law a t ht]
    exact hi
  exact (integrable_map_measure hm.aestronglyMeasurable
    (incrementVector_measurable a t).aemeasurable).mp hmap

theorem increment_transform {n : ℕ} (a : ℝ) (t : Fin (n+1) → ℝ≥0) (ht : Monotone t)
    (ξ : Fin n → ℝ) :
    (∫ ω, ∏ j : Fin n, futurePhase a (ξ j) (t j.castSucc) (t j.succ) ω ∂probability) =
      ∏ j : Fin n, Complex.exp (((t j.succ-t j.castSucc : ℝ≥0) : ℂ)*symbol a (ξ j)) := by
  have hi : iIndepFun (fun j : Fin n => futurePhase a (ξ j) (t j.castSucc) (t j.succ))
      probability := by
    have hi₀ := (has_indep_increments a n t ht).comp
      (fun j => fun z : ℂ => Complex.exp (Complex.I*(ξ j : ℂ)*z)) (by intro j; fun_prop)
    convert hi₀ using 1
    funext j ω
    rfl
  rw [hi.integral_fun_prod_eq_prod_integral
    (fun j => (futurePhase_measurable a (ξ j) (t j.castSucc) (t j.succ)).aestronglyMeasurable)]
  congr 1
  funext j
  exact futurePhase_mean a (ξ j) _ _ (ht (Fin.castSucc_le_succ j))

end OperatorDerivativeRewrite.Foundation.MarkedIndependentIncrements
