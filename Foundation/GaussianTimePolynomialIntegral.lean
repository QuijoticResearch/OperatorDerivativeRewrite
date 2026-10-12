import Foundation.GaussianTimeDivergence
import Foundation.GaussianTimeStepIntegral
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The actual predictable polynomial integral agrees with the Gaussian divergence

The coefficients are evaluations of actual multivariate polynomials at finitely
many past process values. Their moments and past measurability are proved here.
The finite predictable integral is the previously constructed L² increment sum,
and its divergence identity uses the existing adjoint on its actual domain.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal NNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianTimePolynomialIntegral

open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence

variable {ι : Type*} [Fintype ι]

/-- Evaluation of a polynomial on finitely many coordinates of an entire past path. -/
def polynomialPastFunction {s : ℝ≥0} (r : ι → Set.Iic s) (p : MvPolynomial ι ℝ)
    (z : Set.Iic s → ℝ) : ℝ := MvPolynomial.eval (fun j => z (r j)) p

omit [Fintype ι] in
/-- Past-path measurability is derived from polynomial continuity and coordinate evaluation. -/
theorem polynomialPastFunction_measurable [Finite ι] {s : ℝ≥0} (r : ι → Set.Iic s)
    (p : MvPolynomial ι ℝ) : Measurable (polynomialPastFunction r p) := by
  let := Fintype.ofFinite ι
  exact (MvPolynomial.continuous_eval (p := p)).measurable.comp
    (Measurable.of_eval fun j => measurable_pi_apply (r j))

omit [Fintype ι] in
/-- The actual random coefficient is the polynomial in the constructed time process. -/
theorem polynomialPastFunction_coefficient {s : ℝ≥0} (r : ι → Set.Iic s)
    (p : MvPolynomial ι ℝ) :
    GaussianPredictableStep.pastCoefficient process s (polynomialPastFunction r p) =
      fun ω => MvPolynomial.eval (fun j => process (r j) ω) p := rfl

omit [Fintype ι] in
/-- Every finite moment is available; no square-integrability assumption is added. -/
theorem polynomialPastFunction_memLp {s : ℝ≥0} (r : ι → Set.Iic s)
    (p : MvPolynomial ι ℝ) (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (GaussianPredictableStep.pastCoefficient process s (polynomialPastFunction r p))
      q gaussianProduct :=
  pastPolynomial_memLp (fun j => r j) p q hq

/-- The actual predictable L² integral specialized to polynomial past coefficients. -/
def polynomialPartitionIntegralL2 {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (r : (i : Fin n) → ι → Set.Iic (τ i.castSucc)) (p : Fin n → MvPolynomial ι ℝ) :
    GaussianL2 :=
  partitionIntegralL2 τ hτ (fun i => polynomialPastFunction (r i) (p i))
    (fun i => polynomialPastFunction_measurable (r i) (p i))
    (fun i => polynomialPastFunction_memLp (r i) (p i) 2 (by simp))

/-- Equality with the genuine finite sum of coefficient/increment L² products. -/
theorem polynomialPartitionIntegralL2_eq_sum {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (r : (i : Fin n) → ι → Set.Iic (τ i.castSucc)) (p : Fin n → MvPolynomial ι ℝ) :
    polynomialPartitionIntegralL2 τ hτ r p =
      ∑ i, incrementProductL2 (fun j => r i j) (p i) (τ i.castSucc) (τ i.succ) := by
  apply Lp.ext
  have hI := partitionIntegralL2_coeFn τ hτ
    (fun i => polynomialPastFunction (r i) (p i))
    (fun i => polynomialPastFunction_measurable (r i) (p i))
    (fun i => polynomialPastFunction_memLp (r i) (p i) 2 (by simp))
  have hc (i : Fin n) :=
    incrementProductL2_coeFn (fun j => (r i j).val) (p i) (τ i.castSucc) (τ i.succ)
  filter_upwards [hI,
    Lp.coeFn_finsetSum Finset.univ (fun i =>
      incrementProductL2 (fun j => r i j) (p i) (τ i.castSucc) (τ i.succ)),
    Filter.eventually_all.2 hc] with ω hωI hωS hωc
  rw [show polynomialPartitionIntegralL2 τ hτ r p ω =
    GaussianPredictableStep.partitionIntegral process τ
      (fun i => polynomialPastFunction (r i) (p i)) ω from hωI, hωS]
  simp only [GaussianPredictableStep.partitionIntegral, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (hωc i).symm

/-- The actual coefficient-space valued random field associated to the time steps. -/
def polynomialPartitionField {n : ℕ} (τ : Fin (n + 1) → ℝ≥0)
    (r : (i : Fin n) → ι → Set.Iic (τ i.castSucc)) (p : Fin n → MvPolynomial ι ℝ) :
    Lp CoefficientSpace 2 gaussianProduct :=
  ∑ i, scalarTensor (incrementDirection (τ i.castSucc) (τ i.succ))
    (GaussianTimeDivergence.pastCoefficient (fun j => r i j) (p i))

/-- Domain and value agreement with the existing cylindrical divergence. -/
theorem polynomialPartitionIntegralL2_cylindricalDivergence_graph {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (r : (i : Fin n) → ι → Set.Iic (τ i.castSucc)) (p : Fin n → MvPolynomial ι ℝ) :
    (polynomialPartitionField τ r p, polynomialPartitionIntegralL2 τ hτ r p)
      ∈ cylindricalDivergence.graph := by
  rw [polynomialPartitionIntegralL2_eq_sum]
  exact pastCoefficient_sum_cylindricalDivergence_graph (fun i j => r i j) p
    (fun i => τ i.castSucc) (fun i => τ i.succ)
    (fun i j => (r i j).property) (fun i => hτ (Fin.castSucc_le_succ i))

/-- Exact agreement with the full Hilbert adjoint divergence on these polynomial predictable fields.
No graph-core density assertion is made. -/
theorem polynomialPartitionIntegralL2_hilbertDivergence_graph {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (r : (i : Fin n) → ι → Set.Iic (τ i.castSucc)) (p : Fin n → MvPolynomial ι ℝ) :
    (polynomialPartitionField τ r p, polynomialPartitionIntegralL2 τ hτ r p)
      ∈ hilbertDivergence.graph :=
  LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (polynomialPartitionIntegralL2_cylindricalDivergence_graph τ hτ r p)

/-- The same genuine divergence value obeys the elapsed-time weighted Itô isometry. -/
theorem polynomialPartitionIntegralL2_norm_sq {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (r : (i : Fin n) → ι → Set.Iic (τ i.castSucc)) (p : Fin n → MvPolynomial ι ℝ) :
    ‖polynomialPartitionIntegralL2 τ hτ r p‖ ^ 2 =
      ∑ i, ((τ i.succ : ℝ) - τ i.castSucc) *
        ∫ ω, (MvPolynomial.eval (fun j => process (r i j) ω) (p i)) ^ 2
          ∂gaussianProduct :=
  partitionIntegralL2_norm_sq τ hτ (fun i => polynomialPastFunction (r i) (p i))
    (fun i => polynomialPastFunction_measurable (r i) (p i))
    (fun i => polynomialPastFunction_memLp (r i) (p i) 2 (by simp))

end OperatorDerivativeRewrite.Foundation.GaussianTimePolynomialIntegral
