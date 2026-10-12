import Foundation.GaussianTimeProcess
import Foundation.InfiniteGaussianOperators

/-!
# Past polynomial coefficients and genuine time-increment divergences

A coefficient polynomial in finitely many process values at times at most `s`
has zero derivative in the direction of `(s,t]`. Consequently its genuine
cylindrical and full Hilbert divergences equal coefficient times process
increment. All products are constructed in actual L², with their finite moments
proved before graph membership is asserted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal NNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianTimeDivergence

open InfiniteGaussian GaussianTimeHilbert GaussianHilbertProcess GaussianTimeProcess
open SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

variable {ι : Type*} [Fintype ι]

/-- The actual coefficient-space direction of a time interval. -/
def incrementDirection (s t : ℝ≥0) : CoefficientSpace :=
  hilbertEmbedding TimeHilbert (intervalVector s t)

/-- The actual polynomial scalar domain element represented by finitely many process values. -/
def pastCoefficient (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) : polynomialCylindricalDomain :=
  ⟨isonormalCylinderL2 (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) p,
    isonormalCylinderL2_mem_core _ _⟩

theorem pastCoefficient_coeFn (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) :
    (pastCoefficient r p : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => MvPolynomial.eval (fun i => process (r i) ω) p :=
  isonormalCylinderL2_coeFn _ _

omit [Fintype ι] in
theorem pastPolynomial_memLp (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (fun ω => MvPolynomial.eval (fun i => process (r i) ω) p) q gaussianProduct :=
  isonormalCylinder_memLp (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) p q hq

omit [Fintype ι] in
/-- Every finite moment of the actual coefficient/increment product exists. -/
theorem incrementProduct_memLp (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (fun ω => MvPolynomial.eval (fun i => process (r i) ω) p *
      (process t ω - process s ω)) q gaussianProduct := by
  have h2q : 2 * q ≠ ∞ := ENNReal.mul_ne_top (by simp) hq
  have : ENNReal.HolderTriple (2 * q) (2 * q) q := FiniteGaussian.doubled_holderTriple q
  exact (pastPolynomial_memLp r p (2 * q) h2q).fun_mul
    ((process_memLp t (2 * q) h2q).sub (process_memLp s (2 * q) h2q))

omit [Fintype ι] in
theorem incrementProduct_integrable (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) :
    Integrable (fun ω => MvPolynomial.eval (fun i => process (r i) ω) p *
      (process t ω - process s ω)) gaussianProduct :=
  (incrementProduct_memLp r p s t 1 (by simp)).integrable (by simp)

/-- The genuine L² product; its integrability is proved independently of past measurability. -/
def incrementProductL2 (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) (s t : ℝ≥0) : GaussianL2 :=
  (incrementProduct_memLp r p s t 2 (by simp)).toLp _

omit [Fintype ι] in
theorem incrementProductL2_coeFn (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) (s t : ℝ≥0) :
    incrementProductL2 r p s t =ᵐ[gaussianProduct]
      fun ω => MvPolynomial.eval (fun i => process (r i) ω) p *
        (process t ω - process s ω) :=
  MemLp.coeFn_toLp _

/-- A past time direction is orthogonal to a later interval direction. -/
theorem pastDirection_inner_increment (r s t : ℝ≥0) (hrs : r ≤ s) (hst : s ≤ t) :
    inner ℝ (hilbertEmbedding TimeHilbert (timeVector r)) (incrementDirection s t) = 0 := by
  unfold incrementDirection
  rw [(hilbertEmbedding TimeHilbert).inner_map_map, ← timeVector_sub s t hst,
    inner_sub_right, timeVector_inner, timeVector_inner,
    min_eq_left (show (r : ℝ) ≤ (t : ℝ) from hrs.trans hst),
    min_eq_left (show (r : ℝ) ≤ (s : ℝ) from hrs), sub_self]

/-- The contraction vanishes by differentiating the actual polynomial and using orthogonality. -/
theorem pastCoefficient_gradient_inner_increment (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) (hrs : ∀ i, r i ≤ s) (hst : s ≤ t) :
    (fun ω => inner ℝ (polynomialDerivative (pastCoefficient r p) ω)
      (incrementDirection s t)) =ᵐ[gaussianProduct] fun _ => (0 : ℝ) := by
  change (fun ω => inner ℝ
    (polynomialDerivative ⟨isonormalCylinderL2
      (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) p, _⟩ ω) _) =ᵐ[_] _
  rw [polynomialDerivative_on_cylinder]
  filter_upwards [isonormalCylinderGradientL2_coeFn
    (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) p] with ω hω
  rw [hω]
  simp only [isonormalCylinderGradient, sum_inner, real_inner_smul_left,
    pastDirection_inner_increment _ s t (hrs _) hst, mul_zero, Finset.sum_const_zero]

/-- The proved rank-one divergence formula becomes the actual coefficient/increment product. -/
theorem rankDivergence_pastCoefficient (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) (hrs : ∀ i, r i ≤ s) (hst : s ≤ t) :
    rankDivergence (pastCoefficient r p) (incrementDirection s t) =
      incrementProductL2 r p s t := by
  apply Lp.ext
  filter_upwards [rankDivergence_coeFn (pastCoefficient r p) (incrementDirection s t),
    pastCoefficient_coeFn r p, pastCoefficient_gradient_inner_increment r p s t hrs hst,
    process_increment_ae s t hst, incrementProductL2_coeFn r p s t]
      with ω hδ hG hD hB hI
  change firstChaosEmbedding (incrementDirection s t) ω = _ at hB
  simp only [hδ, hG, hD, hB, sub_zero, hI]

/-- Exact domain membership and value of the existing cylindrical divergence. -/
theorem pastCoefficient_cylindricalDivergence_graph (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) (hrs : ∀ i, r i ≤ s) (hst : s ≤ t) :
    (scalarTensor (incrementDirection s t) (pastCoefficient r p), incrementProductL2 r p s t)
      ∈ cylindricalDivergence.graph := by
  rw [← rankDivergence_pastCoefficient r p s t hrs hst]
  exact cylindricalDivergence_rank_graph _ _

/-- The full adjoint divergence retains the same actual elementary value. -/
theorem pastCoefficient_hilbertDivergence_graph (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) (hrs : ∀ i, r i ≤ s) (hst : s ≤ t) :
    (scalarTensor (incrementDirection s t) (pastCoefficient r p), incrementProductL2 r p s t)
      ∈ hilbertDivergence.graph :=
  LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (pastCoefficient_cylindricalDivergence_graph r p s t hrs hst)

/-- Finite sums have the summed elementary value;
intervals need not be disjoint for this identity. -/
theorem pastCoefficient_sum_cylindricalDivergence_graph {κ : Type*} [Fintype κ]
    (r : κ → ι → ℝ≥0) (p : κ → MvPolynomial ι ℝ) (s t : κ → ℝ≥0)
    (hrs : ∀ j i, r j i ≤ s j) (hst : ∀ j, s j ≤ t j) :
    (∑ j, scalarTensor (incrementDirection (s j) (t j)) (pastCoefficient (r j) (p j)),
      ∑ j, incrementProductL2 (r j) (p j) (s j) (t j)) ∈ cylindricalDivergence.graph := by
  have hs := cylindricalDivergence.graph.sum_mem (t := Finset.univ)
    (fun j _ => pastCoefficient_cylindricalDivergence_graph
      (r j) (p j) (s j) (t j) (hrs j) (hst j))
  convert hs using 1
  exact prod_mk_sum Finset.univ _ _

theorem pastCoefficient_sum_hilbertDivergence_graph {κ : Type*} [Fintype κ]
    (r : κ → ι → ℝ≥0) (p : κ → MvPolynomial ι ℝ) (s t : κ → ℝ≥0)
    (hrs : ∀ j i, r j i ≤ s j) (hst : ∀ j, s j ≤ t j) :
    (∑ j, scalarTensor (incrementDirection (s j) (t j)) (pastCoefficient (r j) (p j)),
      ∑ j, incrementProductL2 (r j) (p j) (s j) (t j)) ∈ hilbertDivergence.graph :=
  LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (pastCoefficient_sum_cylindricalDivergence_graph r p s t hrs hst)

end OperatorDerivativeRewrite.Foundation.GaussianTimeDivergence
