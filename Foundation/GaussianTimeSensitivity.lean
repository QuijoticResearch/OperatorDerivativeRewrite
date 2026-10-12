import Foundation.GaussianTimePolynomialPairing

/-!
# Genuine Gaussian sensitivity of polynomial time-step integrals

The derivative of `A * (B_t - B_s)` retains both the original interval field
and the extra term `(B_t - B_s) * D A`. The terms are actual L² products on the
verified polynomial domain, not independently prescribed derivative data.
This finite-polynomial result makes no assertion about differentiating the
completed stochastic integral on its whole domain.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal NNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianTimeSensitivity

open InfiniteGaussian GaussianTimeDivergence GaussianTimeProcess
open GaussianTimePolynomialPairing GaussianTimePolynomialIntegral
open GaussianTimeHilbert SeparableHilbertEmbedding GaussianTimeFieldNorm
attribute [local instance] timeHilbert_secondCountable
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

/-- An actual polynomial product in the already verified scalar operator domain. -/
def incrementProductPolynomial (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) : polynomialCylindricalDomain :=
  polynomialProduct (pastCoefficient r p) (firstChaosPolynomial (incrementDirection s t))

/-- This actual domain element is exactly the previously defined increment-product L² class. -/
theorem incrementProductPolynomial_eq (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (incrementProductPolynomial r p s t : GaussianL2) = incrementProductL2 r p s t := by
  apply Lp.ext
  filter_upwards [polynomialProductL2_coeFn (pastCoefficient r p)
      (firstChaosPolynomial (incrementDirection s t)),
    pastCoefficient_coeFn r p, firstChaosPolynomial_coeFn (incrementDirection s t),
    process_increment_ae s t hst, incrementProductL2_coeFn r p s t]
    with ω hp hA hW hB hI
  change firstChaosEmbedding (incrementDirection s t) ω = _ at hB
  change polynomialProductL2 (pastCoefficient r p)
    (firstChaosPolynomial (incrementDirection s t)) ω = _
  rw [hp, hA, hW, hB, hI]

omit [Fintype ι] in
theorem incrementProduct_mem_polynomialDomain [Finite ι]
    (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) : incrementProductL2 r p s t ∈ polynomialCylindricalDomain := by
  let := Fintype.ofFinite ι
  rw [← incrementProductPolynomial_eq r p s t hst]
  exact (incrementProductPolynomial r p s t).property

/-- The sensitivity is the actual first-chaos factor times the actual polynomial derivative. -/
def incrementSensitivity (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) : GaussianVectorL2 :=
  polynomialTimesDerivative (firstChaosPolynomial (incrementDirection s t)) (pastCoefficient r p)

theorem incrementSensitivity_coeFn (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    incrementSensitivity r p s t =ᵐ[gaussianProduct]
      fun ω => (process t ω - process s ω) • polynomialDerivative (pastCoefficient r p) ω := by
  filter_upwards [polynomialTimesDerivative_coeFn
      (firstChaosPolynomial (incrementDirection s t)) (pastCoefficient r p),
    firstChaosPolynomial_coeFn (incrementDirection s t), process_increment_ae s t hst]
    with ω hS hW hB
  change firstChaosEmbedding (incrementDirection s t) ω = _ at hB
  change polynomialTimesDerivative (firstChaosPolynomial (incrementDirection s t))
    (pastCoefficient r p) ω = _
  rw [hS, hW, hB]

/-- All finite moments of the sensitivity integrand follow from proved polynomial moments. -/
theorem incrementSensitivity_fun_memLp (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (fun ω => (process t ω - process s ω) •
      polynomialDerivative (pastCoefficient r p) ω) q gaussianProduct := by
  have hm := polynomialDomain_smul_derivative_memLp
    (firstChaosPolynomial (incrementDirection s t)) (pastCoefficient r p) q hq
  apply hm.ae_eq
  filter_upwards [firstChaosPolynomial_coeFn (incrementDirection s t),
    process_increment_ae s t hst] with ω hW hB
  change firstChaosEmbedding (incrementDirection s t) ω = _ at hB
  rw [hW, hB]

/-- Differentiating a genuine polynomial times a first-chaos coordinate produces
the deterministic-direction field as its first product-rule term. -/
theorem polynomialTimesDerivative_firstChaos (f : polynomialCylindricalDomain)
    (h : CoefficientSpace) : polynomialTimesDerivative f (firstChaosPolynomial h) =
      scalarTensor h f := by
  apply Lp.ext
  filter_upwards [polynomialTimesDerivative_coeFn f (firstChaosPolynomial h),
    firstChaosPolynomial_derivative_coeFn h, scalarTensor_coeFn h f] with ω hp hD ht
  rw [hp, hD, ht]

/-- The actual polynomial derivative retains both terms; no sensitivity cancellation is assumed. -/
theorem incrementProductPolynomial_derivative (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ)
    (s t : ℝ≥0) :
    polynomialDerivative (incrementProductPolynomial r p s t) =
      scalarTensor (incrementDirection s t) (pastCoefficient r p) +
        incrementSensitivity r p s t := by
  unfold incrementProductPolynomial
  rw [polynomialDerivative_product, polynomialTimesDerivative_firstChaos]
  rfl

/-- Exact domain and value for the original polynomial derivative operator. -/
theorem incrementProduct_cylindricalDerivative_graph (r : ι → ℝ≥0)
    (p : MvPolynomial ι ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (incrementProductL2 r p s t,
      scalarTensor (incrementDirection s t) (pastCoefficient r p) + incrementSensitivity r p s t)
      ∈ cylindricalDerivative.graph := by
  have h := cylindricalDerivative.mem_graph (incrementProductPolynomial r p s t)
  change ((incrementProductPolynomial r p s t : GaussianL2),
    polynomialDerivative (incrementProductPolynomial r p s t)) ∈ cylindricalDerivative.graph at h
  rwa [incrementProductPolynomial_eq r p s t hst, incrementProductPolynomial_derivative] at h

/-- The existing closed Gaussian derivative agrees with the same genuine two-term formula. -/
theorem incrementProduct_closedDerivative_graph (r : ι → ℝ≥0)
    (p : MvPolynomial ι ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (incrementProductL2 r p s t,
      scalarTensor (incrementDirection s t) (pastCoefficient r p) + incrementSensitivity r p s t)
      ∈ closedCylindricalDerivative.graph :=
  LinearPMap.le_graph_of_le cylindricalDerivative.le_closure
    (incrementProduct_cylindricalDerivative_graph r p s t hst)

/-- Finite sums retain the sum of all sensitivity terms, including overlapping time intervals. -/
theorem sum_incrementProduct_closedDerivative_graph {κ : Type*} [Fintype κ]
    (r : κ → ι → ℝ≥0) (p : κ → MvPolynomial ι ℝ) (s t : κ → ℝ≥0)
    (hst : ∀ j, s j ≤ t j) :
    (∑ j, incrementProductL2 (r j) (p j) (s j) (t j),
      (∑ j, scalarTensor (incrementDirection (s j) (t j)) (pastCoefficient (r j) (p j))) +
        ∑ j, incrementSensitivity (r j) (p j) (s j) (t j))
      ∈ closedCylindricalDerivative.graph := by
  have hg := closedCylindricalDerivative.graph.sum_mem (t := Finset.univ)
    (fun j _ => incrementProduct_closedDerivative_graph (r j) (p j) (s j) (t j) (hst j))
  simpa only [← prod_mk_sum, Finset.sum_add_distrib] using hg

/-- The already constructed predictable polynomial integral belongs to the actual
closed derivative domain, with the retained finite sensitivity sum. -/
theorem polynomialPartitionIntegralL2_closedDerivative_graph {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (r : (i : Fin n) → ι → Set.Iic (τ i.castSucc)) (p : Fin n → MvPolynomial ι ℝ) :
    (polynomialPartitionIntegralL2 τ hτ r p,
      polynomialPartitionField τ r p +
        ∑ i, incrementSensitivity (fun j => r i j) (p i) (τ i.castSucc) (τ i.succ))
      ∈ closedCylindricalDerivative.graph := by
  rw [polynomialPartitionIntegralL2_eq_sum]
  exact sum_incrementProduct_closedDerivative_graph (fun i j => r i j) p
    (fun i => τ i.castSucc) (fun i => τ i.succ)
    (fun i => hτ (Fin.castSucc_le_succ i))

/-- The polynomial coordinate has precisely the norm of its deterministic direction. -/
theorem firstChaosPolynomial_norm (h : CoefficientSpace) :
    ‖(firstChaosPolynomial h : GaussianL2)‖ = ‖h‖ := by
  have he : (firstChaosPolynomial h : GaussianL2) = firstChaosEmbedding h :=
    Lp.ext (firstChaosPolynomial_coeFn h)
  rw [he, firstChaos_norm]

/-- For the genuine adapted coefficient `A = B_a`, the extra term is the
future increment multiplied by the early-time direction `(0,a]`. -/
theorem incrementSensitivity_X (a b : ℝ≥0) :
    incrementSensitivity (fun _ : Unit => a) (X ()) a b =
      scalarTensor (hilbertEmbedding TimeHilbert (timeVector a))
        (firstChaosPolynomial (incrementDirection a b)) :=
  polynomialTimesDerivative_firstChaos (firstChaosPolynomial (incrementDirection a b))
    (hilbertEmbedding TimeHilbert (timeVector a))

/-- The early-time sensitivity has positive energy whenever `0 < a < b`. -/
theorem incrementSensitivity_X_norm_sq (a b : ℝ≥0) (hab : a ≤ b) :
    ‖incrementSensitivity (fun _ : Unit => a) (X ()) a b‖ ^ 2 =
      (a : ℝ) * ((b : ℝ) - a) := by
  rw [incrementSensitivity_X, ← real_inner_self_eq_norm_sq, scalarTensor_pair_inner,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, firstChaosPolynomial_norm,
    incrementDirection_norm_sq a b hab, (hilbertEmbedding TimeHilbert).norm_map,
    timeVector_norm_sq]
  ring

theorem incrementSensitivity_X_ne_zero (a b : ℝ≥0) (ha : 0 < a) (hab : a < b) :
    incrementSensitivity (fun _ : Unit => a) (X ()) a b ≠ 0 := by
  intro hz
  have hn := incrementSensitivity_X_norm_sq a b hab.le
  rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn
  have ha' : (0 : ℝ) < a := ha
  have hab' : (a : ℝ) < b := hab
  exact (mul_pos ha' (sub_pos.mpr hab')).ne' hn.symm

/-- The actual closed derivative of `B_a (B_b-B_a)` cannot equal its original
adapted interval field. The nonzero early-time term is indispensable. -/
theorem incrementProduct_X_not_originalField_graph (a b : ℝ≥0)
    (ha : 0 < a) (hab : a < b) :
    (incrementProductL2 (fun _ : Unit => a) (X ()) a b,
      scalarTensor (incrementDirection a b) (pastCoefficient (fun _ : Unit => a) (X ())))
      ∉ closedCylindricalDerivative.graph := by
  intro hg
  have hactual := incrementProduct_closedDerivative_graph
    (fun _ : Unit => a) (X ()) a b hab.le
  have he := closedCylindricalDerivative.mem_graph_snd_inj hactual hg rfl
  exact incrementSensitivity_X_ne_zero a b ha hab
    (add_left_cancel (he.trans (add_zero _).symm))

end OperatorDerivativeRewrite.Foundation.GaussianTimeSensitivity
