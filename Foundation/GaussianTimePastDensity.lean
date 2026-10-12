import Foundation.GaussianGeneratedDensity
import Foundation.GaussianTimeObservationDensity

/-! Genuine polynomial density in the full raw Brownian past. -/
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTimePastDensity
open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence GaussianTimeHilbert
open SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

/-- Polynomials have finite algebraic support even though their available
variables comprise the whole (possibly uncountable) time past. -/
def pastPolynomialEmbedding (s : ℝ≥0) : MvPolynomial (Set.Iic s) ℝ →ₗ[ℝ] GaussianL2 :=
  familyPolynomialEmbedding (fun t => hilbertEmbedding TimeHilbert (timeVector t))

/-- Equality with the independently defined full raw natural-filtration L2
subspace. This is stronger than fixed finite-observation density. -/
theorem pastPolynomial_closure (s : ℝ≥0) :
    (pastPolynomialEmbedding s).range.topologicalClosure =
      lpMeas ℝ ℝ (naturalFiltration s) 2 gaussianProduct := by
  change (familyPolynomialEmbedding
    (fun t : Set.Iic s => hilbertEmbedding TimeHilbert (timeVector t))).range.topologicalClosure = _
  rw [familyPolynomial_closure]
  congr 1
  exact (Filtration.natural_eq_comap process process_stronglyMeasurable s).symm

/-- Every past-measurable L2 coefficient has an approximation by one polynomial
in finitely many observations, each provably at or before s. -/
theorem exists_pastPolynomial_approx (s : ℝ≥0) (F : GaussianL2)
    (hF : AEStronglyMeasurable[naturalFiltration s] F gaussianProduct)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (v : Finset (Set.Iic s)) (p : MvPolynomial v ℝ),
      ‖F - (pastCoefficient (fun i : v => (i.val : ℝ≥0)) p : GaussianL2)‖ < ε := by
  have hc : F ∈ (pastPolynomialEmbedding s).range.topologicalClosure := by
    rw [pastPolynomial_closure]
    exact hF
  obtain ⟨G, ⟨p, rfl⟩, hp⟩ := Metric.mem_closure_iff.mp hc ε hε
  obtain ⟨v, q, rfl⟩ := exists_finset_rename p
  refine ⟨v, q, ?_⟩
  change dist F (familyPolynomialEmbedding
    (fun t : Set.Iic s => hilbertEmbedding TimeHilbert (timeVector t))
      (rename Subtype.val q)) < ε at hp
  rw [familyPolynomial_rename] at hp
  simpa only [dist_eq_norm, GaussianTimeDivergence.pastCoefficient] using hp

/-- Reindexing finite observations leaves the actual polynomial class unchanged. -/
theorem pastCoefficient_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) :
    (pastCoefficient (r ∘ e.symm) (rename e p) : GaussianL2) = pastCoefficient r p := by
  apply Lp.ext
  filter_upwards [pastCoefficient_coeFn (r ∘ e.symm) (rename e p), pastCoefficient_coeFn r p]
    with ω hl hr
  rw [hl, hr]
  simp [eval_rename, Function.comp_def]

/-- A Fin-indexed version matches the existing polynomial predictable-step
generators exactly, retaining the proved past restriction. -/
theorem exists_fin_pastPolynomial_approx (s : ℝ≥0) (F : GaussianL2)
    (hF : AEStronglyMeasurable[naturalFiltration s] F gaussianProduct)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (r : Fin n → ℝ≥0) (p : MvPolynomial (Fin n) ℝ),
      (∀ i, r i ≤ s) ∧ ‖F - (pastCoefficient r p : GaussianL2)‖ < ε := by
  classical
  obtain ⟨v, p, hp⟩ := exists_pastPolynomial_approx s F hF ε hε
  let e := Fintype.equivFin v
  let r : v → ℝ≥0 := fun i => i.val
  refine ⟨Fintype.card v, r ∘ e.symm, rename e p, ?_, ?_⟩
  · intro i
    exact (e.symm i).val.property
  · rw [pastCoefficient_equiv]
    exact hp

end OperatorDerivativeRewrite.Foundation.GaussianTimePastDensity
