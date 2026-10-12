import Foundation.InfiniteGaussianFirstChaos
import Mathlib.Topology.Compactness.Lindelof

/-! Every separable real Hilbert space embeds isometrically into the coefficient
space of the already constructed Gaussian product model.  Countability is proved
for an actual Hilbert basis; no choice of coordinates is a hypothesis. -/

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.SeparableHilbertEmbedding

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Orthonormal families in a second-countable real inner product space have
countable index type, including empty and finite families. -/
theorem orthonormal_index_countable [SecondCountableTopology H]
    {ι : Type*} {v : ι → H} (hv : Orthonormal ℝ v) : Countable ι := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  have hsep : Pairwise (fun i j => (1 : ℝ) ≤ dist (v i) (v j)) := by
    intro i j hij
    have hsq : ‖v i - v j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, hv.1 i, hv.1 j, hv.2 hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j)]
  have he := Metric.isClosedEmbedding_of_pairwise_le_dist zero_lt_one hsep
  let : SecondCountableTopology ι := he.isEmbedding.secondCountableTopology
  exact countable_of_Lindelof_of_discrete

/-- Selected standard coordinate vectors are orthonormal whenever their
indices are distinct. -/
theorem standardCoordinates_orthonormal {ι : Type*} (e : ι ↪ ℕ) :
    Orthonormal ℝ (fun i => (lp.single 2 (e i) (1 : ℝ) :
      InfiniteGaussian.CoefficientSpace)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [lp.inner_single_left]
  simp [lp.single_apply, Pi.single_apply, e.injective.eq_iff]

/-- A countable family of coefficients is placed at distinct natural-number
coordinates by the genuine Hilbert-sum isometry. -/
def coefficientEmbedding {ι : Type*} (e : ι ↪ ℕ) :
    lp (fun _ : ι => ℝ) 2 →ₗᵢ[ℝ] InfiniteGaussian.CoefficientSpace :=
  (standardCoordinates_orthonormal e).orthogonalFamily.linearIsometry

/-- The coefficient embedding sends an actual coordinate vector to the
corresponding chosen natural-number coordinate. -/
theorem coefficientEmbedding_single {ι : Type*} [DecidableEq ι]
    (e : ι ↪ ℕ) (i : ι) (a : ℝ) :
    coefficientEmbedding e (lp.single 2 i a) = lp.single 2 (e i) a := by
  simp [coefficientEmbedding, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply, ← lp.single_smul]

/-- There is a linear isometric embedding of every separable real Hilbert space
into the countable square-summable coefficient space. -/
theorem exists_hilbertEmbedding (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H] :
    Nonempty (H →ₗᵢ[ℝ] InfiniteGaussian.CoefficientSpace) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ H
  let : Countable w := orthonormal_index_countable b.orthonormal
  obtain ⟨e, he⟩ := exists_injective_nat w
  exact ⟨(coefficientEmbedding ⟨e, he⟩).comp b.repr.toLinearIsometry⟩

/-- A fixed concrete choice of embedding, constructed from a Hilbert basis and
an injection of its countable index set into the natural numbers. -/
def hilbertEmbedding (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H] :
    H →ₗᵢ[ℝ] InfiniteGaussian.CoefficientSpace :=
  Classical.choice (exists_hilbertEmbedding H)

end OperatorDerivativeRewrite.Foundation.SeparableHilbertEmbedding
