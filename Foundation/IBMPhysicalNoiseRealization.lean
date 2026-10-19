import Foundation.IBMPhysicalNoiseVectors
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A physical Lebesgue-L2 white-noise realization of the already constructed
Brownian scenery, on the same Gaussian probability space. The isometry is
fixed by all two-sided Brownian indicator coordinates, not an arbitrary basis. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalNoiseRealization
open InfiniteGaussian GaussianTimeHilbert IBMPhysicalNoiseVectors
open IBMFullSchwartzTerminal IBMQuarticPrimitiveLimit IBMContinuousScenery

theorem base_norm_sq (r : ℝ) : ‖baseCoefficient r‖^2 = |r| := by
  calc
    _ = ‖firstChaosEmbedding (baseCoefficient r)‖^2 := by rw [firstChaosEmbedding.norm_map]
    _ = _ := by rw [base_embedding, IBMRandomTimeHilbert.sourceScenery_norm_sq]

theorem base_increment_sq (s r : ℝ) : ‖baseCoefficient r-baseCoefficient s‖^2 = |r-s| := by
  calc
    _ = ‖firstChaosEmbedding (baseCoefficient r-baseCoefficient s)‖^2 := by
      rw [firstChaosEmbedding.norm_map]
    _ = _ := by rw [map_sub, base_embedding, base_embedding, sourceScenery_increment_sq]

theorem base_inner_eq_physical (s r : ℝ) :
    inner ℝ (baseCoefficient s) (baseCoefficient r) = inner ℝ (vector s) (vector r) := by
  have hp := norm_sub_sq_real (vector s) (vector r)
  have hs := norm_sub_sq_real (baseCoefficient s) (baseCoefficient r)
  rw [vector_increment_sq, vector_norm_sq, vector_norm_sq] at hp
  rw [base_increment_sq, base_norm_sq, base_norm_sq] at hs
  linarith

def physicalCombination : (ℝ →₀ ℝ) →ₗ[ℝ] TimeHilbert := Finsupp.linearCombination ℝ vector

def sourceCombination : (ℝ →₀ ℝ) →ₗ[ℝ] CoefficientSpace := Finsupp.linearCombination ℝ baseCoefficient

theorem physicalCombination_dense : DenseRange physicalCombination := by
  rw [denseRange_iff_closure_range]
  change closure ((LinearMap.range (Finsupp.linearCombination ℝ vector) : Submodule ℝ TimeHilbert) :
    Set TimeHilbert) = Set.univ
  rw [Finsupp.range_linearCombination, ← Submodule.topologicalClosure_coe, span_dense]
  rfl

theorem combination_inner (c d : ℝ →₀ ℝ) :
    inner ℝ (sourceCombination c) (sourceCombination d) =
      inner ℝ (physicalCombination c) (physicalCombination d) := by
  simp only [sourceCombination, physicalCombination, Finsupp.linearCombination_apply, Finsupp.sum,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, base_inner_eq_physical]

theorem combination_norm (c : ℝ →₀ ℝ) : ‖sourceCombination c‖ = ‖physicalCombination c‖ := by
  have he := combination_inner c c
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (sourceCombination c), norm_nonneg (physicalCombination c)]

/-- Defined on every actual Lebesgue-L2 physical kernel, with no density or
realization hypothesis. Its defining finite sums are norm-identical. -/
def physicalToCoefficient : TimeHilbert →ₗᵢ[ℝ] CoefficientSpace :=
  sourceCombination.extendOfIsometry physicalCombination_dense combination_norm

theorem physicalToCoefficient_vector (r : ℝ) : physicalToCoefficient (vector r) = baseCoefficient r := by
  have he := sourceCombination.extendOfIsometry_eq physicalCombination_dense combination_norm
    (Finsupp.single r 1)
  simpa [physicalToCoefficient, physicalCombination, sourceCombination] using he

/-- The white noise uses the existing Gaussian source rather than a new law. -/
def physicalNoise : TimeHilbert →ₗᵢ[ℝ] GaussianL2 := firstChaosEmbedding.comp physicalToCoefficient

theorem physicalNoise_vector (r : ℝ) : physicalNoise (vector r) = sourceScenery r := by
  change firstChaosEmbedding (physicalToCoefficient (vector r)) = _
  rw [physicalToCoefficient_vector, base_embedding]

theorem physicalNoise_interval {a b : ℝ} (hab : a ≤ b) :
    physicalNoise (intervalVector a b) = sourceScenery b-sourceScenery a := by
  rw [← vector_sub hab, map_sub, physicalNoise_vector, physicalNoise_vector]

theorem physicalNoise_inner (f h : TimeHilbert) :
    inner ℝ (physicalNoise f) (physicalNoise h) = ∫ x, f x*h x := by
  rw [physicalNoise.inner_map_map, L2_inner_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [mul_comm]

theorem physicalNoise_isGaussianProcess :
    IsGaussianProcess (fun f : TimeHilbert => (physicalNoise f : SampleSpace → ℝ)) gaussianProduct :=
  firstChaos_isGaussianProcess.comp_right physicalToCoefficient

theorem physicalNoise_law (f : TimeHilbert) :
    gaussianProduct.map (physicalNoise f) =
      gaussianReal 0 (NNReal.mk (‖f‖^2) (sq_nonneg _)) := by
  change gaussianProduct.map (firstChaosEmbedding (physicalToCoefficient f)) = _
  rw [firstChaos_law, physicalToCoefficient.norm_map]

theorem physicalNoise_mean (f : TimeHilbert) :
    (∫ ω, physicalNoise f ω ∂gaussianProduct) = 0 :=
  firstChaos_integral (physicalToCoefficient f)

theorem physicalNoise_covariance (f h : TimeHilbert) :
    cov[physicalNoise f,physicalNoise h;gaussianProduct] = inner ℝ f h := by
  change cov[firstChaosEmbedding (physicalToCoefficient f),
    firstChaosEmbedding (physicalToCoefficient h);gaussianProduct] = _
  rw [firstChaos_covariance, physicalToCoefficient.inner_map_map]

/-- A physical kernel limit is realized in the same actual scenery source. -/
theorem physicalNoise_tendsto {f : ℕ → TimeHilbert} {h : TimeHilbert}
    (hf : Tendsto f atTop (𝓝 h)) :
    Tendsto (fun n => physicalNoise (f n)) atTop (𝓝 (physicalNoise h)) :=
  physicalNoise.continuous.tendsto h |>.comp hf

end OperatorDerivativeRewrite.Foundation.IBMPhysicalNoiseRealization
