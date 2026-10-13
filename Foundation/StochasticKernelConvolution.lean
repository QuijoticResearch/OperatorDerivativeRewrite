import Foundation.GaussianPredictableAdjoint
import Foundation.GaussianDeterministicVolterra

/-! Fixed-terminal kernel transforms of the actual predictable stochastic integral.
K is a supplied bounded map into its proved predictable domain, not a field
asserting an isometry, adjoint identity, or stochastic solution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.StochasticKernelConvolution
open InfiniteGaussian GaussianPredictableFull GaussianPredictableAdjoint
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def convolution (K : E →L[ℝ] fullPredictable) : E →L[ℝ] GaussianL2 :=
  itoIntegral.toContinuousLinearMap.comp K

theorem convolution_norm (K : E →L[ℝ] fullPredictable) (u : E) :
    ‖convolution K u‖ = ‖K u‖ := itoIntegral.norm_map _

theorem convolution_inner (K : E →L[ℝ] fullPredictable) (u v : E) :
    inner ℝ (convolution K u) (convolution K v) = inner ℝ (K u) (K v) :=
  itoIntegral.inner_map_map _ _

theorem convolution_bound (K : E →L[ℝ] fullPredictable) (u : E) :
    ‖convolution K u‖ ≤ ‖K‖ * ‖u‖ := by
  rw [convolution_norm]
  exact K.le_opNorm u

theorem convolution_pair_integrable (K : E →L[ℝ] fullPredictable) (u v : E) :
    Integrable (fun ω => convolution K u ω * convolution K v ω) gaussianProduct :=
  mul_L2_integrable (Lp.memLp _) (Lp.memLp _)

theorem convolution_adjoint (K : E →L[ℝ] fullPredictable) :
    (convolution K).adjoint = K.adjoint.comp predictableAdjoint :=
  ContinuousLinearMap.adjoint_comp _ _

theorem convolution_adjoint_derivative (K : E →L[ℝ] fullPredictable)
    (F : closedCylindricalDerivative.domain) :
    (convolution K).adjoint (F : GaussianL2) =
      K.adjoint (predictableProjection (closedCylindricalDerivative F)) := by
  rw [convolution_adjoint, ContinuousLinearMap.comp_apply,
    predictableAdjoint_eq_projected_derivative]

theorem convolution_normal (K : E →L[ℝ] fullPredictable) :
    (convolution K).adjoint.comp (convolution K) = K.adjoint.comp K := by
  ext u
  simp only [convolution_adjoint, ContinuousLinearMap.comp_apply]
  change K.adjoint (predictableAdjoint (itoIntegral (K u))) = _
  rw [predictableAdjoint_integral]

theorem convolution_zero_iff (K : E →L[ℝ] fullPredictable) (u : E) :
    convolution K u = 0 ↔ K u = 0 := by
  rw [← norm_eq_zero, convolution_norm, norm_eq_zero]

theorem convolution_divergence_graph (K : E →L[ℝ] fullPredictable) (u : E) :
    (predictableField (K u), convolution K u) ∈ hilbertDivergence.graph :=
  predictableField_divergence_graph _

/-- An explicitly constructed finite-rank predictable kernel transform. -/
def finiteKernel {ι : Type*} [Fintype ι] (ℓ : ι → E →L[ℝ] ℝ)
    (v : ι → fullPredictable) : E →L[ℝ] fullPredictable :=
  ∑ i, (ℓ i).smulRight (v i)

theorem finiteKernel_apply {ι : Type*} [Fintype ι] (ℓ : ι → E →L[ℝ] ℝ)
    (v : ι → fullPredictable) (u : E) : finiteKernel ℓ v u = ∑ i, ℓ i u • v i := by
  simp [finiteKernel]

theorem finite_convolution_apply {ι : Type*} [Fintype ι] (ℓ : ι → E →L[ℝ] ℝ)
    (v : ι → fullPredictable) (u : E) :
    convolution (finiteKernel ℓ v) u = ∑ i, ℓ i u • itoIntegral (v i) := by
  change itoIntegral (finiteKernel ℓ v u) = _
  rw [finiteKernel_apply, map_sum]
  simp only [map_smul]

theorem finite_convolution_energy {ι : Type*} [Fintype ι] (ℓ : ι → E →L[ℝ] ℝ)
    (v : ι → fullPredictable) (u : E) :
    ‖convolution (finiteKernel ℓ v) u‖^2 =
      ∑ i, ∑ j, ℓ i u * ℓ j u * inner ℝ (v i) (v j) := by
  rw [convolution_norm, finiteKernel_apply, ← real_inner_self_eq_norm_sq]
  simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Submodule.coe_inner, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (v j : GaussianTimeProductL2.TimeProbabilityL2)
    (v i : GaussianTimeProductL2.TimeProbabilityL2)]
  ring

/-- Exact operator error transport, with no isometry assumption on the kernel. -/
theorem convolution_operator_error (K L : E →L[ℝ] fullPredictable) :
    ‖convolution K - convolution L‖ = ‖K - L‖ := by
  change ‖itoIntegral.toContinuousLinearMap.comp K -
    itoIntegral.toContinuousLinearMap.comp L‖ = _
  rw [← ContinuousLinearMap.comp_sub]
  exact itoIntegral.norm_toContinuousLinearMap_comp

/-- Strong kernel convergence is equivalent to strong stochastic convergence. -/
theorem convolution_tendsto_iff {ι : Type*} (a : Filter ι)
    (K : ι → E →L[ℝ] fullPredictable) (L : E →L[ℝ] fullPredictable) (u : E) :
    Filter.Tendsto (fun i => convolution (K i) u) a (nhds (convolution L u)) ↔
      Filter.Tendsto (fun i => K i u) a (nhds (L u)) := by
  exact (itoIntegral.isometry.tendsto_nhds_iff).symm

/-- Uniform kernel convergence is equivalent to convergence in stochastic operator norm. -/
theorem convolution_operator_tendsto_iff {ι : Type*} (a : Filter ι)
    (K : ι → E →L[ℝ] fullPredictable) (L : E →L[ℝ] fullPredictable) :
    Filter.Tendsto (fun i => convolution (K i)) a (nhds (convolution L)) ↔
      Filter.Tendsto K a (nhds L) := by
  exact ((itoIntegral.postcomp (E := E)).isometry.tendsto_nhds_iff).symm
end OperatorDerivativeRewrite.Foundation.StochasticKernelConvolution
