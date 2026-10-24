import Foundation.IBMPhysicalL2ToL1

/-! A genuine physical forward integral against the original IBM correction:
actual clock-left sums converge in L1, with the physical product identity. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalForwardIntegral
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalClockProductRule
open IBMPhysicalL2ToL1 IBMPhysicalCorrectionIntegral IBMConstructedSources
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul

def native {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : Lp Kernel 1 gaussianProduct :=
  (leftClockSum_integrable τ).toL1 (leftClockSum τ)

theorem native_ae {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    native τ =ᵐ[gaussianProduct] leftClockSum τ :=
  (leftClockSum_integrable τ).coeFn_toL1

theorem native_eq_pair_sub {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    native τ = pairClass τ-inclusion (IBMPhysicalCorrectionSteps.partitionClass τ hτ) := by
  apply Lp.ext
  filter_upwards [native_ae τ, pairClass_ae τ,
    inclusion_ae (IBMPhysicalCorrectionSteps.partitionClass τ hτ),
    IBMPhysicalCorrectionSteps.partitionClass_ae τ hτ,
    Lp.coeFn_sub (pairClass τ) (inclusion (IBMPhysicalCorrectionSteps.partitionClass τ hτ))]
    with Y hn hp hi hc hs
  simp only [Pi.sub_apply] at hs
  rw [hn, hs, hp, hi, hc]
  abel

def integralValue (T : ℝ≥0) : Lp Kernel 1 gaussianProduct :=
  endpointClass T-inclusion (IBMPhysicalCorrectionIntegral.integralValue T)

theorem native_tendsto (T : ℝ≥0) (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hz : ∀ N, τ N 0 = 0)
    (hend : ∀ N, τ N (Fin.last (m N)) = T) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (i : Fin (m N)), (τ N i.succ : ℝ)-τ N i.castSucc ≤ ε N) :
    Tendsto (fun N => native (τ N)) atTop (𝓝 (integralValue T)) := by
  have hc := inclusion.continuous.tendsto (IBMPhysicalCorrectionIntegral.integralValue T) |>.comp
    (IBMPhysicalCorrectionIntegral.native_tendsto m τ hτ T hz hend ε hε hmesh)
  have hp := (pairClass_tendsto T m τ hτ hz hend ε hε hmesh).sub hc
  simpa only [Function.comp_def, ← native_eq_pair_sub _ (hτ _), integralValue] using hp

theorem product_identity (T : ℝ≥0) : endpointClass T = integralValue T+
    inclusion (IBMPhysicalCorrectionIntegral.integralValue T) := by
  unfold integralValue
  abel

theorem product_identity_actual (T : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct,
    clockPath Y T • IBMPhysicalPointKernelIto.correctionLimit T Y-
      clockPath Y 0 • IBMPhysicalPointKernelIto.correctionLimit 0 Y =
        integralValue T Y+IBMPhysicalCorrectionIntegral.integralValue T Y := by
  filter_upwards [endpointClass_ae T,
    inclusion_ae (IBMPhysicalCorrectionIntegral.integralValue T),
    Lp.coeFn_sub (endpointClass T) (inclusion (IBMPhysicalCorrectionIntegral.integralValue T))]
    with Y he hi hs
  change endpoint T Y = (endpointClass T-inclusion
    (IBMPhysicalCorrectionIntegral.integralValue T)) Y+_
  simp only [hs, Pi.sub_apply, he, hi]
  abel

theorem native_scalarization {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (L : Tests) :
    L.compLpL 1 gaussianProduct (native τ) =ᵐ[gaussianProduct] fun Y =>
      ∑ i : Fin n, clockPath Y (τ i.castSucc) * L
        (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-
          IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y) := by
  filter_upwards [L.coeFn_compLpL (native τ), native_ae τ] with Y hl hn
  rw [hl, hn]
  simp only [leftClockSum, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  convert L.map_smul (clockPath Y (τ i.castSucc))
    (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-
      IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y) using 1
  apply congrArg L
  apply BesselPotentialSpace.ext
  simp only [BesselPotentialSpace.toDistr_smul]
  rfl

theorem scalarization_tendsto (T : ℝ≥0) (L : Tests) (m : ℕ → ℕ)
    (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0) (hτ : ∀ N, Monotone (τ N))
    (hz : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (i : Fin (m N)), (τ N i.succ : ℝ)-τ N i.castSucc ≤ ε N) :
    Tendsto (fun N => L.compLpL 1 gaussianProduct (native (τ N))) atTop
      (𝓝 (L.compLpL 1 gaussianProduct (integralValue T))) :=
  (L.compLpL 1 gaussianProduct).continuous.tendsto _ |>.comp
    (native_tendsto T m τ hτ hz hend ε hε hmesh)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalForwardIntegral
