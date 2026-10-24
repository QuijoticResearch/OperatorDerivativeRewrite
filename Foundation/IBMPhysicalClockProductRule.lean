import Foundation.IBMPhysicalClockCrossVariation

/-! Actual two-sided left-sum product rule for the physical correction and
clock. Their SUM converges in L1; individual stochastic integrals are not
asserted to exist by this theorem. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalClockProductRule
open InfiniteGaussian IBMPhysicalWeakWiener IBMConstructedSources GaussianTimeProcess
open IBMPhysicalClockCrossVariation
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul

theorem clock_memLp (t : ℝ≥0) : MemLp (fun Y => clockPath Y t) 2 gaussianProduct :=
  (Lp.memLp (wienerL2 t)).ae_eq (clockPath_coordinate_ae t).symm

def leftClockSum {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (Y : SampleSpace) : Kernel :=
  ∑ i : Fin n, clockPath Y (τ i.castSucc) •
    (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-
      IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y)

def leftCorrectionSum {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (Y : SampleSpace) : Kernel :=
  ∑ i : Fin n, (clockPath Y (τ i.succ)-clockPath Y (τ i.castSucc)) •
    IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y

theorem leftClockSum_integrable {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) :
    Integrable (leftClockSum τ) gaussianProduct :=
  integrable_finsetSum _ fun (i : Fin n) _hi => product_integrable _ _
    ((Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ))).sub
      (Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc)))) (clock_memLp _)

theorem leftCorrectionSum_integrable {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) :
    Integrable (leftCorrectionSum τ) gaussianProduct :=
  integrable_finsetSum _ fun (i : Fin n) _hi => product_integrable _ _
    (Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc))) (clock_increment_memLp _ _)

private theorem telescope {n : ℕ} (f : Fin (n + 1) → Kernel) :
    (∑ i : Fin n, (f i.succ-f i.castSucc)) = f (Fin.last n)-f 0 := by
  rw [Finset.sum_sub_distrib]
  calc
    _ = (f 0+∑ i : Fin n, f i.succ)-((∑ i : Fin n, f i.castSucc)+f 0) := by abel
    _ = ((∑ i : Fin n, f i.castSucc)+f (Fin.last n))-((∑ i : Fin n, f i.castSucc)+f 0) := by
      rw [← Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    _ = _ := by abel

theorem finite_product_rule {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (Y : SampleSpace) :
    clockPath Y (τ (Fin.last n)) • IBMPhysicalPointKernelIto.correctionLimit (τ (Fin.last n)) Y-
      clockPath Y (τ 0) • IBMPhysicalPointKernelIto.correctionLimit (τ 0) Y =
        leftClockSum τ Y+leftCorrectionSum τ Y+cross τ Y := by
  calc
    _ = ∑ i : Fin n, (clockPath Y (τ i.succ) • IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-
        clockPath Y (τ i.castSucc) • IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y) :=
      (telescope (fun i => clockPath Y (τ i) • IBMPhysicalPointKernelIto.correctionLimit (τ i) Y)).symm
    _ = ∑ i : Fin n, (clockPath Y (τ i.castSucc) •
        (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y)+
          (clockPath Y (τ i.succ)-clockPath Y (τ i.castSucc)) • IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y+
            (clockPath Y (τ i.succ)-clockPath Y (τ i.castSucc)) •
              (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      module
    _ = _ := by simp only [Finset.sum_add_distrib, leftClockSum, leftCorrectionSum, cross]

def endpoint (T : ℝ≥0) (Y : SampleSpace) : Kernel :=
  clockPath Y T • IBMPhysicalPointKernelIto.correctionLimit T Y-
    clockPath Y 0 • IBMPhysicalPointKernelIto.correctionLimit 0 Y

theorem endpoint_integrable (T : ℝ≥0) : Integrable (endpoint T) gaussianProduct :=
  (product_integrable _ _ (Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit T)) (clock_memLp T)).sub
    (product_integrable _ _ (Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit 0)) (clock_memLp 0))

def endpointClass (T : ℝ≥0) : Lp Kernel 1 gaussianProduct := (endpoint_integrable T).toL1 (endpoint T)

theorem endpointClass_ae (T : ℝ≥0) : endpointClass T =ᵐ[gaussianProduct] endpoint T :=
  (endpoint_integrable T).coeFn_toL1

def pairClass {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : Lp Kernel 1 gaussianProduct :=
  ((leftClockSum_integrable τ).add (leftCorrectionSum_integrable τ)).toL1
    (fun Y => leftClockSum τ Y+leftCorrectionSum τ Y)

theorem pairClass_ae {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : pairClass τ =ᵐ[gaussianProduct]
    fun Y => leftClockSum τ Y+leftCorrectionSum τ Y :=
  ((leftClockSum_integrable τ).add (leftCorrectionSum_integrable τ)).coeFn_toL1

theorem pairClass_identity {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0)
    (hz : τ 0 = 0) (hend : τ (Fin.last n) = T) :
    pairClass τ = endpointClass T-crossClass τ := by
  apply Lp.ext
  filter_upwards [pairClass_ae τ, endpointClass_ae T, crossClass_ae τ,
    Lp.coeFn_sub (endpointClass T) (crossClass τ)] with Y hp he hc hs
  simp only [Pi.sub_apply] at hs
  rw [hp, hs, he, hc]
  have h := finite_product_rule τ Y
  rw [hz, hend] at h
  change leftClockSum τ Y+leftCorrectionSum τ Y = endpoint T Y-cross τ Y
  change endpoint T Y = leftClockSum τ Y+leftCorrectionSum τ Y+cross τ Y at h
  rw [h]
  abel

theorem pairClass_tendsto (T : ℝ≥0) (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N + 1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hz : ∀ N, τ N 0 = 0)
    (hend : ∀ N, τ N (Fin.last (m N)) = T) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (nhds 0))
    (hmesh : ∀ (N : ℕ) (i : Fin (m N)), (τ N i.succ : ℝ) - τ N i.castSucc ≤ ε N) :
    Tendsto (fun N => pairClass (τ N)) atTop (nhds (endpointClass T)) := by
  have h := (tendsto_const_nhds (x := endpointClass T)).sub
    (crossClass_tendsto T m τ hτ hz hend ε hε hmesh)
  simpa only [← pairClass_identity T _ (hz _) (hend _), sub_zero] using h

end OperatorDerivativeRewrite.Foundation.IBMPhysicalClockProductRule
