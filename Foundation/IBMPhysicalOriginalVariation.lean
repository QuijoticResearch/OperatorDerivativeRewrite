import Foundation.BrownianLocalTimeSquares

/-! The ORIGINAL physical IBM correction, with its genuine origin local
time retained, has uniform-grid squared increment sums tending strongly
to zero in L1. No arbitrary-partition or bounded-variation claim is made. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalOriginalVariation
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalDirac
open GaussianBrownianQuadraticVariation IBMPhysicalCorrectionLocalTime
open BrownianMassContinuousLimit
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul

theorem cell_bound (a b : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct,
    ‖IBMPhysicalPointKernelIto.correctionLimit b Y-IBMPhysicalPointKernelIto.correctionLimit a Y‖^2 ≤
      2*‖IBMPhysicalCorrectedVariation.residual b Y-IBMPhysicalCorrectedVariation.residual a Y‖^2+
        2*‖dirac 0‖^2*(limitPath Y b-limitPath Y a)^2 := by
  filter_upwards [original_correction_actual a, original_correction_actual b] with Y ha hb
  let A := IBMPhysicalCorrectedVariation.residual b Y-IBMPhysicalCorrectedVariation.residual a Y
  let B : Kernel := (limitPath Y b-limitPath Y a) • dirac 0
  have he : IBMPhysicalPointKernelIto.correctionLimit b Y-
      IBMPhysicalPointKernelIto.correctionLimit a Y = A+B := by
    rw [ha, hb]
    dsimp only [A, B]
    module
  have hnorm := norm_add_le A B
  have hsq := pow_le_pow_left₀ (norm_nonneg (A+B)) hnorm 2
  have h : ‖A+B‖^2 ≤ 2*‖A‖^2+2*‖B‖^2 := by nlinarith [sq_nonneg (‖A‖-‖B‖)]
  have hB : ‖B‖^2 = (limitPath Y b-limitPath Y a)^2*‖dirac 0‖^2 := by
    dsimp only [B]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [he]
  change ‖A+B‖^2 ≤ 2*‖A‖^2+2*‖dirac 0‖^2*(limitPath Y b-limitPath Y a)^2
  nlinarith [hB]

def squares (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (n+1), ‖IBMPhysicalPointKernelIto.correctionLimit (uniformTime T n i.succ) Y-
    IBMPhysicalPointKernelIto.correctionLimit (uniformTime T n i.castSucc) Y‖^2

theorem squares_nonnegative (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) : 0 ≤ squares T n Y :=
  Finset.sum_nonneg fun i _hi => sq_nonneg _

theorem squares_integrable (T : ℝ≥0) (n : ℕ) : Integrable (squares T n) gaussianProduct :=
  integrable_finsetSum _ fun (i : Fin (n+1)) _hi =>
    ((Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (uniformTime T n i.succ))).sub
      (Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (uniformTime T n i.castSucc)))).norm.integrable_sq

theorem squares_bound (T : ℝ≥0) (n : ℕ) : ∀ᵐ Y ∂gaussianProduct,
    squares T n Y ≤ 2*IBMPhysicalCorrectedVariation.squares T n Y+
      (2*‖dirac 0‖^2)*BrownianLocalTimeSquares.squares T n Y := by
  have h := ae_all_iff.mpr fun i : Fin (n+1) =>
    cell_bound (uniformTime T n i.castSucc) (uniformTime T n i.succ)
  filter_upwards [h] with Y hY
  calc
    _ ≤ ∑ i : Fin (n+1), (2*‖IBMPhysicalCorrectedVariation.residual (uniformTime T n i.succ) Y-
        IBMPhysicalCorrectedVariation.residual (uniformTime T n i.castSucc) Y‖^2+
          (2*‖dirac 0‖^2)*(limitPath Y (uniformTime T n i.succ)-
            limitPath Y (uniformTime T n i.castSucc))^2) := Finset.sum_le_sum fun i _hi => hY i
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      IBMPhysicalCorrectedVariation.squares, BrownianLocalTimeSquares.squares,
      BrownianLocalTimeSquares.pathSquares]

theorem squares_mean_bound (T : ℝ≥0) (n : ℕ) :
    (∫ Y, squares T n Y ∂gaussianProduct) ≤
      2*(∫ Y, IBMPhysicalCorrectedVariation.squares T n Y ∂gaussianProduct)+
        (2*‖dirac 0‖^2)*(∫ Y, BrownianLocalTimeSquares.squares T n Y ∂gaussianProduct) := by
  calc
    _ ≤ ∫ Y, 2*IBMPhysicalCorrectedVariation.squares T n Y+
        (2*‖dirac 0‖^2)*BrownianLocalTimeSquares.squares T n Y ∂gaussianProduct :=
      integral_mono_ae (squares_integrable T n)
        (((IBMPhysicalCorrectedVariation.squares_integrable T n).const_mul 2).add
          ((BrownianLocalTimeSquares.squares_integrable T n).const_mul _)) (squares_bound T n)
    _ = _ := by rw [integral_add
      ((IBMPhysicalCorrectedVariation.squares_integrable T n).const_mul 2)
      ((BrownianLocalTimeSquares.squares_integrable T n).const_mul _),
      integral_const_mul, integral_const_mul]

theorem squares_mean_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ∫ Y, squares T n Y ∂gaussianProduct) atTop (nhds 0) := by
  apply squeeze_zero (fun n => integral_nonneg (squares_nonnegative T n))
    (fun n => squares_mean_bound T n)
  simpa only [mul_zero, zero_add] using
    ((IBMPhysicalCorrectedVariation.squares_mean_tendsto T).const_mul 2).add
      ((BrownianLocalTimeSquares.squares_mean_tendsto T).const_mul (2*‖dirac 0‖^2))

def squaresClass (T : ℝ≥0) (n : ℕ) : Lp ℝ 1 gaussianProduct :=
  (squares_integrable T n).toL1 (squares T n)

theorem squaresClass_ae (T : ℝ≥0) (n : ℕ) : squaresClass T n =ᵐ[gaussianProduct] squares T n :=
  (squares_integrable T n).coeFn_toL1

theorem squaresClass_tendsto (T : ℝ≥0) : Tendsto (squaresClass T) atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, squaresClass, L1.norm_of_fun_eq_integral_norm,
    Real.norm_of_nonneg (squares_nonnegative T _ _)] using squares_mean_tendsto T

end OperatorDerivativeRewrite.Foundation.IBMPhysicalOriginalVariation
