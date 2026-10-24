import Foundation.IBMPhysicalCorrectedRunning

/-! The ACTUAL corrected physical residual has squared increment sums
converging strongly in L1 to zero on the existing uniform clock grids.
This is not a bounded-variation assertion or an unprojected IBM formula. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectedVariation
open InfiniteGaussian IBMConstructedSources GaussianBrownianQuadraticVariation
open IBMPhysicalWeakWiener IBMPhysicalReflectedPrimitive IBMPhysicalCorrectedRunning
open IBMPhysicalTaylorMean IBMPhysicalCellErrorRate
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul
attribute [local irreducible] IBMPhysicalReflectedPrimitive.corrected
  IBMPhysicalReflectedPrimitive.slope IBMConstructedSources.clockPath

def value (t : ℝ≥0) (Y : SampleSpace) : Kernel := corrected (clockPath Y t)

theorem value_stronglyMeasurable (t : ℝ≥0) : StronglyMeasurable (value t) :=
  corrected_C1.continuous.stronglyMeasurable.comp_measurable (clock_measurable t)

def residual (t : ℝ≥0) (Y : SampleSpace) : Kernel := value t Y-running t Y

theorem residual_stronglyMeasurable (t : ℝ≥0) : StronglyMeasurable (residual t) :=
  (value_stronglyMeasurable t).sub (Lp.stronglyMeasurable (running t))

theorem value_actual_ae (t : ℝ≥0) : value t =ᵐ[gaussianProduct] fun Y =>
    IBMPhysicalPointKernelIto.point t Y-
      |clockPath Y t| • IBMPhysicalDirac.dirac 0 := by
  filter_upwards [IBMPhysicalNegativeEmbedding.embedding.coeFn_compLpL
    (IBMPhysicalNoiseClock.sourceKernel t), IBMPhysicalNoiseClock.sourceKernel_ae t]
    with Y he hk
  change IBMPhysicalPointKernelIto.point t Y =
    IBMPhysicalNegativeEmbedding.embedding (IBMPhysicalNoiseClock.sourceKernel t Y) at he
  rw [he, hk]
  change corrected (clockPath Y t) = _
  rw [IBMPhysicalReflectedPrimitive.corrected, IBMPhysicalPrimitiveDerivative.primitive]

theorem value_memLp (t : ℝ≥0) : MemLp (value t) 2 gaussianProduct := by
  let C : ℝ →L[ℝ] Kernel := (ContinuousLinearMap.id ℝ ℝ).smulRight (IBMPhysicalDirac.dirac 0)
  have hC := C.comp_memLp' (Lp.memLp (GaussianTimeProcess.wienerL2 t)).norm
  apply ((Lp.memLp (IBMPhysicalPointKernelIto.point t)).sub hC).ae_eq
  filter_upwards [value_actual_ae t, clockPath_coordinate_ae t] with Y hv hc
  change IBMPhysicalPointKernelIto.point t Y-C ‖GaussianTimeProcess.wienerL2 t Y‖ = value t Y
  rw [hv, hc]
  rfl

theorem residual_memLp (t : ℝ≥0) : MemLp (residual t) 2 gaussianProduct :=
  (value_memLp t).sub (Lp.memLp (running t))

def residualClass (t : ℝ≥0) : Lp Kernel 2 gaussianProduct := (residual_memLp t).toLp _

theorem residualClass_ae (t : ℝ≥0) : residualClass t =ᵐ[gaussianProduct] residual t :=
  (residual_memLp t).coeFn_toLp

theorem cell_bound (a b : ℝ≥0) (hab : a ≤ b) : ∀ᵐ Y ∂gaussianProduct,
    ‖residual b Y-residual a Y‖^2 ≤
      2*remainder a b Y+2*‖IBMPhysicalCellSlope.integral a b Y‖^2 := by
  filter_upwards [error_integral_actual a b hab] with Y he
  let A : Kernel := corrected (clockPath Y b)-corrected (clockPath Y a)-
    (clockPath Y b-clockPath Y a) • slope (clockPath Y a)
  let B : Kernel := IBMPhysicalCellSlope.integral a b Y
  have hsplit : residual b Y-residual a Y = A-B := by
    dsimp only [residual, value, A, B]
    rw [he]
    module
  have hn := norm_sub_le A B
  have hsq := pow_le_pow_left₀ (norm_nonneg (A-B)) hn 2
  rw [hsplit]
  change ‖A-B‖^2 ≤ 2*‖A‖^2+2*‖B‖^2
  nlinarith [sq_nonneg (‖A‖-‖B‖)]

def squares (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (n+1), ‖residual (uniformTime T n i.succ) Y-
    residual (uniformTime T n i.castSucc) Y‖^2

theorem squares_nonnegative (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) :
    0 ≤ squares T n Y := Finset.sum_nonneg fun i _hi => sq_nonneg _

theorem squares_stronglyMeasurable (T : ℝ≥0) (n : ℕ) : StronglyMeasurable (squares T n) := by
  exact Finset.stronglyMeasurable_fun_sum Finset.univ fun (i : Fin (n+1)) _hi =>
    ((residual_stronglyMeasurable (uniformTime T n i.succ)).sub
      (residual_stronglyMeasurable (uniformTime T n i.castSucc))).norm.pow 2

theorem squares_bound (T : ℝ≥0) (n : ℕ) : ∀ᵐ Y ∂gaussianProduct,
    squares T n Y ≤ 2*remainderSum T n Y+2*cellSquares T n Y := by
  have h := ae_all_iff.mpr fun i : Fin (n+1) => cell_bound
    (uniformTime T n i.castSucc) (uniformTime T n i.succ)
    (uniformTime_monotone T n (Fin.castSucc_le_succ i))
  filter_upwards [h] with Y hY
  calc
    _ ≤ ∑ i : Fin (n+1), (2*remainder (uniformTime T n i.castSucc)
        (uniformTime T n i.succ) Y+2*‖IBMPhysicalCellSlope.integral
          (uniformTime T n i.castSucc) (uniformTime T n i.succ) Y‖^2) :=
      Finset.sum_le_sum fun i _hi => hY i
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, remainderSum, cellSquares]

theorem squares_integrable (T : ℝ≥0) (n : ℕ) : Integrable (squares T n) gaussianProduct := by
  apply (((remainderSum_integrable T n).const_mul 2).add
    ((cellSquares_integrable T n).const_mul 2)).mono'
    (squares_stronglyMeasurable T n).aestronglyMeasurable
  filter_upwards [squares_bound T n] with Y hY
  rw [Real.norm_of_nonneg (squares_nonnegative T n Y)]
  exact hY

theorem squares_mean_bound (T : ℝ≥0) (n : ℕ) :
    (∫ Y, squares T n Y ∂gaussianProduct) ≤
      2*(∫ Y, remainderSum T n Y ∂gaussianProduct)+
        2*(∫ Y, cellSquares T n Y ∂gaussianProduct) := by
  calc
    _ ≤ ∫ Y, 2*remainderSum T n Y+2*cellSquares T n Y ∂gaussianProduct :=
      integral_mono_ae (squares_integrable T n)
        (((remainderSum_integrable T n).const_mul 2).add
          ((cellSquares_integrable T n).const_mul 2)) (squares_bound T n)
    _ = _ := by rw [integral_add ((remainderSum_integrable T n).const_mul 2)
      ((cellSquares_integrable T n).const_mul 2), integral_const_mul, integral_const_mul]

theorem squares_mean_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ∫ Y, squares T n Y ∂gaussianProduct) atTop (nhds 0) := by
  apply squeeze_zero (fun n => integral_nonneg (squares_nonnegative T n))
    (fun n => squares_mean_bound T n)
  simpa only [mul_zero, zero_add] using
    ((remainderSum_mean_tendsto T).const_mul 2).add ((cellSquares_mean_tendsto T).const_mul 2)

def squaresClass (T : ℝ≥0) (n : ℕ) : Lp ℝ 1 gaussianProduct :=
  (squares_integrable T n).toL1 (squares T n)

theorem squaresClass_ae (T : ℝ≥0) (n : ℕ) :
    squaresClass T n =ᵐ[gaussianProduct] squares T n :=
  (squares_integrable T n).coeFn_toL1

theorem squaresClass_tendsto (T : ℝ≥0) :
    Tendsto (squaresClass T) atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, squaresClass, L1.norm_of_fun_eq_integral_norm,
    Real.norm_of_nonneg (squares_nonnegative T _ _)] using squares_mean_tendsto T

end OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectedVariation
