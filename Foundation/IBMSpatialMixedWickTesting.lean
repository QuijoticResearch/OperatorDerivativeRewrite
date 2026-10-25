import Foundation.IBMSpatialSignedReconstruction
import Foundation.IBMRawGridMixedObservable

/-! Physical mixed Gaussian probes of the original source telescope. The
spatial normalization is unhalved; no observable projection is discarded. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialMixedWickTesting
open InfiniteGaussian GaussianTimeProcess IBMPhysicalWickTestDomain
open IBMSpatialBoundedTestOperator IBMSpatialKernelTesting IBMSpatialIncrementKernel
open IBMSpatialLipschitzTestLimit IBMSpatialCompletedTestLimit IBMRawGridSecondChaos

def mixedTest (g h : SchwartzMap ℝ ℝ) : Tests :=
  ((SchwartzMap.derivCLM ℝ ℝ g).toBoundedContinuousFunction.compContinuous
    ⟨Prod.fst,continuous_fst⟩)*
  ((SchwartzMap.derivCLM ℝ ℝ h).toBoundedContinuousFunction.compContinuous
    ⟨Prod.snd,continuous_snd⟩)

theorem mixedTest_apply (g h : SchwartzMap ℝ ℝ) (z : ℝ × ℝ) :
    mixedTest g h z = deriv g z.1*deriv h z.2 := rfl

theorem mixedTest_lipschitz (g h : SchwartzMap ℝ ℝ) :
    LipschitzWith (secondBound g*firstBound h+firstBound g*secondBound h) (mixedTest g h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hg := (GaussianSmoothQuadraticVariation.derivative_lipschitz g (g.smooth 2)
    (secondBound g) (second_derivative_bound g)).norm_sub_le x.1 y.1
  have hh := (GaussianSmoothQuadraticVariation.derivative_lipschitz h (h.smooth 2)
    (secondBound h) (second_derivative_bound h)).norm_sub_le x.2 y.2
  have hd1 : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd2 : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hgb : ‖deriv g y.1‖ ≤ (firstBound g:ℝ) := first_derivative_bound g y.1
  have hhb : ‖deriv h x.2‖ ≤ (firstBound h:ℝ) := first_derivative_bound h x.2
  rw [dist_eq_norm,mixedTest_apply,mixedTest_apply]
  have he : deriv g x.1*deriv h x.2-deriv g y.1*deriv h y.2 =
      (deriv g x.1-deriv g y.1)*deriv h x.2+
        deriv g y.1*(deriv h x.2-deriv h y.2) := by ring
  rw [he]
  calc
    _ ≤ ‖(deriv g x.1-deriv g y.1)*deriv h x.2‖+
        ‖deriv g y.1*(deriv h x.2-deriv h y.2)‖ := norm_add_le _ _
    _ ≤ ((secondBound g:ℝ)*dist x y)*(firstBound h:ℝ)+
        (firstBound g:ℝ)*((secondBound h:ℝ)*dist x y) := by
      simp only [norm_mul]
      exact add_le_add
        (mul_le_mul (hg.trans (mul_le_mul_of_nonneg_left hd1 (secondBound g).coe_nonneg))
          hhb (norm_nonneg _) (by positivity))
        (mul_le_mul hgb (hh.trans (mul_le_mul_of_nonneg_left hd2 (secondBound h).coe_nonneg))
          (norm_nonneg _) (firstBound g).coe_nonneg)
    _ = _ := by push_cast; ring

def mixedCore (g h : SchwartzMap ℝ ℝ) : Core := ⟨mixedTest g h,_,mixedTest_lipschitz g h⟩

theorem cell_mixed (g h : SchwartzMap ℝ ℝ) (x y : ℝ) :
    cellPair (mixedTest g h) x y = (g y-g x)*(h y-h x) := by
  have he : (fun z => rectangle (cellSet x y) z*mixedTest g h z) =
      (cellSet x y ×ˢ cellSet x y).indicator (fun z => deriv g z.1*deriv h z.2) := by
    funext z
    by_cases hz : z ∈ cellSet x y ×ˢ cellSet x y
    · simp only [rectangle,indicator_of_mem hz,one_mul,mixedTest_apply]
    · simp only [rectangle,indicator_of_notMem hz,zero_mul]
  unfold cellPair
  rw [he]
  change (∫ z, (cellSet x y ×ˢ cellSet x y).indicator
    (fun z => deriv g z.1*deriv h z.2) z ∂(volume.prod volume)) = _
  rw [integral_indicator (show MeasurableSet (cellSet x y ×ˢ cellSet x y) from
    measurableSet_Ioc.prod measurableSet_Ioc),setIntegral_prod_mul]
  have hp (f : SchwartzMap ℝ ℝ) (a b : ℝ) :
      (∫ t in a..b, deriv f t) = f b-f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => f.hasDerivAt t)
      ((SchwartzMap.derivCLM ℝ ℝ f).continuous.intervalIntegrable _ _)
  rcases le_total x y with hxy | hyx
  · simp only [cellSet,min_eq_left hxy,max_eq_right hxy]
    rw [← intervalIntegral.integral_of_le hxy,← intervalIntegral.integral_of_le hxy,hp,hp]
  · simp only [cellSet,min_eq_right hyx,max_eq_left hyx]
    rw [← intervalIntegral.integral_of_le hyx,← intervalIntegral.integral_of_le hyx,hp,hp]
    ring

def sourceAction (g h : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  (innerSL ℝ (IBMSchwartzSourceContinuity.rawProduct (testDirection g) (testDirection h))).compLpL
    2 gaussianProduct (sourceGrid (T/(N+1)) (N+1))

theorem sourceAction_actual (g h : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) :
    sourceAction g h T N =ᵐ[gaussianProduct] fun Y =>
      inner ℝ (sourceSum (clockCurve (T/(N+1)) Y) (N+1))
        (IBMSchwartzSourceContinuity.rawProduct (testDirection g) (testDirection h)) := by
  filter_upwards [(innerSL ℝ (IBMSchwartzSourceContinuity.rawProduct (testDirection g)
    (testDirection h))).coeFn_compLpL (sourceGrid (T/(N+1)) (N+1)),
    sourceGrid_ae (T/(N+1)) (N+1)] with Y ha hs
  change sourceAction g h T N Y = _ at ha
  rw [ha,hs]
  change inner ℝ (IBMSchwartzSourceContinuity.rawProduct (testDirection g) (testDirection h)) _ = _
  exact real_inner_comm _ _

private theorem time_grid (T : ℝ≥0) (N : ℕ) (i : Fin (N+2)) :
    GaussianBrownianQuadraticVariation.uniformTime T N i =
      IBMUniformClockGridEnergy.grid (T/(N+1)) i.val := by
  unfold GaussianBrownianQuadraticVariation.uniformTime IBMUniformClockGridEnergy.grid
  push_cast
  ring

theorem source_signed_identity (g h : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) :
    IBMClippedClockStrongLimit.clockL1 (sourceAction g h T N) =
      IBMSpatialSignedReconstruction.finiteOperator T N (mixedCore g h:Completed) := by
  have ht : IBMUniformClockGridEnergy.grid (T/(N+1)) (N+1) = T := by
    unfold IBMUniformClockGridEnergy.grid
    have hp : (N+1:ℝ≥0) ≠ 0 := by positivity
    simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ T hp
  have hz : IBMUniformClockGridEnergy.grid (T/(N+1)) 0 = 0 := by
    simp [IBMUniformClockGridEnergy.grid]
  apply Lp.ext
  filter_upwards [IBMClippedClockStrongLimit.clockL1_actual (sourceAction g h T N),
    sourceAction_actual g h T N,
    IBMSpatialSignedReconstruction.finite_actual T N (mixedCore g h:Completed),
    process_zero_ae] with Y hl ha hs h0
  rw [hl,ha,hs,realize_coe]
  change _ = cellPair (mixedTest g h) 0 |process T Y|-finiteValue (mixedTest g h) T N Y
  rw [IBMRawGridMixedObservable.source_mixed_test,cell_mixed]
  simp only [clockCurve,clock_primitive,ht,hz,h0,abs_zero,sub_self,zero_mul,sub_zero]
  congr 1
  unfold finiteValue
  simp only [cell_mixed,time_grid,Fin.val_succ,Fin.val_castSucc]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (g |process (IBMUniformClockGridEnergy.grid (T/(N+1)) (i+1)) Y|-
      g |process (IBMUniformClockGridEnergy.grid (T/(N+1)) i) Y|)*
    (h |process (IBMUniformClockGridEnergy.grid (T/(N+1)) (i+1)) Y|-
      h |process (IBMUniformClockGridEnergy.grid (T/(N+1)) i) Y|)) (N+1)]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem source_signed_tendsto (g h : SchwartzMap ℝ ℝ) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => IBMClippedClockStrongLimit.clockL1 (sourceAction g h T N)) atTop
      (𝓝 (IBMSpatialSignedReconstruction.limitOperator T hT (mixedCore g h:Completed))) := by
  have ht := IBMSpatialSignedReconstruction.signed_tendsto T hT (mixedCore g h:Completed)
  exact ht.congr' (Eventually.of_forall fun N => (source_signed_identity g h T N).symm)

theorem endpoint_product_actual (g h : SchwartzMap ℝ ℝ) (T : ℝ≥0) :
    IBMSpatialEndpointOperator.value (mixedTest g h) T =ᵐ[gaussianProduct]
      fun Y => (g |process T Y|-g 0)*(h |process T Y|-h 0) := by
  filter_upwards [IBMSpatialEndpointOperator.value_actual (mixedTest g h) T] with Y hY
  exact hY.trans (cell_mixed g h 0 |process T Y|)

theorem limit_explicit (g h : SchwartzMap ℝ ℝ) (T : ℝ≥0) (hT : 0 < T) :
    IBMSpatialSignedReconstruction.limitOperator T hT (mixedCore g h:Completed) =
      IBMSpatialEndpointOperator.value (mixedTest g h) T-
        IBMSpatialKernelOccupation.occupation (mixedTest g h) (mixedTest_lipschitz g h) T := by
  have ht := IBMSpatialKernelOccupation.action_tendsto (mixedTest g h)
    (mixedTest_lipschitz g h) ‖mixedTest g h‖ (mixedTest g h).norm_coe_le_norm T hT
  have he : Tendsto (fun N => IBMSpatialLipschitzTestLimit.finiteOperator T N (mixedCore g h))
      atTop (𝓝 (IBMSpatialKernelOccupation.occupation (mixedTest g h)
        (mixedTest_lipschitz g h) T)) :=
    ht.congr' (Eventually.of_forall fun N =>
      (value_old_action (mixedTest g h) (mixedTest_lipschitz g h) T N).symm)
  have hl := tendsto_nhds_unique (core_tendsto T hT (mixedCore g h)) he
  change IBMSpatialSignedReconstruction.endpoint T (mixedCore g h:Completed)-
    IBMSpatialCompletedTestLimit.limitOperator T hT (mixedCore g h:Completed) = _
  rw [limit_coe,IBMSpatialLipschitzTestLimit.limit_apply,hl]
  congr 1
  change IBMSpatialEndpointOperator.value (realize (mixedCore g h:Completed)) T = _
  rw [realize_coe]
  rfl

theorem source_tendsto_explicit (g h : SchwartzMap ℝ ℝ) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => IBMClippedClockStrongLimit.clockL1 (sourceAction g h T N)) atTop
      (𝓝 (IBMSpatialEndpointOperator.value (mixedTest g h) T-
        IBMSpatialKernelOccupation.occupation (mixedTest g h) (mixedTest_lipschitz g h) T)) := by
  rw [← limit_explicit g h T hT]
  exact source_signed_tendsto g h T hT

end OperatorDerivativeRewrite.Foundation.IBMSpatialMixedWickTesting

