import Foundation.IBMFoldedWeightedLoss

/-! Actual physical quadratic-Wick source tests for EVERY Schwartz primitive.
Strong clock L1 convergence requires no parity or artificial derivative at zero. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMAllSchwartzWickLimit
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMPhysicalWickTestDomain IBMClippedClockStrongLimit IBMUniformClockGridEnergy
open IBMFoldedWeightedLoss

def weighted (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  GaussianLipschitzQuadraticVariation.error (weight_lipschitz g) T N+
    GaussianSmoothIto.driftSum (weight_lipschitz g) T N

def drift (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) : GaussianL2 :=
  ∫ t in 0..(T:ℝ), GaussianLipschitzIntegrands.valueL2 (weight_lipschitz g) t.toNNReal

theorem weighted_actual (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) :
    weighted g T N =ᵐ[gaussianProduct] fun Y => ∑ i : Fin (N+1),
      weight g (process (uniformTime T N i.castSucc) Y)*
        (process (uniformTime T N i.succ) Y-process (uniformTime T N i.castSucc) Y)^2 := by
  filter_upwards [Lp.coeFn_add (GaussianLipschitzQuadraticVariation.error (weight_lipschitz g) T N)
    (GaussianSmoothIto.driftSum (weight_lipschitz g) T N),
    GaussianLipschitzQuadraticVariation.error_coeFn (weight_lipschitz g) T N,
    GaussianSmoothIto.driftSum_coeFn (weight_lipschitz g) T N] with Y ha he hd
  change weighted g T N Y = _ at ha
  rw [ha,Pi.add_apply,he,hd,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem weighted_tendsto (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) :
    Tendsto (weighted g T) atTop (𝓝 (drift g T)) := by
  have h := (GaussianLipschitzQuadraticVariation.error_tendsto (weight_lipschitz g) T).add
    (GaussianLipschitzIntegrands.drift_sum_tendsto (weight_lipschitz g) T)
  unfold weighted drift
  simpa only [zero_add,GaussianSmoothIto.driftSum] using h

def quadratic (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  clockL1 (IBMFoldedSmoothQuadraticError.errorSum g (g.smooth 2) (firstBound g) (secondBound g)
    (first_derivative_bound g) (second_derivative_bound g) T N+weighted g T N)-lossClass g T N

theorem quadratic_actual (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) :
    quadratic g T N =ᵐ[gaussianProduct] fun Y => ∑ i : Fin (N+1),
      (g |process (uniformTime T N i.succ) Y|-g |process (uniformTime T N i.castSucc) Y|)^2 := by
  let e := IBMFoldedSmoothQuadraticError.errorSum g (g.smooth 2) (firstBound g) (secondBound g)
    (first_derivative_bound g) (second_derivative_bound g) T N
  filter_upwards [Lp.coeFn_sub (clockL1 (e+weighted g T N)) (lossClass g T N),
    clockL1_actual (e+weighted g T N),Lp.coeFn_add e (weighted g T N),
    IBMFoldedSmoothQuadraticError.errorSum_actual g (g.smooth 2) (firstBound g) (secondBound g)
      (first_derivative_bound g) (second_derivative_bound g) T N,
    weighted_actual g T N,lossClass_actual g T N] with Y hs hl ha he hw hlos
  change quadratic g T N Y = _ at hs
  rw [hs,Pi.sub_apply,hl,ha,Pi.add_apply,he,hw,hlos]
  unfold value
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold GaussianSmoothQuadraticVariation.quadraticError weight IBMFoldedClockQuadraticVariation.loss
  ring

theorem quadratic_tendsto (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (quadratic g T) atTop (𝓝 (clockL1 (drift g T))) := by
  have he := (IBMFoldedSmoothQuadraticError.errorSum_tendsto g (g.smooth 2) (firstBound g) (secondBound g)
    (first_derivative_bound g) (second_derivative_bound g) T).add (weighted_tendsto g T)
  simp only [zero_add] at he
  have h := (clockL1_tendsto _ _ he).sub (lossClass_tendsto g T hT)
  unfold quadratic
  simpa only [sub_zero] using h

end OperatorDerivativeRewrite.Foundation.IBMAllSchwartzWickLimit
