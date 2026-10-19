import Foundation.IBMPhysicalClockIto
import Foundation.IBMSchwartzPhysicalSlopeClock

/-! The actual convergent physical first-slope fields belong to the native
predictable H^-1 integral domain. Their stochastic integral values converge
strongly. The reflected chain rule identifying the WHOLE correction is separate. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalClockIntegral
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 IBMPhysicalClockIto
open IBMSchwartzPhysicalSlopeClock

def restriction (T : ℝ≥0) : Lp (H^{(-1 : ℝ)}(ℝ)) 2 timeProbability →L[ℂ]
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 (PredictableRealL2.horizonMeasure T gaussianProduct) :=
  LpToLpRestrictCLM _ H^{(-1 : ℝ)}(ℝ) ℂ timeProbability 2 (PredictableRealL2.horizon T)

def integrand (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : Domain T :=
  ⟨restriction T (field g a n T), (field_predictable g a n T).restrict.congr
    (LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T) (field g a n T)).symm⟩

def limitIntegrand (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : Domain T :=
  ⟨restriction T (limitField g a T), (limitField_predictable g a T).restrict.congr
    (LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T) (limitField g a T)).symm⟩

theorem integrand_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => integrand g a n T) atTop (𝓝 (limitIntegrand g a T)) := by
  apply tendsto_subtype_rng.mpr
  exact (restriction T).continuous.tendsto _ |>.comp (field_tendsto g a T)

def integralValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct := integral T (integrand g a n T)

def limitIntegralValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct := integral T (limitIntegrand g a T)

theorem integralValue_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => integralValue g a n T) atTop (𝓝 (limitIntegralValue g a T)) :=
  (integral_isometry T).continuous.tendsto _ |>.comp (integrand_tendsto g a T)

theorem integralValue_difference_norm (g : SchwartzMap ℝ ℝ) (a : ℝ) (n m : ℕ) (T : ℝ≥0) :
    ‖integralValue g a n T-integralValue g a m T‖ =
      ‖integrand g a n T-integrand g a m T‖ := by
  exact (dist_eq_norm _ _).symm.trans
    (((integral_isometry T).dist_eq (integrand g a n T) (integrand g a m T)).trans
      (dist_eq_norm _ _))

end OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalClockIntegral
