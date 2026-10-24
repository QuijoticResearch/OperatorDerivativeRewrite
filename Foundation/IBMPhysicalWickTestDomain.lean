import Foundation.IBMPhysicalNoiseRealization
import Foundation.IBMRawGridSecondChaos
import Foundation.GaussianSmoothQuadraticVariation

/-! Actual physical quadratic-Wick test directions for the IBM source kernel.
The primitive relation is proved on the ORIGINAL scenery isometry. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalWickTestDomain
open InfiniteGaussian GaussianTimeHilbert IBMPhysicalNoiseVectors IBMPhysicalNoiseRealization
open IBMRawStepSources IBMRawGridSecondChaos IBMFullSchwartzTerminal

def physicalTest (g : SchwartzMap ℝ ℝ) : TimeHilbert :=
  (SchwartzMap.derivCLM ℝ ℝ g).toLp 2 volume

def testDirection (g : SchwartzMap ℝ ℝ) : CoefficientSpace := physicalToCoefficient (physicalTest g)

theorem physical_primitive (g : SchwartzMap ℝ ℝ) (r : ℝ) :
    (∫ x in 0..r, physicalTest g x) = g r-g 0 := by
  calc
    _ = ∫ x in 0..r, SchwartzMap.derivCLM ℝ ℝ g x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(SchwartzMap.derivCLM ℝ ℝ g).coeFn_toLp 2 volume] with x hx
      exact fun _ => hx
    _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => by simpa only [SchwartzMap.derivCLM_apply] using g.hasDerivAt x)
      ((SchwartzMap.derivCLM ℝ ℝ g).continuous.intervalIntegrable _ _)

theorem source_primitive (g : SchwartzMap ℝ ℝ) (r : ℝ) :
    inner ℝ (IBMSineSourceField.direction r) (testDirection g) = g r-g 0 := by
  have he : IBMSineSourceField.direction r = physicalToCoefficient (vector r) := by
    apply firstChaosEmbedding.injective
    rw [physicalToCoefficient_vector,base_embedding]
    rfl
  rw [he]
  change inner ℝ (physicalToCoefficient (vector r)) (physicalToCoefficient (physicalTest g)) = _
  rw [physicalToCoefficient.inner_map_map, vector_inner_integral, physical_primitive]

theorem clock_primitive (g : SchwartzMap ℝ ℝ) (t : ℝ≥0) (Y : SampleSpace) :
    inner ℝ (clockDirection t Y) (testDirection g) =
      g |GaussianTimeProcess.process t Y|-g 0 := source_primitive g _

theorem even_clock_primitive (g : SchwartzMap ℝ ℝ) (hg : ∀ x, g (-x)=g x)
    (t : ℝ≥0) (Y : SampleSpace) :
    inner ℝ (clockDirection t Y) (testDirection g) = g (GaussianTimeProcess.process t Y)-g 0 := by
  rw [clock_primitive]
  congr 1
  rcases le_total 0 (GaussianTimeProcess.process t Y) with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,hg]

def firstBound (g : SchwartzMap ℝ ℝ) : ℝ≥0 :=
  Real.toNNReal (SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ g))
def secondBound (g : SchwartzMap ℝ ℝ) : ℝ≥0 :=
  firstBound (SchwartzMap.derivCLM ℝ ℝ g)

theorem first_derivative_bound (g : SchwartzMap ℝ ℝ) (x : ℝ) : ‖deriv g x‖₊ ≤ firstBound g := by
  apply NNReal.coe_le_coe.mp
  change ‖deriv g x‖ ≤ ((firstBound g:ℝ≥0):ℝ)
  unfold firstBound
  rw [Real.coe_toNNReal']
  have hb : ‖deriv g x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ g) := by
    simpa only [SchwartzMap.derivCLM_apply] using
      IBMBoundaryResidualLimit.schwartz_bound (SchwartzMap.derivCLM ℝ ℝ g) x
  exact hb.trans (le_max_left _ _)

theorem second_derivative_bound (g : SchwartzMap ℝ ℝ) (x : ℝ) :
    ‖deriv (deriv g) x‖₊ ≤ secondBound g := by
  have he : (SchwartzMap.derivCLM ℝ ℝ g : ℝ → ℝ) = deriv g := by
    funext x
    rfl
  simpa only [secondBound,he] using first_derivative_bound (SchwartzMap.derivCLM ℝ ℝ g) x

end OperatorDerivativeRewrite.Foundation.IBMPhysicalWickTestDomain
