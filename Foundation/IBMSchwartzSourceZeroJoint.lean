import Foundation.IBMSchwartzWholeSourceMean
import Foundation.ProductL2Flip

/-! Native source-zero/full-clock closure of the literal whole correction.
The old clock lift is explicitly swapped to (clock, source) coordinates. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzSourceZeroJoint
open InfiniteGaussian GaussianNumberSectors IBMSchwartzWholeSourceMean IBMSchwartzTimeProjection
open IBMSchwartzJointRealization IBMSchwartzBochnerDomain IBMSceneryAveragedCorrectionLimit
open IBMQuarticJointRealization (jointMeasure jointSourceSector)
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def clockLift : GaussianL2 →ₗᵢ[ℝ] Lp ℝ 2 jointMeasure :=
  (ProductL2Curry.swap gaussianProduct gaussianProduct).comp IBMClockConditionalCorrection.clockLift

theorem clockLift_coeFn (f : GaussianL2) :
    clockLift f =ᵐ[jointMeasure] fun p => f p.1 := by
  have hl := measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (IBMClockConditionalCorrection.clockLift_coeFn f)
  change ProductL2Curry.swap gaussianProduct gaussianProduct
    (IBMClockConditionalCorrection.clockLift f) =ᵐ[jointMeasure] _
  filter_upwards [ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct
    (IBMClockConditionalCorrection.clockLift f), hl] with p hs hh
  rw [hs]
  exact hh

variable (g : SchwartzMap ℝ ℝ) (a : ℝ)

theorem lifted_averaged_coeFn (n : ℕ) (T : ℝ≥0) :
    clockLift ((1/2 : ℝ) • averagedClass g a n T) =ᵐ[jointMeasure]
      fun p => (1/2 : ℝ)*averagedPath g a n T p.1 := by
  have hm := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae
    (averagedClass_coeFn g a n T)
  have hs := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae
    (Lp.coeFn_smul (1/2 : ℝ) (averagedClass g a n T))
  filter_upwards [clockLift_coeFn ((1/2 : ℝ) • averagedClass g a n T), hm, hs] with p hl hm hs
  rw [hl, hs, Pi.smul_apply, smul_eq_mul, hm]

theorem zero_sections (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ ωY ∂gaussianProduct, projection 0 (wholeCorrection g a n T ωY) =ᵐ[gaussianProduct]
      fun ωX => jointSourceSector 0 (jointClass g a n T) (ωY,ωX) := by
  simp only [jointSourceSector, jointClass, LinearIsometryEquiv.apply_symm_apply]
  have he := ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct
    (((projection 0).compLpL 2 gaussianProduct) (wholeClass g a n T))
  have hp := (projection 0).coeFn_compLpL (wholeClass g a n T)
  filter_upwards [he, hp, wholeClass_coeFn g a n T] with ωY hy hp hw
  rw [hp, hw] at hy
  exact hy

/-- This is the complete source-zero component, retaining every clock
sector, and includes the proved vanishing origin mean. -/
theorem source_zero_eq_clockLift (n : ℕ) (T : ℝ≥0) :
    jointSourceSector 0 (jointClass g a n T) = clockLift ((1/2 : ℝ) • averagedClass g a n T) := by
  apply Lp.ext
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun
      (Lp.stronglyMeasurable (jointSourceSector 0 (jointClass g a n T))).measurable
      (Lp.stronglyMeasurable (clockLift ((1/2 : ℝ) • averagedClass g a n T))).measurable)).mpr
  have hl := ae_ae_of_ae_prod (lifted_averaged_coeFn g a n T)
  filter_upwards [zero_sections g a n T, hl] with ωY hz hl
  rw [whole_projection_zero] at hz
  filter_upwards [hz, hl, Lp.coeFn_smul ((1/2 : ℝ)*averagedPath g a n T ωY) gaussianOne,
    gaussianOne_coeFn] with ωX hz hl hs ho
  rw [hs, Pi.smul_apply, ho, smul_eq_mul, mul_one] at hz
  exact hz.symm.trans hl.symm

theorem literal_source_zero_eq (n : ℕ) (T : ℝ≥0) :
    jointSourceSector 0 (IBMSchwartzLiteralJoint.literalClass g a n T) =
      clockLift ((1/2 : ℝ) • averagedClass g a n T) := by
  rw [IBMSchwartzLiteralJoint.literalClass_eq_joint, source_zero_eq_clockLift]

/-- Strong native product-L2 convergence, simultaneously retaining all
clock sectors in the whole source-zero component. -/
theorem literal_source_zero_tendsto (T : ℝ≥0) :
    Tendsto (fun n => jointSourceSector 0 (IBMSchwartzLiteralJoint.literalClass g a n T)) atTop
      (𝓝 (clockLift ((1/2 : ℝ) • averagedLimit g a T))) := by
  simp_rw [literal_source_zero_eq]
  exact clockLift.continuous.tendsto _ |>.comp ((averagedClass_tendsto g a T).const_smul (1/2 : ℝ))

end OperatorDerivativeRewrite.Foundation.IBMSchwartzSourceZeroJoint
