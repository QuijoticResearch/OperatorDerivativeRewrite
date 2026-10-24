import Foundation.IBMSchwartzWeakWienerClosure
import Foundation.IBMClockPhysicalOccupation
import Foundation.MultiplierCore

/-! The ACTUAL signed spatial clock slope converges in the physical Wiener
test dual. This is the original native slope, not a new residual. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalPointSlope
open InfiniteGaussian IBMFirstSourceClockGraph IBMPhysicalWeakWiener
open IBMSchwartzWeakWienerClosure IBMClockPhysicalOccupation
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

def clockSign (t : ℝ≥0) (Y : SampleSpace) : ℝ :=
  BrownianSignIntegral.signum (IBMConstructedSources.clockPath Y t)

theorem clockSign_memLp (t : ℝ≥0) : MemLp (clockSign t) ∞ gaussianProduct := by
  have hm : Measurable (fun Y : SampleSpace => IBMConstructedSources.clockPath Y t) := by
    have h := BrownianClockWeightedEnergy.sigma_measurable.comp
      (show Measurable (fun Y : SampleSpace => ((t : ℝ),Y)) from
        measurable_const.prodMk measurable_id)
    simpa only [Function.comp_def, BrownianClockWeightedEnergy.sigma,
      Real.toNNReal_coe] using h
  exact MemLp.of_bound
    (BrownianSignIntegral.signum_measurable.comp hm).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun Y => BrownianSignIntegral.signum_bound _)

def signMultiplier (t : ℝ≥0) : Lp Kernel 2 gaussianProduct →L[ℝ]
    Lp Kernel 2 gaussianProduct := boundedMultiplier (clockSign t) (clockSign_memLp t)

def signedDirac (t : ℝ≥0) : Lp Kernel 2 gaussianProduct :=
  signMultiplier t (IBMPhysicalDirac.diracClass t)

def slopeLimit (t : ℝ≥0) := weakField (signedDirac t)

theorem signedDirac_ae (t : ℝ≥0) : signedDirac t =ᵐ[gaussianProduct] fun Y =>
    clockSign t Y • IBMPhysicalDirac.dirac |IBMConstructedSources.clockPath Y t| := by
  filter_upwards [boundedMultiplier_coeFn (clockSign t) (clockSign_memLp t)
    (IBMPhysicalDirac.diracClass t), IBMPhysicalDirac.diracClass_ae t] with Y hm hd
  change signedDirac t Y = _ at hm
  rw [hm, hd]
  rfl

theorem slopeLimit_ae (t : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct, ∀ L : Tests,
    slopeLimit t Y L = clockSign t Y *
      L (IBMPhysicalDirac.dirac |IBMConstructedSources.clockPath Y t|) := by
  filter_upwards [integral.coeFn_compLpL (signedDirac t), signedDirac_ae t] with Y hi hd
  intro L
  change slopeLimit t Y = integral (signedDirac t Y) at hi
  rw [hi, hd, integral_apply, map_smul, smul_eq_mul]

theorem slope_pairing_integral (t : ℝ≥0) (L : Tests) (ζ : GaussianL2) :
    inner ℝ (evaluate L (slopeLimit t)) ζ =
      ∫ Y, (clockSign t Y *
        L (IBMPhysicalDirac.dirac |IBMConstructedSources.clockPath Y t|)) * ζ Y
          ∂gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.apply ℝ ℝ L).coeFn_compLpL (slopeLimit t),
    slopeLimit_ae t] with Y he hs
  change evaluate L (slopeLimit t) Y = slopeLimit t Y L at he
  rw [he, hs L, Real.inner_apply]

theorem native_kernel_eq (n : ℕ) (t : ℝ≥0) :
    IBMPhysicalNegativeEmbedding.embedding.compLpL 2 gaussianProduct
      (recover (signedSource n t)) = signMultiplier t (IBMPhysicalDirac.mollifiedDirac n t) := by
  apply Lp.ext
  filter_upwards [IBMPhysicalNegativeEmbedding.embedding.coeFn_compLpL
      (recover (signedSource n t)), recovered_signedSource_ae n t,
    boundedMultiplier_coeFn (clockSign t) (clockSign_memLp t)
      (IBMPhysicalDirac.mollifiedDirac n t), IBMPhysicalDirac.mollifiedDirac_ae n t]
    with Y he hr hm hd
  change signMultiplier t (IBMPhysicalDirac.mollifiedDirac n t) Y = _ at hm
  rw [he, hr, map_smul, hm, hd]
  rfl

theorem native_slope_eq (n : ℕ) (t : ℝ≥0) :
    nativeField (signedSource n t) =
      weakField (signMultiplier t (IBMPhysicalDirac.mollifiedDirac n t)) := by
  have hn : noiseField (recover (signedSource n t)) = signedSource n t := by
    exact signedSource_physical n t
  rw [← native_kernel_eq, ← field_agreement, hn]

theorem native_slope_tendsto (t : ℝ≥0) :
    Tendsto (fun n => nativeField (signedSource n t)) atTop (nhds (slopeLimit t)) := by
  simp only [native_slope_eq, slopeLimit, signedDirac]
  exact weakField.continuous.tendsto _ |>.comp
    ((signMultiplier t).continuous.tendsto _ |>.comp (IBMPhysicalDirac.mollifiedDirac_tendsto t))

end OperatorDerivativeRewrite.Foundation.IBMPhysicalPointSlope
