import Foundation.IBMFullSchwartzClockMean
import Foundation.IBMSchwartzLiteralJoint
import Foundation.IBMQuarticJointRealization
import Foundation.ProductL2Equivalence
import Foundation.IBMClockConditionalCorrection

/-! Native joint L2 realization. Coordinates in this module are ordered
(clock, source), matching the existing product/Bochner equivalence. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFullSchwartzNativeMean
open InfiniteGaussian IBMSchwartzBochnerDomain
open IBMSchwartzTimeProjection (wholeCorrection originClass)
open IBMFullSchwartzClockMean
open IBMSchwartzJointRealization (jointClass joint_sections)
open IBMQuarticJointRealization (jointMeasure jointSourceSector sourceLift sourceLift_coeFn sourceSigma_le)

variable (g : SchwartzMap ℝ ℝ) (a : ℝ)
open GaussianNumberSectors
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

theorem whole_integrable (n : ℕ) (T : ℝ≥0) :
    Integrable (wholeCorrection g a n T) gaussianProduct :=
  (wholeCorrection_memLp g a n T).integrable (by norm_num)

theorem whole_mean (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    (∫ ω, wholeCorrection g a n T ω ∂gaussianProduct) = correctedMean g a n T := by
  have hm := ((Lp.memLp (BrownianMassLimitIdentification.coordinateClass T)).integrable
    (by norm_num)).smul_const (originClass g a n)
  have hi : Integrable (fun ω => (1/2 : ℝ) • integratedValue g a n T ω) gaussianProduct :=
    (integratedValue_integrable g a n T hT).smul (1/2 : ℝ)
  change (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω • originClass g a n+
    (1/2 : ℝ) • integratedValue g a n T ω ∂gaussianProduct) = _
  rw [integral_add hm hi, integral_smul_const, integral_smul]
  rfl

theorem source_mean_ae (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    correctedMean g a n T =ᵐ[gaussianProduct]
      fun ωX => ∫ ωY, jointClass g a n T (ωY,ωX) ∂gaussianProduct := by
  have he := BochnerL2RepresentativeFubini.integral_coeFn_ae
    (fun ωY => wholeCorrection g a n T ωY) (whole_integrable g a n T)
    (fun p => jointClass g a n T p) (Lp.stronglyMeasurable _).aestronglyMeasurable
    (joint_sections g a n T)
  rwa [whole_mean g a n T hT] at he

theorem conditional_source_ae (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    jointMeasure[jointClass g a n T |
      MeasurableSpace.comap (Prod.snd : SampleSpace × SampleSpace → SampleSpace) inferInstance] =ᵐ[jointMeasure]
      fun p => correctedMean g a n T p.2 := by
  have hi : IndepFun (Prod.snd : SampleSpace × SampleSpace → SampleSpace) Prod.fst jointMeasure :=
    (indepFun_prod (μ := gaussianProduct) (ν := gaussianProduct) measurable_id measurable_id).symm
  have he := IndependentInnovationConditioning.conditional_integral jointMeasure
    (Prod.snd : SampleSpace × SampleSpace → SampleSpace) Prod.fst measurable_snd measurable_fst hi
    (fun p : SampleSpace × SampleSpace => jointClass g a n T (p.2,p.1))
    ((Lp.stronglyMeasurable (jointClass g a n T)).comp_measurable measurable_swap)
    ((Lp.memLp (jointClass g a n T)).integrable (by norm_num))
  have hm : jointMeasure.map (Prod.fst : SampleSpace × SampleSpace → SampleSpace) = gaussianProduct :=
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).map_eq
  have hmean := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae
    (source_mean_ae g a n T hT).symm
  have hc : jointMeasure[jointClass g a n T |
      MeasurableSpace.comap (Prod.snd : SampleSpace × SampleSpace → SampleSpace) inferInstance] =ᵐ[jointMeasure]
      fun p => ∫ ωY, jointClass g a n T (ωY,p.2) ∂gaussianProduct := by
    simpa only [hm, Prod.mk.eta] using he
  exact hc.trans hmean

/-- The whole correction conditioned on the complete scenery factor. All
source chaos degrees are retained; the clock factor is averaged out. -/
theorem native_mean_eq (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    (condExpL2 ℝ ℝ sourceSigma_le (jointClass g a n T) : Lp ℝ 2 jointMeasure) =
      sourceLift (correctedMean g a n T) := by
  apply Lp.ext
  have he := (Lp.memLp (jointClass g a n T)).condExpL2_ae_eq_condExp (𝕜 := ℝ) sourceSigma_le
  have hh : (condExpL2 ℝ ℝ sourceSigma_le (jointClass g a n T) : Lp ℝ 2 jointMeasure) =ᵐ[jointMeasure]
      jointMeasure[jointClass g a n T |
        MeasurableSpace.comap (Prod.snd : SampleSpace × SampleSpace → SampleSpace) inferInstance] := by
    simpa only [Lp.toLp_coeFn] using he
  exact hh.trans ((conditional_source_ae g a n T hT).trans (sourceLift_coeFn _).symm)

theorem native_mean_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => (condExpL2 ℝ ℝ sourceSigma_le (jointClass g a n T) : Lp ℝ 2 jointMeasure))
      atTop (𝓝 (sourceLift (IBMFullSchwartzTerminal.terminalLimit g a T-g a • gaussianOne))) := by
  simp_rw [native_mean_eq g a _ T hT]
  change Tendsto (sourceLift ∘ fun n => correctedMean g a n T) atTop _
  exact sourceLift.continuous.tendsto _ |>.comp (correctedMean_tendsto g a T hT)


theorem literal_native_mean_eq (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    (condExpL2 ℝ ℝ sourceSigma_le (IBMSchwartzLiteralJoint.literalClass g a n T) :
      Lp ℝ 2 jointMeasure) =
      sourceLift (IBMFullSchwartzTerminal.terminal g a n T-IBMFullSchwartzTerminal.spatial g a n 0) := by
  rw [IBMSchwartzLiteralJoint.literalClass_eq_joint, native_mean_eq g a n T hT,
    correctedMean_eq_terminal g a n T hT]

theorem literal_native_mean_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => (condExpL2 ℝ ℝ sourceSigma_le
      (IBMSchwartzLiteralJoint.literalClass g a n T) : Lp ℝ 2 jointMeasure)) atTop
      (𝓝 (sourceLift (IBMFullSchwartzTerminal.terminalLimit g a T-g a • gaussianOne))) := by
  simp_rw [IBMSchwartzLiteralJoint.literalClass_eq_joint]
  exact native_mean_tendsto g a T hT

theorem terminal_zero (n : ℕ) : IBMFullSchwartzTerminal.terminal g a n 0 =
    IBMFullSchwartzTerminal.spatial g a n 0 := by
  have hc := (IBMConstructedSources.clockPath_coordinate_ae 0).trans GaussianTimeProcess.process_zero_ae
  unfold IBMFullSchwartzTerminal.terminal
  have he : (fun ω => IBMFullSchwartzTerminal.spatial g a n
      |IBMConstructedSources.clockPath ω 0|) =ᵐ[gaussianProduct]
      fun _ => IBMFullSchwartzTerminal.spatial g a n 0 := by
    filter_upwards [hc] with ω hω
    simp only [hω, abs_zero]
  rw [integral_congr_ae he]
  simp

theorem terminalLimit_zero : IBMFullSchwartzTerminal.terminalLimit g a 0 = g a • gaussianOne := by
  have hc := (IBMConstructedSources.clockPath_coordinate_ae 0).trans GaussianTimeProcess.process_zero_ae
  unfold IBMFullSchwartzTerminal.terminalLimit
  have he : (fun ω => IBMFullSchwartzTerminal.spatialLimit g a
      |IBMConstructedSources.clockPath ω 0|) =ᵐ[gaussianProduct] fun _ => g a • gaussianOne := by
    filter_upwards [hc] with ω hω
    simp only [hω, abs_zero, IBMFullSchwartzTerminal.origin_limit]
  rw [integral_congr_ae he]
  simp

theorem literal_native_mean_eq_all (n : ℕ) (T : ℝ≥0) :
    (condExpL2 ℝ ℝ sourceSigma_le (IBMSchwartzLiteralJoint.literalClass g a n T) :
      Lp ℝ 2 jointMeasure) =
      sourceLift (IBMFullSchwartzTerminal.terminal g a n T-IBMFullSchwartzTerminal.spatial g a n 0) := by
  by_cases hT : T=0
  · subst T
    simp [IBMSchwartzLiteralJoint.literalClass_zero, terminal_zero]
  · exact literal_native_mean_eq g a n T (pos_iff_ne_zero.mpr hT)

/-- Includes zero horizon by actual zero-time identities, without using a
positive-time heat potential at T=0. -/
theorem literal_native_mean_tendsto_all (T : ℝ≥0) :
    Tendsto (fun n => (condExpL2 ℝ ℝ sourceSigma_le
      (IBMSchwartzLiteralJoint.literalClass g a n T) : Lp ℝ 2 jointMeasure)) atTop
      (𝓝 (sourceLift (IBMFullSchwartzTerminal.terminalLimit g a T-g a • gaussianOne))) := by
  simp_rw [literal_native_mean_eq_all]
  exact sourceLift.continuous.tendsto _ |>.comp (IBMFullSchwartzTerminal.difference_tendsto g a T)

/-- Uniform source-chaos tails for the actual scenery-conditional correction,
not merely for an unidentified terminal candidate. Both indices vary only
after their thresholds have been chosen. All nonnegative horizons. -/
theorem native_uniform_source_tail (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 n0 : ℕ, ∀ N ≥ N0, ∀ n ≥ n0,
      ‖(condExpL2 ℝ ℝ sourceSigma_le (IBMSchwartzLiteralJoint.literalClass g a n T) :
          Lp ℝ 2 jointMeasure)-sourceLift (truncation N
            (IBMFullSchwartzTerminal.terminal g a n T-IBMFullSchwartzTerminal.spatial g a n 0))‖ < ε := by
  obtain ⟨N0,n0,h⟩ := IBMFullSchwartzTerminal.uniform_source_tail g a T hε
  refine ⟨N0,n0,fun N hNN n hnn => ?_⟩
  rw [literal_native_mean_eq_all g a n T, ← map_sub, sourceLift.norm_map]
  exact h N hNN n hnn

end OperatorDerivativeRewrite.Foundation.IBMFullSchwartzNativeMean
