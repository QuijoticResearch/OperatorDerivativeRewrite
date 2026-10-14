import Foundation.IBMClockCubicTimeProjection
import Foundation.GaussianDivergenceRecovery

/-! A genuine full scenery-source divergence primitive of the actual cubic
time-integrated Gaussian-L2 clock section. No predictable-clock or singular
spatial integration theorem is inferred. -/
noncomputable section
open MeasureTheory
open scoped NNReal
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.IBMClockCubicSourcePrimitive
open InfiniteGaussian GaussianNumberSectors GaussianTimeSpaceHermite IBMGaussianSteinMoments
open IBMCubicFirstChaos IBMClockCubicCorrection IBMClockCubicTimeProjection GaussianDivergenceRecovery

theorem correction_centered (u v w : CoefficientSpace) :
    inner ℝ gaussianOne (correction u v w)=0 := by
  have hc (h : CoefficientSpace) : inner ℝ gaussianOne (cube h)=0 := by
    rw [cube,inner_add_right,inner_smul_right,wick_centered h 2,wick_centered h 0]
    simp
  have hm (h k : CoefficientSpace) : inner ℝ gaussianOne (mixedCube h k)=0 := by
    simp only [mixedCube,inner_smul_right,inner_sub_right,inner_add_right,hc]
    ring
  simp only [correction,inner_add_right,inner_smul_right,hm]
  ring

theorem section_centered (n : ℕ) (t : ℝ≥0) (ωY : SampleSpace) :
    inner ℝ gaussianOne (sectionClass n t ωY)=0 :=
  correction_centered _ _ _

def integratedCorrection (n : ℕ) (ωY : SampleSpace) (T : ℝ) : GaussianL2 :=
  ∫ s in Set.Icc 0 T, sectionClass n (Real.toNNReal s) ωY

theorem integratedCorrection_centered (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    inner ℝ gaussianOne (integratedCorrection n ωY T)=0 := by
  have he := (innerSL ℝ gaussianOne).integral_comp_comm (sectionClass_time_integrable n ωY T)
  have hz : (∫ s in Set.Icc 0 T, inner ℝ gaussianOne
      (sectionClass n (Real.toNNReal s) ωY))=0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun s => section_centered n _ ωY
  change (∫ s in Set.Icc 0 T, inner ℝ gaussianOne (sectionClass n (Real.toNNReal s) ωY)) =
    inner ℝ gaussianOne (integratedCorrection n ωY T) at he
  exact he.symm.trans hz

def sourcePrimitive (n : ℕ) (ωY : SampleSpace) (T : ℝ) : GaussianVectorL2 :=
  recovery (integratedCorrection n ωY T)

/-- An unconditional full-source integration graph for each actual clock path.
The primitive is constructed by the independently verified recovery operator. -/
theorem sourcePrimitive_graph (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    (sourcePrimitive n ωY T,integratedCorrection n ωY T) ∈ hilbertDivergence.graph := by
  have hg := recovery_graph (integratedCorrection n ωY T)
  rw [projection_zero,integratedCorrection_centered,zero_smul,sub_zero] at hg
  exact hg

theorem sourcePrimitive_time_integral (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    sourcePrimitive n ωY T =
      ∫ s in Set.Icc 0 T, recovery (sectionClass n (Real.toNNReal s) ωY) :=
  (recoveryOperator.integral_comp_comm (sectionClass_time_integrable n ωY T)).symm

theorem sourcePrimitive_norm_le (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    ‖sourcePrimitive n ωY T‖ ≤ ‖integratedCorrection n ωY T‖ :=
  recovery_norm_le _

theorem sourcePrimitive_minimal_norm (n : ℕ) (ωY : SampleSpace) (T : ℝ)
    (u : GaussianVectorL2) (hu : (u,integratedCorrection n ωY T) ∈ hilbertDivergence.graph) :
    ‖sourcePrimitive n ωY T‖ ≤ ‖u‖ := by
  apply recovery_minimal_norm
  simpa only [projection_zero,integratedCorrection_centered,zero_smul,sub_zero] using hu

end OperatorDerivativeRewrite.Foundation.IBMClockCubicSourcePrimitive
