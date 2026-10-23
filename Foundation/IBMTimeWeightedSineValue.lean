import Foundation.IBMSineAverageStrongJoint
import Foundation.IBMClockTimeWeightEnergy

/-! Actual rough-time-weighted IBM sine observables, constructed inside the
original closed observable space. Native mollified values converge in actual L2. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTimeWeightedSineValue
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMClockOverlapEnergy
open IBMActualSineDomainObstruction IBMNonlinearClockAverageGraph
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem point_norm_le (t : ℝ≥0) : ‖sinePoint t‖ ≤ 1 := by
  have hb : ∀ᵐ p ∂IBMSourceLaws.jointMeasure, ‖(sinePoint t : JointL2) p‖ ≤ (1:ℝ) := by
    filter_upwards [sinePoint_actual_ae t] with p hp
    rw [hp]
    exact Real.abs_sin_le_one _
  change ‖(sinePoint t : JointL2)‖ ≤ 1
  simpa [measureUnivNNReal] using
    Lp.norm_le_of_ae_bound (f := (sinePoint t : JointL2)) zero_le_one hb

theorem intrinsic_integrable (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    Integrable (fun t => g t • sinePoint t.toNNReal) (window T) := by
  apply (hg.integrable (by norm_num)).norm.mono'
    (hg.aestronglyMeasurable.smul
      (sinePoint_continuous.comp continuous_real_toNNReal).aestronglyMeasurable)
  exact ae_of_all _ fun t => by
    change ‖g t • sinePoint t.toNNReal‖ ≤ ‖g t‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (point_norm_le _) (norm_nonneg _)).trans_eq (mul_one _)

def actual (g : ℝ → ℝ) (T : ℝ≥0) : IntrinsicSpace :=
  ∫ t, g t • sinePoint t.toNNReal ∂window T

theorem actual_congr_ae (g k : ℝ → ℝ) (T : ℝ≥0) (hk : g =ᵐ[window T] k) :
    actual g T = actual k T :=
  integral_congr_ae (hk.mono fun t ht => congrArg (fun z : ℝ => z • sinePoint t.toNNReal) ht)

theorem actual_coe (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    (actual g T : JointL2) = ∫ t, g t • (sinePoint t.toNNReal : JointL2) ∂window T := by
  exact (IntrinsicSpace.subtypeL.integral_comp_comm (intrinsic_integrable g T hg)).symm

theorem joint_integrable (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    Integrable (fun t => g t • (sinePoint t.toNNReal : JointL2)) (window T) := by
  have hi := IntrinsicSpace.subtypeL.integrable_comp (intrinsic_integrable g T hg)
  change Integrable (fun t => g t • (sinePoint t.toNNReal : JointL2)) (window T) at hi
  exact hi

theorem actual_actual_ae (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    (actual g T : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] fun p =>
      ∫ t, g t * Real.sin (IBMConstructedSources.ibmValue t.toNNReal p) ∂window T := by
  rw [actual_coe g T hg]
  apply BochnerL2RepresentativeFubini.integral_coeFn_ae _ (joint_integrable g T hg)
    (fun p : ℝ × IBMSourceLaws.JointSample =>
      g p.1 * Real.sin (IBMConstructedSources.ibmValue p.1.toNNReal p.2))
  · exact hg.aestronglyMeasurable.comp_fst.mul
      IBMSineAverageClockDomain.integrand_measurable.aestronglyMeasurable
  · exact ae_of_all _ fun t => by
      filter_upwards [Lp.coeFn_smul (g t) (sinePoint t.toNNReal : JointL2),
        sinePoint_actual_ae t.toNNReal] with p hs hp
      rw [hs,Pi.smul_apply,hp]
      rfl

theorem path_integrable (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T))
    (p : IBMSourceLaws.JointSample) :
    Integrable (fun t => g t * Real.sin (IBMConstructedSources.ibmValue t.toNNReal p))
      (window T) := by
  have hc := Real.continuous_sin.comp
    ((IBMConstructedSources.ibmValue_continuous p).comp continuous_real_toNNReal)
  apply (hg.integrable (by norm_num)).norm.mono'
    (hg.aestronglyMeasurable.mul hc.aestronglyMeasurable)
  exact ae_of_all _ fun t => by
    change ‖g t * Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)‖ ≤ ‖g t‖
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (norm_nonneg _)).trans_eq (mul_one _)

theorem mollified_integrable (n : ℕ) (g : ℝ → ℝ) (T : ℝ≥0)
    (hg : MemLp g 2 (window T)) :
    Integrable (fun t => g t • sineValue n t) (window T) := by
  apply (hg.integrable (by norm_num)).norm.mono'
    (hg.aestronglyMeasurable.smul (sineValue_continuous n).aestronglyMeasurable)
  exact ae_of_all _ fun t => by
    change ‖g t • sineValue n t‖ ≤ ‖g t‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (sineValue_norm_le n t) (norm_nonneg _)).trans_eq (mul_one _)

def mollified (n : ℕ) (g : ℝ → ℝ) (T : ℝ≥0) : JointL2 :=
  ∫ t, g t • sineValue n t ∂window T

theorem point_error (n : ℕ) (t : ℝ) :
    ‖sineValue n t - (sinePoint t.toNNReal : JointL2)‖ ≤
      Real.sqrt (IBMMollifier.bump n).rOut := by
  have h := IBMClockWeakChain.value_error sineTest (IBMNonlinearClockGraph.input n t.toNNReal)
    (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal))
  have he : ‖IBMNonlinearClockGraph.input n t.toNNReal -
      jointRealization (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal)‖ =
        ‖IBMRandomTimeHilbert.randomMollifiedL2 n t.toNNReal -
          IBMRandomTimeHilbert.randomSourceL2 t.toNNReal‖ := by
    change ‖jointRealization (IBMRandomTimeHilbert.randomMollifiedL2 n t.toNNReal) -
      jointRealization (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal)‖ = _
    rw [← map_sub,jointRealization.norm_map]
  rw [he] at h
  exact h.trans (by simpa only [sineTest,one_mul] using
    IBMRandomTimeHilbert.randomMollifiedL2_error_le n t.toNNReal)

theorem mollified_error (n : ℕ) (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    ‖mollified n g T - (actual g T : JointL2)‖ ≤
      (∫ t, ‖g t‖ ∂window T) * Real.sqrt (IBMMollifier.bump n).rOut := by
  have hi := joint_integrable g T hg
  rw [mollified,actual_coe g T hg,← integral_sub (mollified_integrable n g T hg) hi]
  calc
    _ ≤ ∫ t, ‖g t • sineValue n t - g t • (sinePoint t.toNNReal : JointL2)‖ ∂window T :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖g t‖ * Real.sqrt (IBMMollifier.bump n).rOut ∂window T := by
      apply integral_mono_ae ((mollified_integrable n g T hg).sub hi).norm
        ((hg.integrable (by norm_num)).norm.mul_const _)
      exact ae_of_all _ fun t => by
        change ‖g t • sineValue n t - g t • (sinePoint t.toNNReal : JointL2)‖ ≤
          ‖g t‖ * Real.sqrt (IBMMollifier.bump n).rOut
        rw [← smul_sub,norm_smul]
        exact mul_le_mul_of_nonneg_left (point_error n t) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

theorem mollified_tendsto (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    Tendsto (fun n => mollified n g T) atTop (𝓝 (actual g T : JointL2)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun n => (∫ t, ‖g t‖ ∂window T) *
      Real.sqrt (IBMMollifier.bump n).rOut) atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp IBMMollifier.bump_outer_tendsto_zero
    simpa only [Function.comp_def,Real.sqrt_zero,mul_zero] using
      hs.const_mul (∫ t, ‖g t‖ ∂window T)
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => mollified_error n g T hg) ht

end OperatorDerivativeRewrite.Foundation.IBMTimeWeightedSineValue
