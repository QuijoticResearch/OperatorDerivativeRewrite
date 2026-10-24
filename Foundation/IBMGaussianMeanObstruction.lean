import Foundation.IBMSchwartzSimpsonNative
import Foundation.IBMCenteredSourceRepresentation
import Foundation.GaussianSchwartzKernel
import Foundation.IBMDeterministicRangeObstruction

/-! The mean correction in the physical/native comparison cannot be omitted:
the actual Gaussian Schwartz terminal at time1 has expectation strictly below1. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMGaussianMeanObstruction
open InfiniteGaussian IBMTimeAveragedObservable IBMConstructedSources
open IBMSchwartzSimpsonNative GaussianSchwartzKernel
attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative physicalValue

theorem mean_less_one :
    (∫ p, realSchwartz (ibmValue 1 p) ∂IBMSourceLaws.jointMeasure) < 1 := by
  let A : IBMSourceLaws.JointSample → ℝ := fun p => realSchwartz (ibmValue 1 p)
  have he : IBMSchwartzHybridReconstruction.terminal realSchwartz 0 1 =ᵐ[IBMSourceLaws.jointMeasure] A := by
    simpa only [zero_add] using IBMSchwartzHybridReconstruction.terminal_actual realSchwartz 0 1
  have hi : Integrable A IBMSourceLaws.jointMeasure :=
    ((Lp.memLp (IBMSchwartzHybridReconstruction.terminal realSchwartz 0 1)).integrable
      (by norm_num)).congr he
  have hn (p : IBMSourceLaws.JointSample) : 0 ≤ 1-A p := by
    change 0 ≤ 1-Real.exp (-(ibmValue 1 p)^2)
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  have hd : Integrable (fun p => 1-A p) IBMSourceLaws.jointMeasure :=
    (integrable_const 1).sub hi
  have hne : (∫ p, 1-A p ∂IBMSourceLaws.jointMeasure) ≠ 0 := by
    intro hzero
    have hz := (integral_eq_zero_iff_of_nonneg hn hd).mp hzero
    have hB : ibmValue 1 =ᵐ[IBMSourceLaws.jointMeasure] fun _ => (0 : ℝ) := by
      filter_upwards [hz] with p hp
      change 1-Real.exp (-(ibmValue 1 p)^2) = 0 at hp
      have heq : Real.exp (-(ibmValue 1 p)^2) = 1 := by linarith
      exact sq_eq_zero_iff.mp (neg_eq_zero.mp ((Real.exp_eq_one_iff _).mp heq))
    have hobs : IBMDeterministicRangeObstruction.observed 1 = 0 := by
      apply Lp.ext
      filter_upwards [IBMDeterministicRangeObstruction.observed_ae 1,hB,
        Lp.coeFn_zero ℝ 2 IBMSourceLaws.jointMeasure] with p ho hb h0
      rw [ho,hb,h0]
      rfl
    exact IBMDeterministicRangeObstruction.observed_one_ne_zero hobs
  have hp : 0 < ∫ p, 1-A p ∂IBMSourceLaws.jointMeasure :=
    lt_of_le_of_ne (integral_nonneg hn) (Ne.symm hne)
  have hI : (∫ p, 1-A p ∂IBMSourceLaws.jointMeasure) =
      1-∫ p, A p ∂IBMSourceLaws.jointMeasure := by
    rw [integral_sub (integrable_const 1) hi]
    simp
  rw [hI] at hp
  linarith

theorem physical_mean_negative :
    (∫ p, physicalValue realSchwartz 0 1 p ∂IBMSourceLaws.jointMeasure) < 0 := by
  have hg : realSchwartz 0 = 1 := by change Real.exp (-(0 : ℝ)^2) = 1; norm_num
  have he : physicalValue realSchwartz 0 1 =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => realSchwartz (ibmValue 1 p)-1 := by
    simpa only [zero_add,hg] using physicalValue_actual realSchwartz 0 1
  have hA : Integrable (fun p => realSchwartz (ibmValue 1 p)) IBMSourceLaws.jointMeasure :=
    ((Lp.memLp (IBMSchwartzHybridReconstruction.terminal realSchwartz 0 1)).integrable
      (by norm_num)).congr (by
        simpa only [zero_add] using IBMSchwartzHybridReconstruction.terminal_actual realSchwartz 0 1)
  rw [integral_congr_ae he,integral_sub hA (integrable_const 1)]
  have h1 : (∫ _ : IBMSourceLaws.JointSample, (1 : ℝ) ∂IBMSourceLaws.jointMeasure) = 1 := by simp
  rw [h1]
  exact sub_neg.mpr mean_less_one

theorem no_uncentered_divergence (u : IBMJointIntrinsicDerivative.jointDivergence.domain) :
    (IBMJointIntrinsicDerivative.jointDivergence u : JointL2) ≠ physicalValue realSchwartz 0 1 := by
  intro he
  have hz := IBMCenteredSourceRepresentation.divergence_mean_zero u
  rw [he] at hz
  have hn := physical_mean_negative
  linarith

end OperatorDerivativeRewrite.Foundation.IBMGaussianMeanObstruction
