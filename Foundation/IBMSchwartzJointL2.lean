import Foundation.IBMDerivativeFourthDomain
import Foundation.IBMClockConditionalCorrection
import Foundation.FiniteMeasureL2Integration

/-! The genuine fixed-mollifier joint L² domain of the full Schwartz
correction, before any higher-source projection or singular limit. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzJointL2
open InfiniteGaussian IBMSourceLaws IBMGeneralSchwartzFubini IBMCorrectionStein
open IBMFiniteHorizonEvaluation IBMDerivativeFourthDomain IBMClockConditionalCorrection

theorem correction_square_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (p : ℝ × JointSample) :
    (timeValue g a n p)^2 ≤
      2*(SchwartzMap.seminorm ℝ 0 0 (jet g 2))^2 * (horizonValue n 1 p)^4 +
      2*(SchwartzMap.seminorm ℝ 0 0 (jet g 1))^2 * (horizonValue n 2 p)^2 := by
  have h₂ := shiftedJet_bound g a 2 (horizonValue n 0 p)
  have h₁ := shiftedJet_bound g a 1 (horizonValue n 0 p)
  have h₂sq := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  have h₁sq := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  simp only [Real.norm_eq_abs, sq_abs] at h₂sq h₁sq
  have he₂ := mul_le_mul_of_nonneg_right h₂sq (by positivity : 0 ≤ (horizonValue n 1 p)^4)
  have he₁ := mul_le_mul_of_nonneg_right h₁sq (sq_nonneg (horizonValue n 2 p))
  change (shiftedJet g a 2 (horizonValue n 0 p)*(horizonValue n 1 p)^2 +
    shiftedJet g a 1 (horizonValue n 0 p)*horizonValue n 2 p)^2 ≤ _
  nlinarith [sq_nonneg (shiftedJet g a 2 (horizonValue n 0 p)*(horizonValue n 1 p)^2 -
    shiftedJet g a 1 (horizonValue n 0 p)*horizonValue n 2 p)]

theorem timeValue_square_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Integrable (fun p => (timeValue g a n p)^2)
      ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod jointMeasure) := by
  have hi := ((horizon_fourth_integrable n 1 T).const_mul
    (2*(SchwartzMap.seminorm ℝ 0 0 (jet g 2))^2)).add
      ((horizon_square_integrable n 2 T).const_mul
        (2*(SchwartzMap.seminorm ℝ 0 0 (jet g 1))^2))
  apply hi.mono' ((timeValue_measurable g a n).pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact correction_square_bound g a n p

theorem timeValue_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp (timeValue g a n) 2 ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod jointMeasure) :=
  (memLp_two_iff_integrable_sq (timeValue_measurable g a n).aestronglyMeasurable).mpr
    (timeValue_square_integrable g a n T)

theorem integratedValue_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp (integratedValue g a n T) 2 jointMeasure := by
  unfold integratedValue
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  simpa only [timeValue] using FiniteMeasureL2Integration.column_integral_memLp
    (timeValue g a n) (timeValue_memLp g a n T)

def jointClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : Lp ℝ 2 jointMeasure :=
  (integratedValue_memLp g a n T).toLp _

theorem jointClass_coeFn (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    jointClass g a n T =ᵐ[jointMeasure] integratedValue g a n T :=
  (integratedValue_memLp g a n T).coeFn_toLp

theorem integratedValue_energy_le (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    (∫ ω, (integratedValue g a n T ω)^2 ∂jointMeasure) ≤
      (volume.restrict (Set.Ioc 0 (T : ℝ))).real Set.univ *
        ∫ p, (timeValue g a n p)^2
          ∂(volume.restrict (Set.Ioc 0 (T : ℝ))).prod jointMeasure := by
  unfold integratedValue
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact FiniteMeasureL2Integration.column_integral_energy_le _ (timeValue_memLp g a n T)

theorem conditionalClass_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    jointMeasure[jointClass g a n T |
      MeasurableSpace.comap (Prod.snd : JointSample → SampleSpace) inferInstance] =ᵐ[jointMeasure]
      clockLift (IBMSceneryAveragedCorrectionLimit.averagedClass g a n T) :=
  (condExp_congr_ae (jointClass_coeFn g a n T)).trans (liftedClass_coeFn g a n T).symm

theorem clockSigma_le :
    MeasurableSpace.comap (Prod.snd : JointSample → SampleSpace) inferInstance ≤
      (inferInstance : MeasurableSpace JointSample) := measurable_snd.comap_le

/-- The native L² conditional projection is now applied to its proved joint
L² input, and agrees with the identified genuine clock mean. -/
theorem clockProjection_eq (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    (condExpL2 ℝ ℝ clockSigma_le (jointClass g a n T) : Lp ℝ 2 jointMeasure) =
      clockLift (IBMSceneryAveragedCorrectionLimit.averagedClass g a n T) := by
  apply Lp.ext
  have he := (Lp.memLp (jointClass g a n T)).condExpL2_ae_eq_condExp (𝕜 := ℝ) clockSigma_le
  have hh : (condExpL2 ℝ ℝ clockSigma_le (jointClass g a n T) : Lp ℝ 2 jointMeasure) =ᵐ[jointMeasure]
      jointMeasure[jointClass g a n T |
        MeasurableSpace.comap (Prod.snd : JointSample → SampleSpace) inferInstance] := by
    simpa only [Lp.toLp_coeFn] using he
  exact hh.trans (conditionalClass_ae g a n T)

end OperatorDerivativeRewrite.Foundation.IBMSchwartzJointL2
