import Foundation.IBMIntrinsicChainApproximation

/-! Strong L2 convergence of the actual native product-space multipliers. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicChainMultiplier
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicChainRule
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def multiply (a : IBMSourceLaws.JointSample → ℝ)
    (ha : AEStronglyMeasurable a IBMSourceLaws.jointMeasure) (B : ℝ)
    (hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖a ω‖ ≤ B) (g : JointVectorL2) : JointVectorL2 :=
  (smul_memLp (p := ∞) (q := 2) (r := 2) (MemLp.of_bound ha B hb) (Lp.memLp g)).toLp _

theorem multiply_ae (a : IBMSourceLaws.JointSample → ℝ)
    (ha : AEStronglyMeasurable a IBMSourceLaws.jointMeasure) (B : ℝ)
    (hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖a ω‖ ≤ B) (g : JointVectorL2) :
    multiply a ha B hb g =ᵐ[IBMSourceLaws.jointMeasure] fun ω => a ω • g ω :=
  MemLp.coeFn_toLp _

theorem multiply_norm (a : IBMSourceLaws.JointSample → ℝ)
    (ha : AEStronglyMeasurable a IBMSourceLaws.jointMeasure) (B : ℝ)
    (hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖a ω‖ ≤ B) (g : JointVectorL2) :
    ‖multiply a ha B hb g‖ ≤ B * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae a ha B hb g, hb] with ω hω hbound
  rw [hω,norm_smul]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

theorem multiply_tendsto (a : ℕ → IBMSourceLaws.JointSample → ℝ)
    (b : IBMSourceLaws.JointSample → ℝ)
    (ha : ∀ n, AEStronglyMeasurable (a n) IBMSourceLaws.jointMeasure)
    (hb : AEStronglyMeasurable b IBMSourceLaws.jointMeasure) (B : ℝ) (hB : 0 ≤ B)
    (hba : ∀ n, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖a n ω‖ ≤ B)
    (hbb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖b ω‖ ≤ B)
    (ht : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, Tendsto (fun n => a n ω) atTop (𝓝 (b ω)))
    (g : JointVectorL2) :
    Tendsto (fun n => multiply (a n) (ha n) B (hba n) g) atTop
      (𝓝 (multiply b hb B hbb g)) := by
  let hm := (Lp.memLp g).norm.const_mul B
  let m : Lp ℝ 2 IBMSourceLaws.jointMeasure := hm.toLp (fun ω => B * ‖g ω‖)
  apply BochnerL2Approximation.tendsto_of_dominated _ _ m
  · intro n
    filter_upwards [multiply_ae (a n) (ha n) B (hba n) g, hm.coeFn_toLp, hba n]
      with ω ha hm hb
    rw [ha,hm,norm_smul,Real.norm_of_nonneg (mul_nonneg hB (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · filter_upwards [multiply_ae b hb B hbb g, hm.coeFn_toLp, hbb] with ω ha hm hb
    rw [ha,hm,norm_smul,Real.norm_of_nonneg (mul_nonneg hB (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · filter_upwards [ht, ae_all_iff.mpr (fun n => multiply_ae (a n) (ha n) B (hba n) g),
      multiply_ae b hb B hbb g] with ω ht ha hb
    simpa only [ha,hb] using ht.smul_const (g ω)

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicChainMultiplier
