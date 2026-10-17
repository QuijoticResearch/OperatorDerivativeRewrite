import Foundation.GaussianJointShearSmooth

/-! Explicit failure of a canonical threshold/time-window screening statement for the fixed shear. -/
noncomputable section
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianShearNoScreening
open FiniteFourierSynthesis GaussianInfiniteShear GaussianJointShearSmooth
open GaussianShearShellSplit GaussianShearShellSeparation GaussianShearLowAnisotropy
open FibonacciShearCentroid LabelledShearCentroid

def canonicalScreening (nu : ℝ) : Prop :=
  ∃ B : ℝ, ∀ N : ℕ, 1 ≤ N →
    0 < GaussianShearLowAnisotropy.variance N nu 0 → B < highCentroid N nu 0 →
      ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 < t → t ≤ T → zeroExtendedCentroid partition nu t < 1

theorem threshold_window_failure (nu : ℝ) (hnu : 0 < nu) (B T : ℝ) (hT : 0 < T) :
    ∃ N : ℕ, 1 ≤ N ∧ 0 < GaussianShearLowAnisotropy.variance N nu 0 ∧
      B < highCentroid N nu 0 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ T ∧
        1 < zeroExtendedCentroid partition nu t := by
  obtain ⟨N,hN,hvar,hall⟩ := fixed_flow_separation nu hnu B
  obtain ⟨_,_,_,_,_,hB0,_,_⟩ := hall 0 (by norm_num)
  obtain ⟨_,_,_,_,_,_,_,hRatio⟩ := hall (T/2) (by positivity)
  exact ⟨N,hN,hvar,hB0,T/2,by positivity,by linarith,hRatio⟩

theorem no_canonical_screening (nu : ℝ) (hnu : 0 < nu) : ¬ canonicalScreening nu := by
  rintro ⟨B,h⟩
  obtain ⟨N,hN,hvar,hall⟩ := fixed_flow_separation nu hnu B
  obtain ⟨_,_,_,_,_,hB0,_,_⟩ := hall 0 (by norm_num)
  obtain ⟨T,hT,hsmall⟩ := h N hN hvar hB0
  obtain ⟨_,_,_,_,_,_,_,hRatio⟩ := hall (T/2) (by positivity)
  have hbad := hsmall (T/2) (by positivity) (by linarith)
  linarith

theorem fixed_initial (nu mu : ℝ) (x : Space) : velocity nu 0 x=velocity mu 0 x := by
  rw [initial,initial]

theorem smooth_countermodel (nu : ℝ) (hnu : 0 < nu) :
    (∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ContDiffAt ℝ ∞ (fun p : ℝ × Space => velocity nu p.1 p.2) (t,x)) ∧
    ¬ canonicalScreening nu :=
  ⟨fun t ht x => joint_at_nonnegative nu t hnu.le ht x,no_canonical_screening nu hnu⟩

end OperatorDerivativeRewrite.Foundation.GaussianShearNoScreening
