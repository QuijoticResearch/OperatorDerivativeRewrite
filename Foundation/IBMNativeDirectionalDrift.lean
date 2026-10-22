import Foundation.IBMNativeDirectionalMaps

/-! Actual L2 convergence of clipped multiplication by a fixed native divergence value. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeDirectionalDrift
open IBMTimeAveragedObservable IBMIntrinsicChainApproximation
set_option backward.isDefEq.respectTransparency false

def drift (f z : JointL2)
    (h : MemLp (fun ω => f ω*z ω) 2 IBMSourceLaws.jointMeasure) : JointL2 :=
  h.toLp (fun ω => f ω*z ω)

theorem drift_ae (f z : JointL2)
    (h : MemLp (fun ω => f ω*z ω) 2 IBMSourceLaws.jointMeasure) :
    drift f z h =ᵐ[IBMSourceLaws.jointMeasure] fun ω => f ω*z ω := h.coeFn_toLp

theorem drift_limit (f z : JointL2)
    (h : MemLp (fun ω => f ω*z ω) 2 IBMSourceLaws.jointMeasure)
    (a : ℕ → JointL2)
    (ha : ∀ n, a n =ᵐ[IBMSourceLaws.jointMeasure] fun ω => clip n (f ω))
    (hb : ∀ n, MemLp (a n : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    Tendsto (fun n => boundedMultiplier (a n) (hb n) z) atTop (𝓝 (drift f z h)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ (drift f z h) (drift f z h)
  · intro n
    filter_upwards [boundedMultiplier_coeFn (a n) (hb n) z,ha n,drift_ae f z h]
      with ω hm ha hd
    rw [hm,ha,hd,norm_smul,norm_mul]
    exact mul_le_mul_of_nonneg_right (clip_domination n (f ω)) (norm_nonneg _)
  · exact ae_of_all _ fun _ => le_rfl
  · filter_upwards [ae_all_iff.mpr ha,
      ae_all_iff.mpr (fun n => boundedMultiplier_coeFn (a n) (hb n) z),drift_ae f z h]
      with ω ha hm hd
    have ht := (clip_tendsto (f ω)).mul_const (z ω)
    simpa only [hm,ha,hd,smul_eq_mul] using ht

end OperatorDerivativeRewrite.Foundation.IBMNativeDirectionalDrift
