import Foundation.IBMConditionalNativeCalculus
import Foundation.IBMIntrinsicAbsoluteChain

/-! Uniformly bounded ORIGINAL-domain tests approximate every bounded IBM observable. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMUniformBoundedNativeTests
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative
set_option backward.isDefEq.respectTransparency false

def clip (x : ℝ) : ℝ := (1/2 : ℝ) * (|x+1|-|x-1|)

theorem clip_eq_max_min (x : ℝ) : clip x = max (-1) (min 1 x) := by
  unfold clip
  by_cases hx : x ≤ -1
  · rw [abs_of_nonpos (by linarith : x+1 ≤ 0),abs_of_nonpos (by linarith : x-1 ≤ 0),
      min_eq_right (by linarith : x ≤ 1),max_eq_left hx]
    ring
  · have hlo : -1 ≤ x := le_of_lt (lt_of_not_ge hx)
    by_cases hh : 1 ≤ x
    · rw [abs_of_nonneg (by linarith : 0 ≤ x+1),abs_of_nonneg (by linarith : 0 ≤ x-1),
        min_eq_left hh,max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
      ring
    · have hhi : x ≤ 1 := le_of_lt (lt_of_not_ge hh)
      rw [abs_of_nonneg (by linarith : 0 ≤ x+1),abs_of_nonpos (by linarith : x-1 ≤ 0),
        min_eq_right hhi,max_eq_right hlo]
      ring

theorem clip_bound (x : ℝ) : |clip x| ≤ 1 := by
  rw [clip_eq_max_min,abs_le]
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clip_fixed (x : ℝ) (hx : |x| ≤ 1) : clip x = x := by
  rw [clip_eq_max_min,min_eq_right (abs_le.mp hx).2,max_eq_right (abs_le.mp hx).1]

theorem clip_nonexpansive (x y : ℝ) : |clip x-clip y| ≤ |x-y| := by
  rw [clip_eq_max_min,clip_eq_max_min]
  calc
    _ ≤ max |(-1 : ℝ)-(-1)| |min 1 x-min 1 y| := abs_max_sub_max_le_max _ _ _ _
    _ = |min 1 x-min 1 y| := by simp
    _ ≤ max |(1 : ℝ)-1| |x-y| := abs_min_sub_min_le_max _ _ _ _
    _ = |x-y| := by simp

theorem half_sub_ae (A B : JointL2) :
    ((1/2 : ℝ) • (A-B) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => (1/2 : ℝ) * (A ω-B ω) := by
  filter_upwards [Lp.coeFn_smul (1/2 : ℝ) (A-B),Lp.coeFn_sub A B] with ω hm hs
  rw [hm,Pi.smul_apply,hs,Pi.sub_apply,smul_eq_mul]

theorem clip_domain (f : jointDerivative.domain) :
    ∃ F : jointDerivative.domain,
      ((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => clip (((f : IntrinsicSpace) : JointL2) ω) := by
  obtain ⟨A,hA,_,_,_⟩ := IBMIntrinsicAbsoluteChain.absolute_shift_chain f (-1)
  obtain ⟨B,hB,_,_,_⟩ := IBMIntrinsicAbsoluteChain.absolute_shift_chain f 1
  refine ⟨(1/2 : ℝ) • (A-B),?_⟩
  have hh := half_sub_ae ((A : IntrinsicSpace) : JointL2) ((B : IntrinsicSpace) : JointL2)
  change ((1/2 : ℝ) • (((A : IntrinsicSpace) : JointL2)-((B : IntrinsicSpace) : JointL2)))
    =ᵐ[IBMSourceLaws.jointMeasure] _
  filter_upwards [hh,hA,hB] with ω hh hA hB
  rw [hh,hA,hB]
  simp only [sub_neg_eq_add]
  rfl

theorem clipped_error_norm (X G Y : JointL2)
    (hX : X =ᵐ[IBMSourceLaws.jointMeasure] fun ω => clip (G ω))
    (hY : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |Y ω| ≤ 1) : ‖X-Y‖ ≤ ‖G-Y‖ := by
  have hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖(X-Y) ω‖ ≤ (1 : ℝ)*‖(G-Y) ω‖ := by
    filter_upwards [hX,hY,Lp.coeFn_sub X Y,Lp.coeFn_sub G Y] with ω hX hY hx hg
    rw [hx,hg,Pi.sub_apply,Pi.sub_apply,hX,Real.norm_eq_abs,Real.norm_eq_abs,one_mul]
    have he := clip_nonexpansive (G ω) (Y ω)
    rw [clip_fixed (Y ω) hY] at he
    exact he
  simpa only [one_mul] using Lp.norm_le_mul_norm_of_ae_le_mul hb

theorem uniformly_bounded_approximation (F : IntrinsicSpace)
    (hF : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(F : JointL2) ω| ≤ 1) :
    ∃ u : ℕ → jointDerivative.domain,
      (∀ n, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((u n : IntrinsicSpace) : JointL2) ω)| ≤ 1) ∧
      Tendsto (fun n => ((u n : IntrinsicSpace) : JointL2)) atTop (𝓝 (F : JointL2)) := by
  obtain ⟨g,hg,hlim⟩ := mem_closure_iff_seq_limit.mp (jointDerivative_dense F)
  choose u hu using fun n => clip_domain ⟨g n,hg n⟩
  have hb (n : ℕ) : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      |(((u n : IntrinsicSpace) : JointL2) ω)| ≤ 1 := by
    filter_upwards [hu n] with ω hω
    rw [hω]
    exact clip_bound _
  have hv : Tendsto (fun n => (g n : JointL2)) atTop (𝓝 (F : JointL2)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hlim
  have hz : Tendsto (fun n => ‖(g n : JointL2)-(F : JointL2)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero] using (hv.sub_const (F : JointL2)).norm
  have hn := squeeze_zero (fun n => norm_nonneg (((u n : IntrinsicSpace) : JointL2)-(F : JointL2)))
    (fun n => clipped_error_norm _ _ _ (hu n) hF) hz
  exact ⟨u,hb,tendsto_iff_norm_sub_tendsto_zero.mpr hn⟩

end OperatorDerivativeRewrite.Foundation.IBMUniformBoundedNativeTests
