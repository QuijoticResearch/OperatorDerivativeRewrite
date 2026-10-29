import Foundation.CubeWilsonSlab
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-! Endpoint gauge invariance of the correctly split homogeneous cube slab.
The Haar-averaged kernel retains its actual temporal-link integral. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeSlabGauge
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab

private theorem face_cycle (p : SpatialFace) :
    shift (faceEdge p 0).val.1 (faceEdge p 0).val.2=(faceEdge p 1).val.1 ∧
    shift (faceEdge p 1).val.1 (faceEdge p 1).val.2=
      shift (faceEdge p 2).val.1 (faceEdge p 2).val.2 ∧
    (faceEdge p 2).val.1=shift (faceEdge p 3).val.1 (faceEdge p 3).val.2 ∧
    (faceEdge p 3).val.1=(faceEdge p 0).val.1 := by
  rcases p with ⟨⟨v,a,b⟩,hab,ha,hb⟩
  change shift v a=shift v a ∧ shift (shift v a) b=shift (shift v b) a ∧ shift v b=shift v b ∧ v=v
  refine ⟨rfl,?_,rfl,rfl⟩
  funext j
  by_cases hja : j=a
  · subst j
    simp [shift,Function.update_apply,hab.ne,hab.ne.symm]
  · by_cases hjb : j=b
    · subst j
      simp [shift,Function.update_apply,hab.ne,hab.ne.symm]
    · simp [shift,Function.update_apply,hja,hjb]

theorem spatial_word_covariant (a : Gauge) (U : State) (p : SpatialFace) :
    spatialWord (gaugeAction a U) p=
      a (faceEdge p 0).val.1*spatialWord U p*(a (faceEdge p 0).val.1)⁻¹ := by
  have h := face_cycle p
  unfold spatialWord gaugeAction
  rw [← congrArg a h.1,← congrArg a h.2.1,congrArg a h.2.2.1,congrArg a h.2.2.2]
  group

theorem spatial_action_invariant (a : Gauge) (U : State) :
    spatialAction (gaugeAction a U)=spatialAction U := by
  unfold spatialAction
  simp_rw [spatial_word_covariant,halfTrace_conjugate]

theorem temporal_left_word (a g : Gauge) (U V : State) (e : SpatialEdge) :
    temporalWord (gaugeAction a U) V (a*g) e=
      a e.val.1*temporalWord U V g e*(a e.val.1)⁻¹ := by
  unfold temporalWord gaugeAction
  simp only [Pi.mul_apply]
  group

theorem temporal_right_word (a g : Gauge) (U V : State) (e : SpatialEdge) :
    temporalWord U (gaugeAction a V) g e=temporalWord U V (g*a) e := by
  unfold temporalWord gaugeAction
  simp only [Pi.mul_apply]
  group

theorem weight_left (beta : ℝ) (a g : Gauge) (U V : State) :
    weight beta (gaugeAction a U) V (a*g)=weight beta U V g := by
  unfold weight halfAction temporalAction
  rw [spatial_action_invariant]
  simp_rw [temporal_left_word,halfTrace_conjugate]

theorem weight_right (beta : ℝ) (a g : Gauge) (U V : State) :
    weight beta U (gaugeAction a V) g=weight beta U V (g*a) := by
  unfold weight halfAction temporalAction
  rw [spatial_action_invariant]
  simp_rw [temporal_right_word]

theorem gauge_left_preserving (a : Gauge) :
    MeasurePreserving (fun g : Gauge => a*g) gaugeHaar gaugeHaar :=
  measurePreserving_pi (fun _ => law) (fun _ => law)
    (fun v => measurePreserving_mul_left law (a v))

theorem gauge_right_preserving (a : Gauge) :
    MeasurePreserving (fun g : Gauge => g*a) gaugeHaar gaugeHaar :=
  measurePreserving_pi (fun _ => law) (fun _ => law)
    (fun v => measurePreserving_mul_right law (a v))

theorem kernel_left_invariant (beta : ℝ) (a : Gauge) (U V : State) :
    kernel beta (gaugeAction a U) V=kernel beta U V := by
  have h := (gauge_left_preserving a).integral_comp (MeasurableEquiv.mulLeft a).measurableEmbedding
    (weight beta (gaugeAction a U) V)
  change (∫ g,weight beta (gaugeAction a U) V (a*g) ∂gaugeHaar)=
    kernel beta (gaugeAction a U) V at h
  rw [← h]
  simp_rw [weight_left]
  rfl

theorem kernel_right_invariant (beta : ℝ) (a : Gauge) (U V : State) :
    kernel beta U (gaugeAction a V)=kernel beta U V := by
  unfold kernel
  simp_rw [weight_right]
  exact (gauge_right_preserving a).integral_comp (MeasurableEquiv.mulRight a).measurableEmbedding _

/-- A positive eigenfunction of THIS actual temporal-integrated finite kernel.
Bounds depend on beta; no uniform spectral-gap claim is made. -/
theorem positive_ground_exists (beta : ℝ) :
    ∃ lam : ℝ, ∃ psi : State → ℝ, 0 < lam ∧ Measurable psi ∧
      (∀ U,Real.exp (-36*|beta|)/Real.exp (36*|beta|) ≤ psi U ∧
        psi U ≤ Real.exp (36*|beta|)/Real.exp (-36*|beta|)) ∧
      (∀ U,∫ V,kernel beta U V*psi V ∂boundaryHaar=lam*psi U) ∧
      (∀ a U,psi (gaugeAction a U)=psi U) := by
  obtain ⟨lam,psi,hl,hu,hm,hb,he⟩ :=
    YMPositivePower.positive_eigenfunction_exists boundaryHaar (kernel beta)
      (Real.exp (-36*|beta|)) (Real.exp (36*|beta|)) (kernel_joint_measurable beta)
      (Real.exp_pos _) (kernel_bounds beta) (fun _ => 1)
  have hlam : 0 < lam := (Real.exp_pos _).trans_le hl
  refine ⟨lam,psi,hlam,hm,hb,he,?_⟩
  intro a U
  have h1 := he (gaugeAction a U)
  have h2 := he U
  unfold YMPositivePower.applyKernel at h1 h2
  simp_rw [kernel_left_invariant] at h1
  nlinarith

theorem temporal_swap (U V : State) (g : Gauge) (e : SpatialEdge) :
    halfTrace (temporalWord V U g⁻¹ e)=halfTrace (temporalWord U V g e) := by
  have he : temporalWord V U g⁻¹ e=
      (g e.val.1)⁻¹*(temporalWord U V g e)⁻¹*g e.val.1 := by
    unfold temporalWord
    simp only [Pi.inv_apply]
    group
  rw [he]
  have hc := halfTrace_conjugate ((g e.val.1)⁻¹) ((temporalWord U V g e)⁻¹)
  simpa only [inv_inv] using hc.trans (SU2WilsonConvolution.halfTrace_inv _)

theorem weight_swap (beta : ℝ) (U V : State) (g : Gauge) :
    weight beta V U g⁻¹=weight beta U V g := by
  have ht : temporalAction V U g⁻¹=temporalAction U V g := by
    unfold temporalAction
    apply Finset.sum_congr rfl
    intro e _
    rw [temporal_swap U V g e]
  unfold weight halfAction
  rw [ht]
  congr 1
  ring

private theorem su2_inv_preserving : MeasurePreserving (fun A : SU2 => A⁻¹) law law := by
  letI : IsProbabilityMeasure law.inv := by
    change IsProbabilityMeasure (law.map (fun A : SU2 => A⁻¹))
    infer_instance
  letI : law.inv.IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior law.inv Set.univ isCompact_univ
      (by simp) (by simp) (by simp)
  have h : law.inv=law := (law_eq_probability_haar law.inv).symm
  exact ⟨measurable_inv,h⟩

theorem gauge_inv_preserving : MeasurePreserving (fun g : Gauge => g⁻¹) gaugeHaar gaugeHaar :=
  measurePreserving_pi (fun _ => law) (fun _ => law) (fun _ => su2_inv_preserving)

/-- Symmetry of the actual temporal-integrated kernel; not an operator positivity claim. -/
theorem kernel_symmetric (beta : ℝ) (U V : State) : kernel beta U V=kernel beta V U := by
  have h := gauge_inv_preserving.integral_comp (MeasurableEquiv.inv Gauge).measurableEmbedding
    (weight beta V U)
  change (∫ g,weight beta V U g⁻¹ ∂gaugeHaar)=kernel beta V U at h
  rw [← h]
  simp_rw [weight_swap]
  rfl

end OperatorDerivativeRewrite.Foundation.CubeSlabGauge
