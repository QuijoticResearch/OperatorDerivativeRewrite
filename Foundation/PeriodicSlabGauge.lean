import Foundation.PeriodicWilsonSlab

/-! Independent endpoint gauge invariance of the actual periodic temporal kernel. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicSlabGauge
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab

def gaugeAction (a : Gauge) (U : State) (e : SpatialEdge) : SU2 :=
  a e.1*U e*(a (shift e.1 e.2))⁻¹

private theorem shift_commute (v : SpatialVertex) (i j : Fin 3) :
    shift (shift v i) j=shift (shift v j) i := by
  funext k
  simp only [shift]
  abel

theorem spatial_word_covariant (a : Gauge) (U : State) (p : SpatialFace) :
    spatialWord (gaugeAction a U) p=
      a p.val.1*spatialWord U p*(a p.val.1)⁻¹ := by
  unfold spatialWord gaugeAction
  rw [shift_commute p.val.1 p.val.2.1 p.val.2.2]
  group

theorem spatial_action_invariant (a : Gauge) (U : State) :
    spatialAction (gaugeAction a U)=spatialAction U := by
  unfold spatialAction
  simp_rw [spatial_word_covariant,halfTrace_conjugate]

theorem temporal_left_word (a g : Gauge) (U V : State) (e : SpatialEdge) :
    temporalWord (gaugeAction a U) V (a*g) e=
      a e.1*temporalWord U V g e*(a e.1)⁻¹ := by
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
      (∀ U,Real.exp (-768*|beta|)/Real.exp (768*|beta|) ≤ psi U ∧
        psi U ≤ Real.exp (768*|beta|)/Real.exp (-768*|beta|)) ∧
      (∀ U,∫ V,kernel beta U V*psi V ∂boundaryHaar=lam*psi U) ∧
      (∀ a U,psi (gaugeAction a U)=psi U) := by
  obtain ⟨lam,psi,hl,hu,hm,hb,he⟩ :=
    YMPositivePower.positive_eigenfunction_exists boundaryHaar (kernel beta)
      (Real.exp (-768*|beta|)) (Real.exp (768*|beta|)) (kernel_joint_measurable beta)
      (Real.exp_pos _) (kernel_bounds beta) (fun _ => 1)
  have hlam : 0 < lam := (Real.exp_pos _).trans_le hl
  refine ⟨lam,psi,hlam,hm,hb,he,?_⟩
  intro a U
  have h1 := he (gaugeAction a U)
  have h2 := he U
  unfold YMPositivePower.applyKernel at h1 h2
  simp_rw [kernel_left_invariant] at h1
  nlinarith

end OperatorDerivativeRewrite.Foundation.PeriodicSlabGauge
