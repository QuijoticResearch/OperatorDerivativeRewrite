import Foundation.CubeCenterProjection

/-! Gauge averaging preserves the actual integral operator on bounded invariant
observables, although it changes the pointwise center cross-ratio witness. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeInvariantTransfer
open CubeTemporalSlab CubeWilsonSlab CubeSlabGauge CubeSlabGround CubeSlabL2

attribute [local irreducible] weight boundaryHaar gaugeHaar

private theorem joint_integrable (beta : ℝ) (U : State) (f : State → ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ V, |f V| ≤ B) :
    Integrable (fun q : State × Gauge => weight beta U q.1 q.2*f q.1)
      (boundaryHaar.prod gaugeHaar) := by
  have hc : Measurable (fun q : State × Gauge => ((U,q.1),q.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  apply Integrable.of_bound (((weight_joint_measurable beta).comp hc).mul
    (hf.comp measurable_fst)).aestronglyMeasurable (Real.exp (36*|beta|)*|B|)
  filter_upwards with q
  change ‖weight beta U q.1 q.2*f q.1‖ ≤ _
  have hp : 0 < weight beta U q.1 q.2 :=
    (Real.exp_pos _).trans_le (weight_bounds beta U q.1 q.2).1
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos hp]
  exact mul_le_mul (weight_bounds beta U q.1 q.2).2 ((hb q.1).trans (le_abs_self _))
    (abs_nonneg _) (Real.exp_pos _).le

/-- Actual Fubini/Haar reduction, including the homogeneous spatial weights. -/
theorem integral_projected_eq_raw (beta : ℝ) (f : State → ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ V, |f V| ≤ B)
    (hInv : ∀ a V, f (gaugeAction a V) = f V) (U : State) :
    (∫ V, kernel beta U V*f V ∂boundaryHaar)=
      ∫ V, weight beta U V 1*f V ∂boundaryHaar := by
  have he (a : Gauge) : (∫ V, weight beta U V a*f V ∂boundaryHaar)=
      ∫ V, weight beta U V 1*f V ∂boundaryHaar := by
    have h := (boundary_gauge_preserving a).integral_comp
      (show MeasurableEmbedding (gaugeAction a) from
        (boundaryGaugeEquiv a).measurableEmbedding)
      (fun V => weight beta U V 1*f V)
    change (∫ V, weight beta U (gaugeAction a V) 1*f (gaugeAction a V) ∂boundaryHaar)=_ at h
    simp_rw [weight_right,one_mul,hInv] at h
    exact h
  unfold kernel
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap (joint_integrable beta U f hf B hb)]
  simp_rw [he]
  simp only [integral_const,probReal_univ,one_smul]

/-- The constructed invariant ground function solves the unaveraged equation too. -/
theorem ground_raw_eigen {beta : ℝ} (d : GroundData beta) (U : State) :
    (∫ V, weight beta U V 1*d.function V ∂boundaryHaar)=d.value*d.function U := by
  rw [← integral_projected_eq_raw beta d.function d.measurable d.upper
    (fun V => (d.bounds V).2) d.invariant U]
  exact d.eigen U

/-- Literal ground-transform agreement on the bounded measurable physical core.
This alone is not an operator-norm estimate or an arbitrary-domain extension. -/
theorem transfer_on_invariants {beta : ℝ} (d : GroundData beta) (f : State → ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ V, |f V| ≤ B)
    (hInv : ∀ a V, f (gaugeAction a V) = f V) (U : State) :
    transfer d f U=(∫ V, weight beta U V 1*(d.function V*f V) ∂boundaryHaar)/
      (d.value*d.function U) := by
  unfold transfer
  rw [d.transition_integral]
  rw [integral_projected_eq_raw beta (fun V => d.function V*f V) (d.measurable.mul hf)
    (|d.upper| *|B|) (fun V => by
      rw [abs_mul]
      exact mul_le_mul ((d.bounds V).2.trans (le_abs_self _))
        ((hb V).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
    (fun a V => by rw [d.invariant,hInv]) U]

end OperatorDerivativeRewrite.Foundation.CubeInvariantTransfer
