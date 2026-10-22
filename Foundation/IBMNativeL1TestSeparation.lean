import Foundation.IBMUniformBoundedNativeTests

/-! Bounded original-domain tests separate actual observable L1 densities. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeL1TestSeparation
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMObservableHorizonLimit
open IBMUniformBoundedNativeTests IBMConditionalL1Realization
set_option backward.isDefEq.respectTransparency false

theorem integral_zero_on_bounded_observable (a : IBMSourceLaws.JointSample → ℝ)
    (ha : Integrable a IBMSourceLaws.jointMeasure)
    (h : ∀ v : jointDerivative.domain,
      (∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((v : IntrinsicSpace) : JointL2) ω)| ≤ 1) →
      (∫ ω, (((v : IntrinsicSpace) : JointL2) ω) * a ω ∂IBMSourceLaws.jointMeasure) = 0)
    (F : IntrinsicSpace) (hF : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(F : JointL2) ω| ≤ 1) :
    (∫ ω, (F : JointL2) ω * a ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  obtain ⟨u,hu,ht⟩ := uniformly_bounded_approximation F hF
  obtain ⟨ns,_,hae⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hb (n : ℕ) : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      ‖(((u (ns n) : IntrinsicSpace) : JointL2) ω) * a ω‖ ≤ |a ω| := by
    filter_upwards [hu (ns n)] with ω hv
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_right hv (abs_nonneg _)).trans_eq (one_mul _)
  have hl : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      Tendsto (fun n => (((u (ns n) : IntrinsicSpace) : JointL2) ω) * a ω) atTop
        (𝓝 ((F : JointL2) ω * a ω)) := by
    filter_upwards [hae] with ω hω
    exact hω.mul_const (a ω)
  have hi := tendsto_integral_of_dominated_convergence (fun ω => |a ω|)
    (fun n => (Lp.aestronglyMeasurable ((u (ns n) : IntrinsicSpace) : JointL2)).mul ha.aestronglyMeasurable)
    ha.abs hb hl
  have he (n : ℕ) : (∫ ω, (((u (ns n) : IntrinsicSpace) : JointL2) ω) * a ω
      ∂IBMSourceLaws.jointMeasure) = 0 := h _ (hu _)
  have hz : Tendsto (fun n => ∫ ω, (((u (ns n) : IntrinsicSpace) : JointL2) ω) * a ω
      ∂IBMSourceLaws.jointMeasure) atTop (𝓝 (0 : ℝ)) := by
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hi hz

theorem signum_mul_self (x : ℝ) : BrownianSignIntegral.signum x * x = |x| := by
  rcases lt_trichotomy 0 x with hx | hx | hx
  · simp [BrownianSignIntegral.signum,hx,abs_of_pos hx]
  · subst x
    simp [BrownianSignIntegral.signum]
  · simp [BrownianSignIntegral.signum,hx,not_lt_of_gt hx,abs_of_neg hx]

theorem sign_observable (a : IBMSourceLaws.JointSample → ℝ)
    (ha : AEStronglyMeasurable[observationSigma] a IBMSourceLaws.jointMeasure) :
    ∃ F : IntrinsicSpace,
      ((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => BrownianSignIntegral.signum (a ω)) ∧
      ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(F : JointL2) ω| ≤ 1 := by
  have hs0 : StronglyMeasurable[observationSigma]
      (fun ω => BrownianSignIntegral.signum (ha.mk a ω)) :=
    (BrownianSignIntegral.signum_measurable.comp ha.stronglyMeasurable_mk.measurable).stronglyMeasurable
  have hs : AEStronglyMeasurable[observationSigma]
      (fun ω => BrownianSignIntegral.signum (a ω)) IBMSourceLaws.jointMeasure :=
    hs0.aestronglyMeasurable.congr (ha.ae_eq_mk.fun_comp BrownianSignIntegral.signum).symm
  have hp : MemLp (fun ω => BrownianSignIntegral.signum (a ω)) 2 IBMSourceLaws.jointMeasure :=
    MemLp.of_bound (hs.mono observation_le) 1 (ae_of_all _ fun ω => BrownianSignIntegral.signum_bound _)
  let F : IntrinsicSpace := ⟨hp.toLp _,hs.congr hp.coeFn_toLp.symm⟩
  have hF : (F : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => BrownianSignIntegral.signum (a ω) := hp.coeFn_toLp
  refine ⟨F,hF,?_⟩
  filter_upwards [hF] with ω hω
  rw [hω,← Real.norm_eq_abs]
  exact BrownianSignIntegral.signum_bound _

theorem annihilator_zero (a : IBMSourceLaws.JointSample → ℝ)
    (ha : Integrable a IBMSourceLaws.jointMeasure)
    (hm : AEStronglyMeasurable[observationSigma] a IBMSourceLaws.jointMeasure)
    (h : ∀ v : jointDerivative.domain,
      (∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((v : IntrinsicSpace) : JointL2) ω)| ≤ 1) →
      (∫ ω, (((v : IntrinsicSpace) : JointL2) ω) * a ω ∂IBMSourceLaws.jointMeasure) = 0) :
    a =ᵐ[IBMSourceLaws.jointMeasure] 0 := by
  obtain ⟨F,hF,hb⟩ := sign_observable a hm
  have hz := integral_zero_on_bounded_observable a ha h F hb
  have he : (fun ω => (F : JointL2) ω * a ω) =ᵐ[IBMSourceLaws.jointMeasure] fun ω => |a ω| := by
    filter_upwards [hF] with ω hω
    rw [hω,signum_mul_self]
  have hi : (∫ ω, |a ω| ∂IBMSourceLaws.jointMeasure) = 0 := (integral_congr_ae he).symm.trans hz
  have he0 := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun ω => abs_nonneg (a ω)) ha.abs).mp hi
  filter_upwards [he0] with ω hω
  change |a ω| = 0 at hω
  change a ω = 0
  exact abs_eq_zero.mp hω

end OperatorDerivativeRewrite.Foundation.IBMNativeL1TestSeparation
