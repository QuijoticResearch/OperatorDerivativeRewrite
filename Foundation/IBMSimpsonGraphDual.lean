import Foundation.IBMActualSimpson
import Foundation.IBMActualSineDomainObstruction
import Foundation.IBMBoundedGermFactors
import Foundation.BochnerL2Approximation

/-! Genuine bounded Simpson approximants converge in observable L2 and in
the intrinsic graph dual, although their limit is outside the strong domain.
Clipping is explicit; no L2 convergence of the UNCLIPPED sums is asserted. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSimpsonGraphDual
open IBMSourceLaws IBMConstructedSources IBMTimeAveragedObservable
open IBMActualSineDomainObstruction IBMJointIntrinsicDerivative
open IBMActualSimpson IBMBoundedGermFactors
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    sceneryPath_measurable clockPath_measurable).completeSpace_coe

theorem sine_zero_ae : (fun ω => Real.sin (ibmValue 0 ω)) =ᵐ[jointMeasure]
    (fun _ => (0 : ℝ)) := by
  have hz : (sinePoint 0 : JointL2) = 0 := congrArg Subtype.val sinePoint_zero
  have h := sinePoint_actual_ae 0
  rw [hz] at h
  exact h.symm.trans (Lp.coeFn_zero ℝ 2 jointMeasure)

theorem cosine_sums_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (sums Real.cos T) atTop
      (fun ω => Real.sin (ibmValue T ω)) := by
  have h := derivative_sums_tendstoInMeasure Real.sin (by fun_prop) hT
  rw [Real.deriv_sin] at h
  refine h.congr (fun _ => ae_of_all _ fun _ => rfl) ?_
  filter_upwards [sine_zero_ae] with ω hω
  rw [hω, sub_zero]

def clipped (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  clamp 1 (sums Real.cos T n ω)

theorem clipped_bound (T : ℝ≥0) (n : ℕ) (ω : JointSample) : |clipped T n ω| ≤ 1 :=
  clamp_bound zero_le_one _

theorem clipped_measurable (T : ℝ≥0) (n : ℕ) : Measurable (clipped T n) :=
  (clamp_measurable 1).comp (sums_measurable Real.cos Real.continuous_cos T n)

theorem clipped_memLp (T : ℝ≥0) (n : ℕ) : MemLp (clipped T n) 2 jointMeasure :=
  MemLp.of_bound (clipped_measurable T n).aestronglyMeasurable 1
    (ae_of_all _ fun ω => clipped_bound T n ω)

theorem clipped_observable (T : ℝ≥0) (n : ℕ) :
    Measurable[IBMConditionalObservable.observableSigma sceneryPath clockPath] (clipped T n) := by
  have hm (r : ℝ≥0) : Measurable[
      IBMConditionalObservable.observableSigma sceneryPath clockPath] (ibmValue r) := by
    unfold IBMConditionalObservable.observableSigma IBMConstructedSources.ibmValue
    exact (measurable_pi_apply r).comp (comap_measurable
      (fun ω s => IBMContinuousComposition.value sceneryPath clockPath s ω))
  apply (clamp_measurable 1).comp
  unfold sums IBMSimpsonPeano.simpson
  apply Finset.measurable_sum
  intro i hi
  exact (((hm _).sub (hm _)).div_const 6).mul
    (((Real.continuous_cos.measurable.comp (hm _)).add
      ((Real.continuous_cos.measurable.comp (((hm _).add (hm _)).div_const 2)).const_mul 4)).add
        (Real.continuous_cos.measurable.comp (hm _)))

def valueClass (T : ℝ≥0) (n : ℕ) : JointL2 := (clipped_memLp T n).toLp (clipped T n)

theorem valueClass_actual_ae (T : ℝ≥0) (n : ℕ) :
    valueClass T n =ᵐ[jointMeasure] clipped T n := MemLp.coeFn_toLp _

def intrinsicValue (T : ℝ≥0) (n : ℕ) : IntrinsicSpace :=
  ⟨valueClass T n, ⟨clipped T n, (clipped_observable T n).stronglyMeasurable,
    valueClass_actual_ae T n⟩⟩

theorem intrinsicValue_actual_ae (T : ℝ≥0) (n : ℕ) :
    (intrinsicValue T n : JointL2) =ᵐ[jointMeasure] clipped T n := valueClass_actual_ae T n

theorem clipped_error_bound (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    |clipped T n ω - Real.sin (ibmValue T ω)| ≤
      |sums Real.cos T n ω - Real.sin (ibmValue T ω)| := by
  have hl : LipschitzWith 1 (clamp 1) :=
    (LipschitzWith.id.const_min 1).const_max (-1)
  have h := hl.dist_le_mul (sums Real.cos T n ω) (Real.sin (ibmValue T ω))
  rw [clamp_eq (Real.abs_sin_le_one _)] at h
  simpa only [clipped, Real.dist_eq, NNReal.coe_one, one_mul] using h

theorem clipped_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (clipped T) atTop
      (fun ω => Real.sin (ibmValue T ω)) := by
  have h := tendstoInMeasure_iff_measureReal_norm.mp (cosine_sums_tendstoInMeasure hT)
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  simp only [Real.norm_eq_abs]
  have hb (n : ℕ) :
      jointMeasure.real {ω | ε ≤ |clipped T n ω - Real.sin (ibmValue T ω)|} ≤
      jointMeasure.real {ω | ε ≤ |sums Real.cos T n ω - Real.sin (ibmValue T ω)|} := by
    apply measureReal_mono (μ := jointMeasure) (h₂ := measure_ne_top _ _)
    intro ω hω
    exact hω.trans (clipped_error_bound T n ω)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [Real.norm_eq_abs] using h ε hε

theorem valueClass_tendsto {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (valueClass T) atTop (𝓝 (sinePoint T : JointL2)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, hms, ht⟩ := ((clipped_tendstoInMeasure hT).comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply BochnerL2Approximation.tendsto_of_dominated _ (sinePoint T : JointL2)
    (Lp.const 2 jointMeasure (1 : ℝ))
  · intro j
    filter_upwards [valueClass_actual_ae T (ns (ms j)),
      Lp.coeFn_const (p := 2) (μ := jointMeasure) (c := (1 : ℝ))] with ω hv hc
    rw [hv, hc]
    simpa only [Real.norm_eq_abs, Function.const_apply, abs_one] using
      clipped_bound T (ns (ms j)) ω
  · filter_upwards [sinePoint_actual_ae T,
      Lp.coeFn_const (p := 2) (μ := jointMeasure) (c := (1 : ℝ))] with ω hv hc
    rw [hv, hc]
    simpa only [Real.norm_eq_abs, Function.const_apply, abs_one] using
      Real.abs_sin_le_one (ibmValue T ω)
  · filter_upwards [ae_all_iff.mpr (fun n => valueClass_actual_ae T n),
      sinePoint_actual_ae T, ht] with ω hv hs hω
    simpa only [hv, hs, Function.comp_def] using hω

theorem intrinsicValue_tendsto {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (intrinsicValue T) atTop (𝓝 (sinePoint T)) :=
  tendsto_subtype_rng.mpr (valueClass_tendsto hT)

theorem weakDerivative_tendsto {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n => IBMIntrinsicGraphDual.weakDerivative (intrinsicValue T n)) atTop
      (𝓝 (sineDerivative T)) :=
  (IBMIntrinsicGraphDual.weakDerivative.continuous.tendsto _).comp (intrinsicValue_tendsto hT)

attribute [local irreducible] intrinsicValue valueClass jointDerivative

theorem clipped_pairing_integrable (T : ℝ≥0) (n : ℕ) (v : jointDivergence.domain) :
    Integrable (fun ω => clipped T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω) jointMeasure :=
  IBMIntrinsicGraphDual.actual_pairing_integrable (intrinsicValue T n) (clipped T n)
    (intrinsicValue_actual_ae T n) v

/-- The actual bounded stochastic approximants converge against EVERY original
adjoint-domain test, identifying their graph-dual derivative limit. -/
theorem actual_pairing_tendsto {T : ℝ≥0} (hT : 0 < T) (v : jointDivergence.domain) :
    Tendsto (fun n => ∫ ω, clipped T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂jointMeasure) atTop
      (𝓝 (sineDerivative T (IBMIntrinsicGraphDual.testOf v))) := by
  have he : (fun n => ∫ ω, clipped T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂jointMeasure) =
      fun n => IBMIntrinsicGraphDual.weakDerivative (intrinsicValue T n)
        (IBMIntrinsicGraphDual.testOf v) := by
    funext n
    exact (IBMIntrinsicGraphDual.actual_pairing (intrinsicValue T n) (clipped T n)
      (intrinsicValue_actual_ae T n) v).symm
  have hp := ((ContinuousLinearMap.apply ℝ ℝ (IBMIntrinsicGraphDual.testOf v)).continuous.tendsto
    (sineDerivative T)).comp (weakDerivative_tendsto hT)
  exact hp.congr' (Eventually.of_forall fun n => (congrFun he n).symm)

/-- Even this bounded actual stochastic limit has no strong intrinsic joint
derivative field. The graph-dual limit is nonzero and not field-representable. -/
theorem limit_obstruction {T : ℝ≥0} (hT : 0 < T) :
    sinePoint T ∉ jointDerivative.domain ∧ sineDerivative T ≠ 0 ∧
      ¬∃ V : JointFieldSpace,
        IBMIntrinsicGraphDual.embed V = sineDerivative T :=
  ⟨sinePoint_not_joint_domain T hT, sineDerivative_ne_zero T hT,
    sineDerivative_not_representable T hT⟩

/-- Any strong-domain regularizations tracking the ACTUAL bounded stochastic
approximants converge in the graph dual, while their strong gradients escape. -/
theorem tracked_graph_escape {T : ℝ≥0} (hT : 0 < T)
    (u : ℕ → jointDerivative.domain)
    (htrack : Tendsto (fun n => ‖(u n : IntrinsicSpace) - intrinsicValue T n‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => IBMIntrinsicGraphDual.embed (jointDerivative (u n))) atTop
      (𝓝 (sineDerivative T)) ∧
    Tendsto (fun n => ‖jointDerivative (u n)‖) atTop atTop := by
  have hv := tendsto_iff_norm_sub_tendsto_zero.mp (intrinsicValue_tendsto hT)
  have hu : Tendsto (fun n => (u n : IntrinsicSpace)) atTop (𝓝 (sinePoint T)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => norm_sub_le_norm_sub_add_norm_sub (u n : IntrinsicSpace)
        (intrinsicValue T n) (sinePoint T))
    simpa only [add_zero] using htrack.add hv
  exact ⟨IBMIntrinsicGraphDual.graph_dual_limit (sinePoint T) u hu,
    sine_graph_norm_escape T hT u hu⟩

end OperatorDerivativeRewrite.Foundation.IBMSimpsonGraphDual
