import Foundation.IBMFirstSourceClockGraph
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Group.Quotient
import Foundation.HilbertAdjointDomainDensity
import Foundation.BochnerL2RepresentativeFubini

/-! Actual graph integration for the joint partial clock derivative of IBM
time averages. Both Bochner integrability hypotheses are established first. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockAverageGraph
open InfiniteGaussian IBMFirstSourceClockGraph IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
attribute [local irreducible] IBMConstructedSources.clockPath scalarTensor IBMFirstSourceClockGraph.flip
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem signedSourceClass_jointly_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (fun p : ℝ × SampleSpace => signedSourceClass n p.1.toNNReal p.2) := by
  have hs := BrownianSignIntegral.signum_measurable.comp BrownianClockWeightedEnergy.sigma_measurable
  have hc := (IBMClockAverageCandidate.sourceColumn_continuous n).stronglyMeasurable.comp_measurable
    (continuous_abs.measurable.comp BrownianClockWeightedEnergy.sigma_measurable)
  exact hs.stronglyMeasurable.smul hc

theorem signedSource_time_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (fun t : ℝ => signedSource n t.toNNReal) := by
  let g : ℝ × SampleSpace → GaussianL2 := fun p => signedSourceClass n p.1.toNNReal p.2
  have hs := ProductL2Sections.sectionL2_stronglyMeasurable gaussianProduct g
    (signedSourceClass_jointly_stronglyMeasurable n)
  have he (t : ℝ) : ProductL2Sections.sectionL2 gaussianProduct g t = signedSource n t.toNNReal := by
    apply Lp.ext
    exact (ProductL2Sections.sectionL2_coeFn gaussianProduct g t
      (signedSourceClass_memLp n t.toNNReal)).trans (signedSource_ae n t.toNNReal).symm
  have hefun := funext he
  rw [hefun] at hs
  exact hs

def gradientBilinear : CoefficientSpace →L[ℝ] ScalarSpace →L[ℝ] VectorSpace :=
  IBMClockAverageCandidate.tensorBilinear.compLpL₂ 2 gaussianProduct

theorem gradientBilinear_eq (h : CoefficientSpace) (u : ScalarSpace) :
    gradientBilinear h u = gradientMap h u := rfl

theorem clockGradient_time_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (fun t : ℝ => clockGradient n t.toNNReal) := by
  have hb : Continuous (fun p : CoefficientSpace × ScalarSpace => gradientMap p.1 p.2) := by
    simp_rw [← gradientBilinear_eq]
    exact (gradientBilinear.continuous.comp continuous_fst).clm_apply continuous_snd
  have hd : StronglyMeasurable (fun t : ℝ => IBMClockAverageCandidate.direction t) :=
    IBMClockAverageCandidate.direction_continuous.stronglyMeasurable
  have hw := IBMFirstSourceClockGraph.flip.continuous.comp_stronglyMeasurable
    (signedSource_time_stronglyMeasurable n)
  have ht := hb.comp_stronglyMeasurable (hd.prodMk hw)
  have he (t : ℝ) : IBMClockAverageCandidate.direction (t.toNNReal : ℝ) =
      IBMClockAverageCandidate.direction t := by
    unfold IBMClockAverageCandidate.direction
    rw [Real.toNNReal_coe]
  simpa only [clockGradient, he] using ht

theorem clockGradient_integrable (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun t : ℝ => clockGradient n t.toNNReal) (window T) := by
  obtain ⟨C, hC, hb⟩ := IBMClockAverageCandidate.sourceColumn_bounded n
  apply Integrable.of_bound (clockGradient_time_stronglyMeasurable n).aestronglyMeasurable
    (C * Real.sqrt T)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [clockGradient_norm]
  have he : (t.toNNReal : ℝ) = t := Real.coe_toNNReal _ ht.1.le
  rw [he]
  exact (IBMClockAverageCandidate.field_norm_bound n hC hb t).trans
    (mul_le_mul_of_nonneg_left (IBMClockAverageCandidate.direction_norm_bound hT ht) hC)

def averageGradient (n : ℕ) (T : ℝ) : VectorSpace :=
  ∫ t : ℝ, clockGradient n t.toNNReal ∂window T

/-- Genuine joint closed-clock-graph membership of the actual scalar average. -/
theorem mollified_average_clock_graph (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (IBMFirstSourceClockGraph.flip (IBMTimeAveragedObservable.mollifiedAverage n T),
      averageGradient n T) ∈
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph := by
  let S := (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph
  letI : IsClosed (S : Set (ScalarSpace × VectorSpace)) :=
    BochnerClosedOperator.lift_isClosed gaussianProduct closedCylindricalDerivative
      closedCylindricalDerivative_isClosed
  let f : ℝ → ScalarSpace × VectorSpace := fun t =>
    (IBMFirstSourceClockGraph.flip (IBMRandomTimeHilbert.randomMollifiedL2 n t.toNNReal),
      clockGradient n t.toNNReal)
  have hu : Integrable (fun t : ℝ => IBMFirstSourceClockGraph.flip
      (IBMRandomTimeHilbert.randomMollifiedL2 n t.toNNReal)) (window T) :=
    IBMFirstSourceClockGraph.flip.toContinuousLinearMap.integrable_comp
      (IBMTimeAveragedObservable.mollified_time_integrable n T)
  have hf : Integrable f (window T) := hu.prodMk (clockGradient_integrable n hT)
  have ha : ∀ᵐ t ∂window T, f t ∈ S := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mollified_clock_graph n t.toNNReal (Real.toNNReal_pos.mpr ht.1)
  have hq : S.mkQL (∫ t, f t ∂window T) = 0 := by
    rw [← S.mkQL.integral_comp_comm hf]
    apply integral_eq_zero_of_ae
    filter_upwards [ha] with t ht
    exact (Submodule.Quotient.mk_eq_zero S).mpr ht
  have hm : (∫ t, f t ∂window T) ∈ S := (Submodule.Quotient.mk_eq_zero S).mp hq
  rw [show (∫ t, f t ∂window T) =
      (∫ t : ℝ, IBMFirstSourceClockGraph.flip
        (IBMRandomTimeHilbert.randomMollifiedL2 n t.toNNReal) ∂window T,
       averageGradient n T) from integral_pair hu (clockGradient_integrable n hT)] at hm
  change (∫ t : ℝ, IBMFirstSourceClockGraph.flip.toContinuousLinearMap
      (IBMRandomTimeHilbert.randomMollifiedL2 n t.toNNReal) ∂window T,
    averageGradient n T) ∈ S at hm
  rw [IBMFirstSourceClockGraph.flip.toContinuousLinearMap.integral_comp_comm
    (IBMTimeAveragedObservable.mollified_time_integrable n T)] at hm
  exact hm

theorem averageGradient_inner (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    inner ℝ (averageGradient n T) (averageGradient m T) =
      inner ℝ (IBMClockAverageCandidate.average n T) (IBMClockAverageCandidate.average m T) := by
  rw [averageGradient, averageGradient, IBMClockAverageCandidate.average,
    IBMClockAverageCandidate.average, real_inner_comm,
    ← integral_inner (clockGradient_integrable n hT), real_inner_comm,
    ← integral_inner (IBMClockAverageCandidate.field_integrable n hT)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [real_inner_comm, ← integral_inner (clockGradient_integrable m hT),
    real_inner_comm, ← integral_inner (IBMClockAverageCandidate.field_integrable m hT)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [clockGradient_inner, Real.coe_toNNReal _ hs.1.le, Real.coe_toNNReal _ ht.1.le]

theorem averageGradient_norm (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖averageGradient n T‖ = ‖IBMClockAverageCandidate.average n T‖ := by
  have he := averageGradient_inner n n hT
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (averageGradient n T), norm_nonneg (IBMClockAverageCandidate.average n T)]

/-- The previous candidate estimate now bounds an ACTUAL closed-clock derivative. -/
theorem averageGradient_uniform_energy (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖averageGradient n T‖ ^ 2 ≤ 8 * IBMFoldedTransitionBound.peak 1 * T ^ 2 * Real.sqrt T := by
  rw [averageGradient_norm n hT]
  exact IBMClockAverageCandidate.average_uniform_energy n hT

abbrev clockDerivative := BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative

set_option maxHeartbeats 800000 in
/-- The actual closed clock domain is stable under strong scalar convergence
and a uniform bound on actual derivatives. No derivative convergence is assumed. -/
theorem clock_domain_of_bounded_graph_limit (u : ℕ → ScalarSpace) (v : ℕ → VectorSpace)
    (f : ScalarSpace) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ n, (u n, v n) ∈ clockDerivative.graph)
    (hu : Tendsto u atTop (𝓝 f)) (hv : ∀ n, ‖v n‖ ≤ C) :
    ∃ hf : f ∈ clockDerivative.domain, ‖clockDerivative ⟨f, hf⟩‖ ≤ C := by
  have hd := BochnerClosedOperator.lift_dense_domain gaussianProduct closedCylindricalDerivative
    closedCylindricalDerivative_dense_domain
  have hc := BochnerClosedOperator.lift_isClosed gaussianProduct closedCylindricalDerivative
    closedCylindricalDerivative_isClosed
  have ha := HilbertAdjointDomainDensity.closed_adjoint_dense clockDerivative hc hd
  let L : clockDerivative.adjoint.domain →ₗ[ℝ] ℝ :=
    (innerSL ℝ f).toLinearMap.comp clockDerivative.adjoint.toFun
  have hb (y : clockDerivative.adjoint.domain) :
      ‖inner ℝ f (clockDerivative.adjoint y)‖ ≤ C * ‖(y : VectorSpace)‖ := by
    have he (n : ℕ) : inner ℝ (u n) (clockDerivative.adjoint y) = inner ℝ (v n) (y : VectorSpace) := by
      have hn : u n ∈ clockDerivative.domain := LinearPMap.mem_domain_iff.mpr ⟨v n, hg n⟩
      have hval : clockDerivative ⟨u n, hn⟩ = v n :=
        clockDerivative.mem_graph_snd_inj (clockDerivative.mem_graph _) (hg n) rfl
      have hp := clockDerivative.adjoint_isFormalAdjoint hd y ⟨u n, hn⟩
      rw [hval] at hp
      calc
        inner ℝ (u n) (clockDerivative.adjoint y) = inner ℝ (clockDerivative.adjoint y) (u n) :=
          real_inner_comm _ _
        _ = inner ℝ (y : VectorSpace) (v n) := hp
        _ = inner ℝ (v n) (y : VectorSpace) := real_inner_comm _ _
    apply le_of_tendsto (hu.inner tendsto_const_nhds |>.norm)
    apply Eventually.of_forall
    intro n
    rw [he n]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hv n) (norm_nonneg _))
  have hL : Continuous L := (L.mkContinuous C (fun y => hb y)).continuous
  have hff : f ∈ clockDerivative.adjoint.adjoint.domain := by
    rw [clockDerivative.adjoint.mem_adjoint_domain_iff]
    exact hL
  rw [HilbertAdjointDomainDensity.closed_bidual clockDerivative hc hd] at hff
  refine ⟨hff, ?_⟩
  let z := clockDerivative ⟨f, hff⟩
  have hb' (y : clockDerivative.adjoint.domain) : ‖inner ℝ z (y : VectorSpace)‖ ≤ C * ‖(y : VectorSpace)‖ := by
    have he := clockDerivative.adjoint_isFormalAdjoint hd y ⟨f, hff⟩
    have hz : inner ℝ z (y : VectorSpace) = inner ℝ f (clockDerivative.adjoint y) := by
      calc
        inner ℝ z (y : VectorSpace) = inner ℝ (y : VectorSpace) z := real_inner_comm _ _
        _ = inner ℝ (clockDerivative.adjoint y) f := he.symm
        _ = inner ℝ f (clockDerivative.adjoint y) := real_inner_comm _ _
    rw [hz]
    exact hb y
  have hevery : ∀ y : VectorSpace, ‖inner ℝ z y‖ ≤ C * ‖y‖ := by
    have hs : IsClosed {y : VectorSpace | ‖inner ℝ z y‖ ≤ C * ‖y‖} :=
      isClosed_le (continuous_const.inner continuous_id).norm (continuous_const.mul continuous_norm)
    have hin : (clockDerivative.adjoint.domain : Set VectorSpace) ⊆ {y | ‖inner ℝ z y‖ ≤ C * ‖y‖} :=
      fun y hy => hb' ⟨y, hy⟩
    exact fun y => (closure_minimal hin hs) (ha y)
  have hz := hevery z
  rw [real_inner_self_eq_norm_sq, Real.norm_of_nonneg (sq_nonneg _)] at hz
  change ‖z‖ ≤ C
  nlinarith [norm_nonneg z]

/-- Unmollified IBM time averages genuinely belong to the joint partial clock
domain, with a derivative satisfying the same uniform energy estimate. -/
theorem source_average_clock_domain {T : ℝ} (hT : 0 ≤ T) :
    ∃ hf : IBMFirstSourceClockGraph.flip (IBMTimeAveragedObservable.sourceAverage T) ∈
        clockDerivative.domain,
      ‖clockDerivative ⟨_, hf⟩‖ ^ 2 ≤
        8 * IBMFoldedTransitionBound.peak 1 * T ^ 2 * Real.sqrt T := by
  let E := 8 * IBMFoldedTransitionBound.peak 1 * T ^ 2 * Real.sqrt T
  have hE : 0 ≤ E := (sq_nonneg ‖averageGradient 0 T‖).trans (averageGradient_uniform_energy 0 hT)
  have hv (n : ℕ) : ‖averageGradient n T‖ ≤ Real.sqrt E := by
    have he := averageGradient_uniform_energy n hT
    have hs := Real.sq_sqrt hE
    nlinarith [Real.sqrt_nonneg E, norm_nonneg (averageGradient n T)]
  obtain ⟨hf, hb⟩ := clock_domain_of_bounded_graph_limit
    (fun n => IBMFirstSourceClockGraph.flip (IBMTimeAveragedObservable.mollifiedAverage n T))
    (fun n => averageGradient n T)
    (IBMFirstSourceClockGraph.flip (IBMTimeAveragedObservable.sourceAverage T))
    (Real.sqrt E) (Real.sqrt_nonneg E) (fun n => mollified_average_clock_graph n hT)
    (IBMFirstSourceClockGraph.flip.continuous.continuousAt.tendsto.comp
      (IBMTimeAveragedObservable.average_tendsto hT)) hv
  refine ⟨hf, ?_⟩
  have hs := Real.sq_sqrt hE
  change ‖clockDerivative ⟨_, hf⟩‖ ^ 2 ≤ E
  nlinarith [norm_nonneg (clockDerivative ⟨_, hf⟩)]

theorem source_average_clock_graph {T : ℝ} (hT : 0 ≤ T) :
    ∃ G : VectorSpace,
      (IBMFirstSourceClockGraph.flip (IBMTimeAveragedObservable.sourceAverage T), G) ∈
        clockDerivative.graph ∧
      ‖G‖ ^ 2 ≤ 8 * IBMFoldedTransitionBound.peak 1 * T ^ 2 * Real.sqrt T := by
  obtain ⟨hf, hb⟩ := source_average_clock_domain hT
  exact ⟨clockDerivative ⟨_, hf⟩, clockDerivative.mem_graph ⟨_, hf⟩, hb⟩

/-- Explicit source-outside/clock-inside representation of the native,
intrinsically IBM-observable average already constructed in1087. -/
theorem nativeAverage_clock_representation (T : ℝ) :
    ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
        (IBMTimeAveragedObservable.nativeAverage T) =
      IBMFirstSourceClockGraph.flip (IBMTimeAveragedObservable.sourceAverage T) := by
  unfold IBMTimeAveragedObservable.nativeAverage IBMTimeAveragedObservable.jointRealization
    IBMFirstSourceClockGraph.flip ProductL2Curry.flip
  rfl

theorem nativeAverage_clock_domain {T : ℝ} (hT : 0 ≤ T) :
    ∃ hf : ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
        (IBMTimeAveragedObservable.nativeAverage T) ∈ clockDerivative.domain,
      ‖clockDerivative ⟨_, hf⟩‖ ^ 2 ≤
        8 * IBMFoldedTransitionBound.peak 1 * T ^ 2 * Real.sqrt T := by
  rw [nativeAverage_clock_representation]
  exact source_average_clock_domain hT

attribute [local irreducible] IBMConstructedSources.ibmValue
  IBMTimeAveragedObservable.jointRealization IBMTimeAveragedObservable.nativeAverage

set_option maxHeartbeats 800000 in
/-- The IBM-observable L2 average is the actual sample-path time integral
almost everywhere under the native joint source/clock law. -/
theorem nativeAverage_path_integral_ae (T : ℝ) :
    IBMTimeAveragedObservable.nativeAverage T =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => ∫ t : ℝ, IBMConstructedSources.ibmValue t.toNNReal ω ∂window T) := by
  let v : ℝ → IBMTimeAveragedObservable.JointL2 := fun t =>
    IBMTimeAveragedObservable.jointRealization.toContinuousLinearMap
      (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal)
  have hv : Integrable v (window T) :=
    IBMTimeAveragedObservable.jointRealization.toContinuousLinearMap.integrable_comp
      (IBMTimeAveragedObservable.source_time_integrable T)
  let g : ℝ × IBMSourceLaws.JointSample → ℝ :=
    fun p => IBMConstructedSources.ibmValue p.1.toNNReal p.2
  have hg : Measurable g := IBMConstructedSources.ibmValue_jointly_measurable.comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have he := BochnerL2RepresentativeFubini.integral_coeFn_ae v hv g hg.aestronglyMeasurable
    (ae_of_all (window T) fun t => IBMTimeAveragedObservable.joint_point_actual_ae t.toNNReal)
  have hn : (∫ t, v t ∂window T) = IBMTimeAveragedObservable.nativeAverage T := by
    unfold IBMTimeAveragedObservable.nativeAverage IBMTimeAveragedObservable.sourceAverage
    exact IBMTimeAveragedObservable.jointRealization.toContinuousLinearMap.integral_comp_comm
      (IBMTimeAveragedObservable.source_time_integrable T)
  rwa [hn] at he

end OperatorDerivativeRewrite.Foundation.IBMClockAverageGraph
