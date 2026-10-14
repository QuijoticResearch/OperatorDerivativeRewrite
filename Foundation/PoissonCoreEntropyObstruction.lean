import Foundation.PoissonJumpCurvature
import Foundation.PoissonGraphApprox
import Foundation.BochnerL2Dominated
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The quadratic entropy obstruction survives legitimate finite-support core approximation. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonCoreEntropyObstruction
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonTruncation PoissonTruncationConvergence PoissonExponentialEntropy

theorem cut_integral_tendsto (rate : ℝ≥0) (g : ℕ → ℝ) (hg : Integrable g (poissonLaw rate)) :
    Tendsto (fun N => ∫ n, cut g N n ∂poissonLaw rate) atTop (𝓝 (∫ n, g n ∂poissonLaw rate)) := by
  apply tendsto_integral_of_dominated_convergence (fun n => ‖g n‖)
  · intro N; exact (measurable_of_countable _).aestronglyMeasurable
  · exact hg.norm
  · intro N
    exact Eventually.of_forall fun n => by by_cases hn : n<N <;> simp [cut,hn]
  · exact Eventually.of_forall fun n => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (n+1)] with N hN
      simp [cut,show n<N by omega]

theorem entropy_cut_tendsto (rate : ℝ≥0) (f : ℕ → ℝ)
    (h2 : Integrable (fun n => (f n)^2) (poissonLaw rate))
    (he : Integrable (fun n => (f n)^2*Real.log ((f n)^2)) (poissonLaw rate))
    (hm : 0<∫ n, (f n)^2 ∂poissonLaw rate) :
    Tendsto (fun N => entropySq (poissonLaw rate) (cut f N)) atTop
      (𝓝 (entropySq (poissonLaw rate) f)) := by
  have hs : ∀ N n, (cut f N n)^2=cut (fun n => (f n)^2) N n := by
    intro N n; by_cases hn : n<N <;> simp [cut,hn]
  have hl : ∀ N n, (cut f N n)^2*Real.log ((cut f N n)^2)=
      cut (fun n => (f n)^2*Real.log ((f n)^2)) N n := by
    intro N n; by_cases hn : n<N <;> simp [cut,hn]
  have hmass := cut_integral_tendsto rate (fun n => (f n)^2) h2
  have hent := cut_integral_tendsto rate (fun n => (f n)^2*Real.log ((f n)^2)) he
  have hlog := (Real.continuousAt_log (ne_of_gt hm)).tendsto.comp hmass
  unfold entropySq
  simp_rw [hl,hs]
  exact hent.sub (hmass.mul hlog)

theorem scalar_cut_entropy_tendsto (rate : ℝ≥0) (f : ScalarL2 rate)
    (he : Integrable (fun n => (f n)^2*Real.log ((f n)^2)) (poissonLaw rate)) (hf : f≠0) :
    Tendsto (fun N => entropySq (poissonLaw rate) (truncate (fun n => f n) (N+1))) atTop
      (𝓝 (entropySq (poissonLaw rate) (fun n => f n))) := by
  have h2 : Integrable (fun n => (f n)^2) (poissonLaw rate) := by
    simpa only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs] using L2.integrable_inner (𝕜 := ℝ) f f
  have hm : (∫ n, (f n)^2 ∂poissonLaw rate)=‖f‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using (BochnerL2Dominated.norm_sq_integral f).symm
  have hp : 0<∫ n, (f n)^2 ∂poissonLaw rate := by rw [hm]; exact sq_pos_of_pos (norm_pos_iff.mpr hf)
  have ht := (entropy_cut_tendsto rate (fun n => f n) h2 he hp).comp (tendsto_add_atTop_nat 1)
  have hcut (N : ℕ) : (truncate (fun n => f n) (N+1) : ℕ → ℝ)=cut (fun n => f n) (N+1) := by
    funext n; rfl
  simp_rw [hcut]
  exact ht

theorem finite_core_entropy_counterexample (rate : ℝ≥0) (hr : 0<rate) (C : ℝ) (hC : 0≤C) :
    ∃ f : ℕ →₀ ℝ,
      C*‖fieldFinsupp rate (finsuppDifference f)‖^2<entropySq (poissonLaw rate) f := by
  obtain ⟨f,g,hD,he,hfail⟩ := actual_entropy_counterexample rate hr C hC
  have hf : f≠0 := by
    intro hz
    have hae : (fun n => f n)=ᵐ[poissonLaw rate] fun _ => (0 : ℝ) := by
      rw [hz]; exact Lp.coeFn_zero ℝ 2 (poissonLaw rate)
    rw [entropySq_congr hae] at hfail
    simp only [entropySq,zero_pow (by norm_num : (2 : ℕ)≠0),zero_mul,integral_zero,mul_zero,sub_zero] at hfail
    exact (not_lt_of_ge (mul_nonneg hC (sq_nonneg ‖g‖))) hfail
  have hfD : f∈(maximalDifference rate hr).domain := LinearPMap.mem_domain_iff.mpr ⟨g,hD⟩
  have hout := difference_output_tendsto rate hr f hfD
  have hg : (maximalDifference rate hr) ⟨f,hfD⟩=g :=
    (maximalDifference rate hr).mem_graph_snd_inj ((maximalDifference rate hr).mem_graph ⟨f,hfD⟩) hD rfl
  rw [hg] at hout
  have hent := scalar_cut_entropy_tendsto rate f he hf
  have hlim := hent.sub ((hout.norm.pow 2).const_mul C)
  have hp : 0<entropySq (poissonLaw rate) (fun n => f n)-C*‖g‖^2 := by linarith
  have hpos := hlim.eventually (eventually_gt_nhds hp)
  obtain ⟨N,hN⟩ := hpos.exists
  refine ⟨truncate (fun n => f n) (N+1), ?_⟩
  linarith

theorem finite_core_actual_graph_counterexample (rate : ℝ≥0) (hr : 0<rate) (C : ℝ) (hC : 0≤C) :
    ∃ f : ℕ →₀ ℝ,
      (scalarFinsupp rate f,fieldFinsupp rate (finsuppDifference f))∈(coreDifference rate hr).graph ∧
      (fieldFinsupp rate (finsuppDifference f),scalarFinsupp rate (finsuppDivergence rate (finsuppDifference f)))
        ∈(coreDivergence rate hr).graph ∧
      C*‖fieldFinsupp rate (finsuppDifference f)‖^2<entropySq (poissonLaw rate) f := by
  obtain ⟨f,hf⟩ := finite_core_entropy_counterexample rate hr C hC
  exact ⟨f,coreDifference_finsupp_graph rate hr f,
    coreDivergence_finsupp_graph rate hr (finsuppDifference f),hf⟩

end OperatorDerivativeRewrite.Foundation.PoissonCoreEntropyObstruction


