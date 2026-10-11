import Foundation.PoissonTruncationConvergence

/-! Graph-norm truncation and exact closure of the one-site Poisson operators. -/

noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonTruncationConvergence
open PoissonTruncation PoissonDifferenceCore PoissonDifferenceOperators
open PoissonMaximalOperators PoissonWeightedDomains

/-- A truncated divergence is the cutoff of the full divergence plus one incoming boundary atom. -/
theorem divergence_truncate_decomposition (rate : ℝ≥0) (u : ℕ → ℝ) (N : ℕ) :
    finsuppDivergence rate (truncate u (N + 1)) =
      truncate (maximalDivergenceExpr rate u) (N + 1) +
        Finsupp.single (N + 1) ((N + 1 : ℝ) * u N) := by
  ext n
  simp only [finsuppDivergence_apply, Finsupp.add_apply, truncate_apply]
  by_cases hlt : n < N + 1
  · have hne : N + 1 ≠ n := by omega
    rw [divergence_truncate_interior rate u N n (by omega)]
    simp [hlt, hne, maximalDivergenceExpr]
  by_cases heq : n = N + 1
  · subst n
    rw [divergence_truncate_boundary]
    simp
  · have hgt : N + 1 < n := by omega
    rw [divergence_truncate_tail rate u N n hgt]
    simp [hlt, heq]

/-- Squared norm of one scalar count atom. -/
theorem scalar_single_norm_sq (rate : ℝ≥0) (N : ℕ) (c : ℝ) :
    ‖scalarFinsupp rate (Finsupp.single N c)‖ ^ 2 =
      poissonWeight rate N * c ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, scalarFinsupp_inner]
  have hi : Integrable (fun n => (Finsupp.single N c) n * (Finsupp.single N c) n)
      (poissonLaw rate) :=
    mul_L2_integrable (finsupp_memLp_two rate _) (finsupp_memLp_two rate _)
  rw [integral_eq_weighted_tsum rate _ hi, tsum_eq_single N]
  · simp [pow_two]
  · intro n hn
    simp [hn]

/-- Squared norm of one weighted field atom. -/
theorem field_single_norm_sq (rate : ℝ≥0) (N : ℕ) (c : ℝ) :
    ‖fieldFinsupp rate (Finsupp.single N c)‖ ^ 2 =
      (rate : ℝ) * poissonWeight rate N * c ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, fieldFinsupp_inner]
  have hi : Integrable (fun n => (Finsupp.single N c) n * (Finsupp.single N c) n)
      (poissonLaw rate) :=
    mul_L2_integrable (finsupp_memLp_two rate _) (finsupp_memLp_two rate _)
  rw [integral_eq_weighted_tsum rate _ hi, tsum_eq_single N]
  · simp [pow_two, mul_assoc]
  · intro n hn
    simp [hn]
/-- The outgoing scalar cutoff atom vanishes in the weighted field Hilbert norm. -/
theorem difference_boundary_tendsto_zero (rate : ℝ≥0) (f : ScalarL2 rate) :
    Tendsto (fun N => fieldFinsupp rate (Finsupp.single N (-f N)))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs : Tendsto
      (fun N => ‖fieldFinsupp rate (Finsupp.single N (-f N))‖ ^ 2)
      atTop (𝓝 0) := by
    simp_rw [field_single_norm_sq]
    convert (scalar_boundary_sq_tendsto_zero rate f).const_mul (rate : ℝ) using 1 <;>
      simp [mul_assoc]
  have hh := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hh

/-- The incoming divergence cutoff atom vanishes in the scalar Hilbert norm. -/
theorem divergence_boundary_tendsto_zero (rate : ℝ≥0) (hr : 0 < rate)
    (u : FieldL2 rate) (hu : u ∈ (maximalDivergence rate hr).domain) :
    Tendsto (fun N => scalarFinsupp rate
      (Finsupp.single (N + 1) ((N + 1 : ℝ) * u N))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs : Tendsto
      (fun N => ‖scalarFinsupp rate
        (Finsupp.single (N + 1) ((N + 1 : ℝ) * u N))‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [scalar_single_norm_sq] using
      divergence_boundary_sq_tendsto_zero rate hr u hu
  have hh := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hh

/-- The finite-support difference output splits into the maximal cutoff
 and one boundary atom. -/
theorem difference_truncated_output (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain) (N : ℕ) :
    fieldFinsupp rate (finsuppDifference (truncate (fun n => f n) (N + 1))) =
      fieldFinsupp rate (truncate
        (fun n => ((maximalDifference rate hr) ⟨f, hf⟩) n) N) +
        fieldFinsupp rate (Finsupp.single N (-f N)) := by
  have hg := (maximalDifference rate hr).mem_graph ⟨f, hf⟩
  rw [maximalDifference_graph] at hg
  have he : truncate (fun n => f (n + 1) - f n) N =
      truncate (fun n => ((maximalDifference rate hr) ⟨f, hf⟩) n) N := by
    ext n
    simp only [truncate_apply]
    by_cases hn : n < N <;> simp [hn, (hg n).symm]
  rw [difference_truncate_decomposition, he]
  exact (fieldEmbedding rate).map_add _ _

/-- The finite-support divergence output splits into the maximal cutoff
 and one incoming boundary atom. -/
theorem divergence_truncated_output (rate : ℝ≥0) (hr : 0 < rate)
    (u : FieldL2 rate) (hu : u ∈ (maximalDivergence rate hr).domain) (N : ℕ) :
    scalarFinsupp rate (finsuppDivergence rate (truncate (fun n => u n) (N + 1))) =
      scalarFinsupp rate (truncate
        (fun n => ((maximalDivergence rate hr) ⟨u, hu⟩) n) (N + 1)) +
        scalarFinsupp rate (Finsupp.single (N + 1) ((N + 1 : ℝ) * u N)) := by
  have hg := (maximalDivergence rate hr).mem_graph ⟨u, hu⟩
  rw [maximalDivergence_graph] at hg
  have he : truncate (maximalDivergenceExpr rate (fun n => u n)) (N + 1) =
      truncate (fun n => ((maximalDivergence rate hr) ⟨u, hu⟩) n) (N + 1) := by
    ext n
    simp only [truncate_apply]
    by_cases hn : n < N + 1 <;> simp [hn, (hg n).symm]
  rw [divergence_truncate_decomposition, he]
  exact (scalarEmbedding rate).map_add _ _

/-- Genuine L² graph-output convergence for the maximal Poisson difference. -/
theorem difference_output_tendsto (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain) :
    Tendsto (fun N => fieldFinsupp rate
      (finsuppDifference (truncate (fun n => f n) (N + 1)))) atTop
      (𝓝 ((maximalDifference rate hr) ⟨f, hf⟩)) := by
  have hc := field_truncate_tendsto rate ((maximalDifference rate hr) ⟨f, hf⟩)
  have hb := difference_boundary_tendsto_zero rate f
  have hs := hc.add hb
  simpa only [← difference_truncated_output rate hr f hf, add_zero] using hs

/-- Genuine L² graph-output convergence for the maximal Poisson divergence. -/
theorem divergence_output_tendsto (rate : ℝ≥0) (hr : 0 < rate)
    (u : FieldL2 rate) (hu : u ∈ (maximalDivergence rate hr).domain) :
    Tendsto (fun N => scalarFinsupp rate
      (finsuppDivergence rate (truncate (fun n => u n) (N + 1)))) atTop
      (𝓝 ((maximalDivergence rate hr) ⟨u, hu⟩)) := by
  have hc := (scalar_truncate_tendsto rate
    ((maximalDivergence rate hr) ⟨u, hu⟩)).comp (tendsto_add_atTop_nat 1)
  have hb := divergence_boundary_tendsto_zero rate hr u hu
  have hs := hc.add hb
  simpa only [Function.comp_def, ← divergence_truncated_output rate hr u hu, add_zero] using hs

/-- Every maximal-difference graph pair is a limit of finite-support graph pairs. -/
theorem maximalDifference_mem_coreClosure (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain) :
    (f, (maximalDifference rate hr) ⟨f, hf⟩) ∈
      (coreDifference rate hr).graph.topologicalClosure := by
  have hx := (scalar_truncate_tendsto rate f).comp (tendsto_add_atTop_nat 1)
  have hy := difference_output_tendsto rate hr f hf
  have hp := hx.prodMk hy
  change _ ∈ (↑((coreDifference rate hr).graph.topologicalClosure) :
    Set (ScalarL2 rate × FieldL2 rate))
  rw [Submodule.topologicalClosure_coe]
  apply mem_closure_of_tendsto (by simpa only [nhds_prod_eq] using hp)
  filter_upwards [] with N
  exact coreDifference_finsupp_graph rate hr (truncate (fun n => f n) (N + 1))

/-- Every maximal-divergence graph pair is a limit of finite-support graph pairs. -/
theorem maximalDivergence_mem_coreClosure (rate : ℝ≥0) (hr : 0 < rate)
    (u : FieldL2 rate) (hu : u ∈ (maximalDivergence rate hr).domain) :
    (u, (maximalDivergence rate hr) ⟨u, hu⟩) ∈
      (coreDivergence rate hr).graph.topologicalClosure := by
  have hx := (field_truncate_tendsto rate u).comp (tendsto_add_atTop_nat 1)
  have hy := divergence_output_tendsto rate hr u hu
  have hp := hx.prodMk hy
  change _ ∈ (↑((coreDivergence rate hr).graph.topologicalClosure) :
    Set (FieldL2 rate × ScalarL2 rate))
  rw [Submodule.topologicalClosure_coe]
  apply mem_closure_of_tendsto (by simpa only [nhds_prod_eq] using hp)
  filter_upwards [] with N
  exact coreDivergence_finsupp_graph rate hr (truncate (fun n => u n) (N + 1))

/-- Finite-support differences are a graph core for the closed maximal difference. -/
theorem closure_coreDifference_eq_maximal (rate : ℝ≥0) (hr : 0 < rate) :
    (coreDifference rate hr).closure = maximalDifference rate hr := by
  apply le_antisymm
  · exact OperatorDerivativeRewrite.Foundation.operatorClosure_le_closed
      (coreDifference_isClosable rate hr) (maximalDifference_isClosed rate hr)
      (coreDifference_le_maximal rate hr)
  · apply LinearPMap.le_of_le_graph
    intro z hz
    obtain ⟨f, g⟩ := z
    have hf : f ∈ (maximalDifference rate hr).domain :=
      LinearPMap.mem_domain_of_mem_graph hz
    have he : g = (maximalDifference rate hr) ⟨f, hf⟩ :=
      (maximalDifference rate hr).mem_graph_snd_inj hz
        ((maximalDifference rate hr).mem_graph ⟨f, hf⟩) rfl
    rw [he, ← (coreDifference_isClosable rate hr).graph_closure_eq_closure_graph]
    exact maximalDifference_mem_coreClosure rate hr f hf

/-- Finite-support divergences are a graph core for the closed maximal divergence. -/
theorem closure_coreDivergence_eq_maximal (rate : ℝ≥0) (hr : 0 < rate) :
    (coreDivergence rate hr).closure = maximalDivergence rate hr := by
  apply le_antisymm
  · exact OperatorDerivativeRewrite.Foundation.operatorClosure_le_closed
      (coreDivergence_isClosable rate hr) (maximalDivergence_isClosed rate hr)
      (coreDivergence_le_maximal rate hr)
  · apply LinearPMap.le_of_le_graph
    intro z hz
    obtain ⟨u, g⟩ := z
    have hu : u ∈ (maximalDivergence rate hr).domain :=
      LinearPMap.mem_domain_of_mem_graph hz
    have he : g = (maximalDivergence rate hr) ⟨u, hu⟩ :=
      (maximalDivergence rate hr).mem_graph_snd_inj hz
        ((maximalDivergence rate hr).mem_graph ⟨u, hu⟩) rfl
    rw [he, ← (coreDivergence_isClosable rate hr).graph_closure_eq_closure_graph]
    exact maximalDivergence_mem_coreClosure rate hr u hu
end OperatorDerivativeRewrite.Foundation.PoissonTruncationConvergence
