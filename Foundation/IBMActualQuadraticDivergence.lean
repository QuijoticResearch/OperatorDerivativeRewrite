import Foundation.IBMActualTaylorChain

/-! Divergence of actual IBM quadratic variation and the compensating raw
first Taylor channel. These are physical uniform-grid sums, not clock sums. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMActualQuadraticDivergence
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMUniformQuarticFamily IBMUniformQuarticVariation IBMUniformFifthRemainder
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

def quadratic (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (ibmValue (grid (T / (n + 1)) (i + 1)) ω -
    ibmValue (grid (T / (n + 1)) i) ω)^2

def first (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), 2 * ibmValue (grid (T / (n + 1)) i) ω *
    (ibmValue (grid (T / (n + 1)) (i + 1)) ω -
      ibmValue (grid (T / (n + 1)) i) ω)

theorem quadratic_nonneg (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    0 ≤ quadratic T n ω := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem quadratic_measurable (T : ℝ≥0) (n : ℕ) : Measurable (quadratic T n) := by
  apply Finset.measurable_sum
  intro i hi
  exact ((ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)).sub
    (ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id))).pow_const 2

theorem first_measurable (T : ℝ≥0) (n : ℕ) : Measurable (first T n) := by
  have hm (r : ℝ≥0) : Measurable (ibmValue r) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  apply Finset.measurable_sum
  intro i hi
  exact ((hm _).const_mul 2).mul ((hm _).sub (hm _))

theorem quartic_le (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    quartic T (n + 1) ω ≤ (mesh T n ω)^2 * quadratic T n ω := by
  rw [quartic, quadratic, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hd : |ibmValue (grid (T / (n + 1)) (i + 1)) ω -
      ibmValue (grid (T / (n + 1)) i) ω| ≤ mesh T n ω :=
    Finset.le_sup' (fun k => |ibmValue (grid (T / (n + 1)) (k + 1)) ω -
      ibmValue (grid (T / (n + 1)) k) ω|) hi
  have hsq := mul_self_le_mul_self (abs_nonneg _) hd
  rw [← sq, ← sq, sq_abs] at hsq
  have h := mul_le_mul_of_nonneg_right hsq (sq_nonneg
    (ibmValue (grid (T / (n + 1)) (i + 1)) ω -
      ibmValue (grid (T / (n + 1)) i) ω))
  simpa only [IBMUniformQuarticFamily.segment, Nat.cast_add, Nat.cast_one, ← pow_add] using h

theorem first_identity (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    first T n ω + quadratic T n ω =
      (ibmValue T ω)^2 - (ibmValue 0 ω)^2 := by
  have hs : first T n ω + quadratic T n ω =
      ∑ i ∈ Finset.range (n + 1),
        ((ibmValue (grid (T / (n + 1)) (i + 1)) ω)^2 -
          (ibmValue (grid (T / (n + 1)) i) ω)^2) := by
    rw [first, quadratic, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs]
  have ht := Finset.sum_range_sub
    (fun i => (ibmValue (grid (T / (n + 1)) i) ω)^2) (n + 1)
  rw [ht]
  have hend : grid (T / (n + 1)) (n + 1) = T := by
    unfold grid
    push_cast
    exact div_mul_cancel₀ T (by positivity)
  rw [hend]
  simp [grid]

theorem quadratic_channels_identity (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    IBMActualTaylorChain.channels (fun z => z^2) T n ω =
      first T n ω + quadratic T n ω := by
  unfold IBMActualTaylorChain.channels first quadratic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  norm_num [IBMFourthPeano.lower, iteratedDeriv_pow]

def reciprocal (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  1 / (quadratic T n ω + 1)

theorem reciprocal_measurable (T : ℝ≥0) (n : ℕ) : Measurable (reciprocal T n) :=
  measurable_const.div ((quadratic_measurable T n).add_const 1)

/-- Along any samplewise positive quartic-limit sequence, quadratic variation
escapes to infinity. This deterministic implication uses the actual mesh. -/
theorem reciprocal_tendsto_of_quartic (T : ℝ≥0) (ω : JointSample)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) {c : ℝ} (hc : 0 < c)
    (hq : Tendsto (fun j => quartic T (ns j + 1) ω) atTop (𝓝 c)) :
    Tendsto (fun j => reciprocal T (ns j) ω) atTop (𝓝 0) := by
  have hm := ((mesh_tendsto T ω).comp hns).pow 2
  have hbound : ∀ᶠ j in atTop,
      reciprocal T (ns j) ω ≤ (mesh T (ns j) ω)^2 / (c / 2) := by
    filter_upwards [hq.eventually (lt_mem_nhds (by linarith : c / 2 < c))] with j hj
    unfold reciprocal
    apply (div_le_div_iff₀ (by linarith [quadratic_nonneg T (ns j) ω])
      (by positivity : 0 < c / 2)).mpr
    nlinarith [quartic_le T (ns j) ω, sq_nonneg (mesh T (ns j) ω)]
  apply squeeze_zero' (Eventually.of_forall fun j => by
    unfold reciprocal
    exact one_div_nonneg.mpr (by linarith [quadratic_nonneg T (ns j) ω])) hbound
  simpa using hm.div_const (c / 2)

theorem reciprocal_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (reciprocal T) atTop (fun _ => (0 : ℝ)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (reciprocal_measurable T n).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, hq⟩ :=
    ((quartic_tendstoInMeasure hT).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hq] with ω hω
  apply reciprocal_tendsto_of_quartic T ω (ns ∘ ms) (hns.comp hms).tendsto_atTop
    (c := 3 * (T : ℝ)) (mul_pos (by norm_num) (NNReal.coe_pos.mpr hT))
  simpa only [Function.comp_def] using hω

/-- Quadratic variation tends to positive infinity in probability: every
fixed real lower-tail threshold has probability tending to zero. -/
theorem quadratic_lower_tail {T : ℝ≥0} (hT : 0 < T) (K : ℝ) :
    Tendsto (fun n => jointMeasure.real {ω | quadratic T n ω ≤ K})
      atTop (𝓝 0) := by
  have h := tendstoInMeasure_iff_measureReal_norm.mp (reciprocal_tendstoInMeasure hT)
  have hp : 0 < 1 / (|K| + 1) := by positivity
  have hb (n : ℕ) : jointMeasure.real {ω | quadratic T n ω ≤ K} ≤
      jointMeasure.real {ω | 1 / (|K| + 1) ≤ |reciprocal T n ω|} := by
    apply measureReal_mono (μ := jointMeasure) (h₂ := measure_ne_top _ _)
    intro ω hω
    have he : 1 / (|K| + 1) ≤ reciprocal T n ω := by
      unfold reciprocal
      apply one_div_le_one_div_of_le (by linarith [quadratic_nonneg T n ω])
      have hk := hω.trans (le_abs_self K)
      linarith
    exact he.trans (le_abs_self _)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [sub_zero, Real.norm_eq_abs] using h _ hp

theorem quadratic_no_path_limit (T : ℝ≥0) (ω : JointSample)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) {c : ℝ} (hc : 0 < c)
    (hq : Tendsto (fun j => quartic T (ns j + 1) ω) atTop (𝓝 c)) (y : ℝ) :
    ¬Tendsto (fun j => quadratic T (ns j) ω) atTop (𝓝 y) := by
  intro hy
  have hy0 : 0 ≤ y := ge_of_tendsto hy (Eventually.of_forall fun j =>
    quadratic_nonneg T (ns j) ω)
  have hr : Tendsto (fun j => reciprocal T (ns j) ω) atTop (𝓝 (1 / (y + 1))) :=
    tendsto_const_nhds.div (hy.add_const 1) (by linarith)
  have he := tendsto_nhds_unique hr (reciprocal_tendsto_of_quartic T ω ns hns hc hq)
  exact (ne_of_gt (one_div_pos.mpr (by linarith : 0 < y + 1))) he

/-- No finite real random variable can be the probability limit of the actual
quadratic sums, even with no proposed-limit measurability assumption. -/
theorem quadratic_no_finite_limit {T : ℝ≥0} (hT : 0 < T) (Y : JointSample → ℝ) :
    ¬TendstoInMeasure jointMeasure (quadratic T) atTop Y := by
  intro hy
  obtain ⟨ns, hns, hY⟩ := hy.exists_seq_tendsto_ae
  obtain ⟨ms, hms, hQ⟩ :=
    ((quartic_tendstoInMeasure hT).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  have hf : ∀ᵐ ω ∂jointMeasure, False := by
    filter_upwards [hY, hQ] with ω hω hq
    apply quadratic_no_path_limit T ω (ns ∘ ms) (hns.comp hms).tendsto_atTop
      (c := 3 * (T : ℝ)) (mul_pos (by norm_num) (NNReal.coe_pos.mpr hT))
      (by simpa only [Function.comp_def] using hq) (Y ω)
    exact hω.comp hms.tendsto_atTop
  obtain ⟨ω, hω⟩ := hf.exists
  exact hω

/-- The raw first-rank Taylor sum for f(z)=z^2 cannot converge to a finite
random variable either. Its divergent quadratic compensation is essential. -/
theorem first_no_finite_limit {T : ℝ≥0} (hT : 0 < T) (Y : JointSample → ℝ) :
    ¬TendstoInMeasure jointMeasure (first T) atTop Y := by
  intro hy
  obtain ⟨ns, hns, hY⟩ := hy.exists_seq_tendsto_ae
  obtain ⟨ms, hms, hQ⟩ :=
    ((quartic_tendstoInMeasure hT).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  have hf : ∀ᵐ ω ∂jointMeasure, False := by
    filter_upwards [hY, hQ] with ω hω hq
    apply quadratic_no_path_limit T ω (ns ∘ ms) (hns.comp hms).tendsto_atTop
      (c := 3 * (T : ℝ)) (mul_pos (by norm_num) (NNReal.coe_pos.mpr hT))
      (by simpa only [Function.comp_def] using hq)
      ((ibmValue T ω)^2 - (ibmValue 0 ω)^2 - Y ω)
    have he (j : ℕ) : quadratic T (ns (ms j)) ω =
        (ibmValue T ω)^2 - (ibmValue 0 ω)^2 - first T (ns (ms j)) ω := by
      linarith [first_identity T (ns (ms j)) ω]
    simpa only [Function.comp_def, he] using
      (tendsto_const_nhds.sub (hω.comp hms.tendsto_atTop))
  obtain ⟨ω, hω⟩ := hf.exists
  exact hω

end OperatorDerivativeRewrite.Foundation.IBMActualQuadraticDivergence
