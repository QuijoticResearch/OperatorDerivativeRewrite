import Foundation.SPDEWickBrownianPrediction

/-! Initial Hermite-rank scaling does not improve positive-time L2 roughness. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.SPDEWickTemporalGeometry
open InfiniteGaussian GaussianTimeSpaceHermite GaussianConditionalGraph GaussianWickConditionalProjection
open SPDEWickModes SPDEWickBrownianPrediction

theorem source_projection_between (s t : ℝ≥0) (hst : s≤t) (i : ℕ) :
    sourceProjection (pastDirections s) (brownianDirection i t)=brownianDirection i s := by
  apply sourceProjection_eq_of_pairings
  · exact (Submodule.span ℝ (Set.range (pastDirections s))).le_topologicalClosure
      (Submodule.subset_span ⟨(i,⟨s,by simp⟩),rfl⟩)
  · intro p
    rw [pastDirections,brownianDirection_inner,brownianDirection_inner]
    have hp : (p.2 : ℝ≥0)≤s := p.2.property
    simp only [min_eq_right hp,min_eq_right (hp.trans hst)]

theorem response_prediction_between (s t : ℝ≥0) (hst : s≤t) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2)) :
    conditionalProjection (pastDirections s) (response t d c)=response s d c := by
  have hp := (conditionalProjection (pastDirections s)).hasSum (response_hasSum t d hd c hs)
  simp only [map_smul,conditional_wick_projection,source_projection_between s t hst] at hp
  exact hp.unique (response_hasSum s d hd c hs)

theorem response_energy_scale (t : ℝ≥0) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2)) :
    ‖response t d c‖^2=(t : ℝ)^d*‖response 1 d c‖^2 := by
  have h1 := (response_energy_hasSum 1 d hd c hs).mul_left ((t : ℝ)^d)
  have he (i : ℕ) : (t : ℝ)^d*((c i)^2*(d.factorial : ℝ)*(1 : ℝ≥0)^d)=
      (c i)^2*(d.factorial : ℝ)*(t : ℝ)^d := by simp; ring
  simp_rw [he] at h1
  exact (response_energy_hasSum t d hd c hs).unique h1

theorem response_pairing (s t : ℝ≥0) (hst : s≤t) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2)) :
    inner ℝ (response t d c) (response s d c)=‖response s d c‖^2 := by
  have hm : response s d c∈generated (pastDirections s) := by
    rw [← response_prediction_between s t hst d hd c hs]
    exact (generated (pastDirections s)).starProjection_apply_mem _
  have he := (generated (pastDirections s)).starProjection_inner_eq_zero
    (response t d c) (response s d c) hm
  change inner ℝ (response t d c-conditionalProjection (pastDirections s) (response t d c)) (response s d c)=0 at he
  rw [inner_sub_left,response_prediction_between s t hst d hd c hs,
    real_inner_self_eq_norm_sq] at he
  linarith

theorem response_increment_energy (s t : ℝ≥0) (hst : s≤t) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2)) :
    ‖response t d c-response s d c‖^2=((t : ℝ)^d-(s : ℝ)^d)*‖response 1 d c‖^2 := by
  rw [norm_sub_sq_real,response_pairing s t hst d hd c hs,
    response_energy_scale t d hd c hs,response_energy_scale s d hd c hs]
  ring

theorem harmonic_terminal_energy_lower : 2≤‖response 1 2 harmonicCoefficient‖^2 := by
  have hs := response_energy_hasSum 1 2 (by norm_num) harmonicCoefficient harmonic_square_summable
  have hl := hs.summable.sum_le_tsum ({0} : Finset ℕ) (fun i hi => by positivity)
  rw [hs.tsum_eq] at hl
  norm_num [harmonicCoefficient] at hl
  exact hl

theorem harmonic_positive_time_increment_lower (h : ℝ≥0) :
    2*(h : ℝ)≤‖response ((1/2 : ℝ≥0)+h) 2 harmonicCoefficient-
      response (1/2) 2 harmonicCoefficient‖^2 := by
  rw [response_increment_energy (1/2) ((1/2 : ℝ≥0)+h) (by exact le_add_of_nonneg_right h.coe_nonneg)
    2 (by norm_num) harmonicCoefficient harmonic_square_summable]
  norm_num only [NNReal.coe_add,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
  have he := mul_le_mul_of_nonneg_left harmonic_terminal_energy_lower
    (show 0≤(1/2+(h : ℝ))^2-(1/2 : ℝ)^2 by nlinarith [h.coe_nonneg])
  nlinarith [h.coe_nonneg,sq_nonneg (h : ℝ)]

theorem no_higher_positive_time_power (α : ℝ) (hα : 1<α) (C δ : ℝ) (hδ : 0<δ) :
    ∃ h : ℝ≥0, 0<h ∧ (h : ℝ)<δ ∧ h≤1/2 ∧
      C*(h : ℝ)^α<‖response ((1/2 : ℝ≥0)+h) 2 harmonicCoefficient-
        response (1/2) 2 harmonicCoefficient‖^2 := by
  have hp : 0<α-1 := by linarith
  have hcont : Continuous (fun x : ℝ => C*x^(α-1)) :=
    continuous_const.mul (Real.continuous_rpow_const hp.le)
  have ht : Tendsto (fun x : ℝ => C*x^(α-1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Real.zero_rpow (ne_of_gt hp)] using
      (hcont.tendsto (0 : ℝ)).mono_left (show 𝓝[>] (0 : ℝ)≤𝓝 (0 : ℝ) from inf_le_left)
  have hsmall := ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<2))
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] 0, 0<x := self_mem_nhdsWithin
  have hδ' : ∀ᶠ x : ℝ in 𝓝[>] 0, x<δ := (eventually_lt_nhds hδ).filter_mono inf_le_left
  have hhalf : ∀ᶠ x : ℝ in 𝓝[>] 0, x<1/2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2)).filter_mono inf_le_left
  obtain ⟨x,hxp,hxd,hxh,hxc⟩ := (hpos.and (hδ'.and (hhalf.and hsmall))).exists
  refine ⟨⟨x,hxp.le⟩,hxp,hxd,hxh.le, ?_⟩
  have hm := mul_lt_mul_of_pos_right hxc hxp
  have he : x^(α-1)*x=x^α := by
    calc
      x^(α-1)*x=x^(α-1)*x^(1 : ℝ) := by rw [Real.rpow_one]
      _=x^α := by rw [← Real.rpow_add hxp,sub_add_cancel]
  rw [mul_assoc,he] at hm
  exact hm.trans_le (harmonic_positive_time_increment_lower ⟨x,hxp.le⟩)
end OperatorDerivativeRewrite.Foundation.SPDEWickTemporalGeometry



