import Foundation.GaussianTerminalPredictionSpectrum

/-! Actual full-past fractional forecasts of arbitrary terminal L2 observables:
Hermite-rank energy bounds and small-time power obstructions. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.FractionalTerminalPredictionRank
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianSingleObservationPrediction GaussianTerminalPredictionSpectrum

def terminalDirection (H : ℝ) (hH0 : 0<H) (hH1 : H<1) : CoefficientSpace :=
  FractionalGaussianProcess.direction H hH0 hH1 1

theorem terminalDirection_unit (H : ℝ) (hH0 : 0<H) (hH1 : H<1) :
    ‖terminalDirection H hH0 hH1‖^2=1 := by
  rw [terminalDirection,← real_inner_self_eq_norm_sq,FractionalWickCovariance.direction_inner]
  simp [FractionalSpectralGeometry.covariance,show 2*H≠0 by positivity]

def forecast (H : ℝ) (hH0 : 0<H) (hH1 : H<1) (f : GaussianL2) (t : ℝ≥0) : GaussianL2 :=
  conditionalProjection (FractionalPredictionObstruction.pastDirections H hH0 hH1 t) f

theorem forecast_energy_hasSum (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (f : GaussianL2) (hf : f∈singleGenerated (terminalDirection H hH0 hH1)) (t : ℝ≥0) :
    HasSum (fun n => (coefficient (terminalDirection H hH0 hH1) f n)^2*(n.factorial : ℝ)*
      (‖FractionalPredictionObstruction.forecast H hH0 hH1 t‖^2)^n)
      (‖forecast H hH0 hH1 f t‖^2) := by
  have hs := terminal_prediction_energy_hasSum
    (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)
    (terminalDirection H hH0 hH1) (terminalDirection_unit H hH0 hH1) f hf
  have he := conditional_firstChaos_projection
    (FractionalPredictionObstruction.pastDirections H hH0 hH1 t) (terminalDirection H hH0 hH1)
  have hn := congrArg (fun x : GaussianL2 => ‖x‖^2) he
  rw [LinearIsometry.norm_map] at hn
  change ‖FractionalPredictionObstruction.forecast H hH0 hH1 t‖^2=_ at hn
  simpa only [← hn,forecast] using hs

theorem forecast_zero_of_centered (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (f : GaussianL2) (hf : f∈singleGenerated (terminalDirection H hH0 hH1))
    (hc : coefficient (terminalDirection H hH0 hH1) f 0=0) :
    forecast H hH0 hH1 f 0=0 := by
  have hs := forecast_energy_hasSum H hH0 hH1 f hf 0
  rw [FractionalPredictionObstruction.forecast_zero,norm_zero] at hs
  have hz (n : ℕ) : (coefficient (terminalDirection H hH0 hH1) f n)^2*(n.factorial : ℝ)*
      ((0 : ℝ)^2)^n=0 := by
    cases n <;> simp [hc]
  simp_rw [hz] at hs
  have he : (0 : ℝ)=‖forecast H hH0 hH1 f 0‖^2 := hasSum_zero.unique hs
  apply norm_eq_zero.mp
  nlinarith

theorem forecast_small_time_lower (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (f : GaussianL2) (hf : f∈singleGenerated (terminalDirection H hH0 hH1))
    (t : ℝ≥0) (ht : 0<t) (ht1 : t≤1) (m : ℕ) :
    ((coefficient (terminalDirection H hH0 hH1) f m)^2*(m.factorial : ℝ)/(4 : ℝ)^m)*
      (t : ℝ)^(2*H*(m : ℝ)) ≤ ‖forecast H hH0 hH1 f t‖^2 := by
  have hr := terminal_prediction_rank_lower
    (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)
    (terminalDirection H hH0 hH1) (terminalDirection_unit H hH0 hH1) f hf m
  have hw := conditional_wick_energy
    (FractionalPredictionObstruction.pastDirections H hH0 hH1 t) (terminalDirection H hH0 hH1) m
  have hl := GaussianWickPredictionBound.Fractional.forecast_small_time_lower H hH0 hH1 t ht ht1 m
  change (m.factorial : ℝ)*((t : ℝ)^(2*H))^m/(4 : ℝ)^m ≤
    ‖conditionalProjection _ (GaussianTimeSpaceHermite.wick (terminalDirection H hH0 hH1) m)‖^2 at hl
  rw [hw] at hl
  have he := mul_le_mul_of_nonneg_left hl (sq_nonneg (coefficient (terminalDirection H hH0 hH1) f m))
  rw [← Real.rpow_mul_natCast t.coe_nonneg] at he
  change _ ≤ ‖forecast H hH0 hH1 f t‖^2 at hr
  calc
    _ = (coefficient (terminalDirection H hH0 hH1) f m)^2*
      ((m.factorial : ℝ)*(t : ℝ)^(2*H*(m : ℝ))/(4 : ℝ)^m) := by ring
    _ ≤ _ := he
    _ = _ := by ring
    _ ≤ _ := hr

theorem no_higher_prediction_increment_bound (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (f : GaussianL2) (hf : f∈singleGenerated (terminalDirection H hH0 hH1))
    (hc : coefficient (terminalDirection H hH0 hH1) f 0=0)
    (m : ℕ) (hcm : coefficient (terminalDirection H hH0 hH1) f m≠0)
    (α : ℝ) (hα : 2*H*(m : ℝ)<α) (C δ : ℝ) (hδ : 0<δ) :
    ∃ t : ℝ≥0, 0<t ∧ (t : ℝ)<δ ∧ t≤1 ∧
      C*(t : ℝ)^α < ‖forecast H hH0 hH1 f t-forecast H hH0 hH1 f 0‖^2 := by
  let β := 2*H*(m : ℝ)
  let K := (coefficient (terminalDirection H hH0 hH1) f m)^2*(m.factorial : ℝ)/(4 : ℝ)^m
  have hK : 0<K := by
    have hp := sq_pos_of_ne_zero hcm
    dsimp [K]
    positivity
  have hdiff : 0<α-β := by dsimp [β]; linarith
  have hcont : Continuous (fun x : ℝ => C*x^(α-β)) :=
    continuous_const.mul (Real.continuous_rpow_const hdiff.le)
  have ht : Tendsto (fun x : ℝ => C*x^(α-β)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Real.zero_rpow (ne_of_gt hdiff)] using
      (hcont.tendsto (0 : ℝ)).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  have hsmall := ht.eventually (eventually_lt_nhds hK)
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] 0, 0<x := self_mem_nhdsWithin
  have hδ' : ∀ᶠ x : ℝ in 𝓝[>] 0, x<δ := (eventually_lt_nhds hδ).filter_mono inf_le_left
  have hone : ∀ᶠ x : ℝ in 𝓝[>] 0, x<1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono inf_le_left
  obtain ⟨x,hxp,hxd,hx1,hxc⟩ := (hpos.and (hδ'.and (hone.and hsmall))).exists
  refine ⟨⟨x,hxp.le⟩,hxp,hxd,hx1.le, ?_⟩
  have hm := mul_lt_mul_of_pos_right hxc (Real.rpow_pos_of_pos hxp β)
  have he : x^(α-β)*x^β=x^α := by rw [← Real.rpow_add hxp,sub_add_cancel]
  rw [mul_assoc,he] at hm
  rw [forecast_zero_of_centered H hH0 hH1 f hf hc,sub_zero]
  exact hm.trans_le (forecast_small_time_lower H hH0 hH1 f hf ⟨x,hxp.le⟩ hxp hx1.le m)

end OperatorDerivativeRewrite.Foundation.FractionalTerminalPredictionRank
