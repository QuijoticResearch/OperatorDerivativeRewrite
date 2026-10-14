import Foundation.FractionalTerminalPredictionRank

/-! Both short-memory and persistent fractional covariance contributions
force actual nonlinear prediction obstructions through min(H,1-H). -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.FractionalDualRegimePrediction
open InfiniteGaussian GaussianSingleObservationPrediction GaussianTerminalPredictionSpectrum
open FractionalTerminalPredictionRank
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def predictionPower (H : ℝ) : ℝ := 2*min H (1-H)

theorem terminal_covariance_linear_lower (H : ℝ) (hH0 : 0<H) (t : ℝ≥0) (ht : t≤1) :
    (t : ℝ)/2 ≤ FractionalSpectralGeometry.covariance H 1 t := by
  by_cases ha : 2*H≤1
  · have hp := Real.self_le_rpow_of_le_one t.coe_nonneg (show (t : ℝ)≤1 from ht) ha
    have hl := FractionalPredictionObstruction.terminal_covariance_lower H hH0 t ht
    nlinarith
  · have hp : (1-(t : ℝ))^(2*H) ≤ 1-(t : ℝ) :=
      Real.rpow_le_self_of_le_one (by exact sub_nonneg.mpr ht)
        (by linarith [t.coe_nonneg]) (by linarith)
    unfold FractionalSpectralGeometry.covariance
    rw [abs_one,Real.one_rpow,abs_of_nonneg t.coe_nonneg,
      abs_of_nonpos (sub_nonpos.mpr (show (t : ℝ)≤1 from ht)),neg_sub]
    nlinarith [Real.rpow_nonneg t.coe_nonneg (2*H)]

theorem linear_forecast_persistent_lower (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (t : ℝ≥0) (ht0 : 0<t) (ht1 : t≤1) :
    (t : ℝ)^(2-2*H)/4 ≤ ‖FractionalPredictionObstruction.forecast H hH0 hH1 t‖^2 := by
  have hl := terminal_covariance_linear_lower H hH0 t ht1
  have hc := real_inner_le_norm (FractionalPredictionObstruction.forecast H hH0 hH1 t)
    (FractionalGaussianProcess.value H hH0 hH1 t)
  rw [FractionalPredictionObstruction.forecast_pairing] at hc
  have hn : ‖FractionalGaussianProcess.value H hH0 hH1 t‖^2=(t : ℝ)^(2*H) := by
    rw [FractionalGaussianProcess.value,firstChaosEmbedding.norm_map]
    simp only [FractionalGaussianProcess.direction,
      (SeparableHilbertEmbedding.hilbertEmbedding FractionalSpectralKernel.SpectralSpace).norm_map,
      FractionalSpectralGeometry.normalized_norm_sq,abs_of_nonneg t.coe_nonneg]
  have hs : ((t : ℝ)/2)^2 ≤
      (‖FractionalPredictionObstruction.forecast H hH0 hH1 t‖*
        ‖FractionalGaussianProcess.value H hH0 hH1 t‖)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (hl.trans hc)
  rw [mul_pow,hn] at hs
  have he : (t : ℝ)^(2-2*H)/4=(((t : ℝ)/2)^2)/(t : ℝ)^(2*H) := by
    rw [Real.rpow_sub (x := (t : ℝ)) ht0 2 (2*H),Real.rpow_two]
    ring
  rw [he]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos ht0 (2*H))).mpr hs

theorem linear_forecast_dual_lower (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (t : ℝ≥0) (ht0 : 0<t) (ht1 : t≤1) :
    (t : ℝ)^(predictionPower H)/4 ≤ ‖FractionalPredictionObstruction.forecast H hH0 hH1 t‖^2 := by
  by_cases h : H≤1-H
  · rw [predictionPower,min_eq_left h]
    exact FractionalPredictionObstruction.forecast_norm_sq_lower H hH0 hH1 t ht0 ht1
  · rw [predictionPower,min_eq_right (le_of_lt (lt_of_not_ge h)),show 2*(1-H)=2-2*H by ring]
    exact linear_forecast_persistent_lower H hH0 hH1 t ht0 ht1

theorem wick_forecast_dual_lower (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (t : ℝ≥0) (ht0 : 0<t) (ht1 : t≤1) (n : ℕ) :
    (n.factorial : ℝ)*(t : ℝ)^(predictionPower H*(n : ℝ))/(4 : ℝ)^n ≤
      ‖GaussianWickPredictionBound.Fractional.forecast H hH0 hH1 t n‖^2 := by
  rw [GaussianWickConditionalProjection.Fractional.forecast_energy_exact]
  have hp := pow_le_pow_left₀ (show 0≤(t : ℝ)^(predictionPower H)/4 by positivity)
    (linear_forecast_dual_lower H hH0 hH1 t ht0 ht1) n
  have he := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n.factorial)
  rw [div_pow,← Real.rpow_mul_natCast t.coe_nonneg] at he
  simpa only [mul_div_assoc] using he

theorem terminal_forecast_dual_lower (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (f : GaussianL2) (hf : f∈singleGenerated (terminalDirection H hH0 hH1))
    (t : ℝ≥0) (ht0 : 0<t) (ht1 : t≤1) (m : ℕ) :
    ((coefficient (terminalDirection H hH0 hH1) f m)^2*(m.factorial : ℝ)/(4 : ℝ)^m)*
      (t : ℝ)^(predictionPower H*(m : ℝ)) ≤ ‖forecast H hH0 hH1 f t‖^2 := by
  have hs := forecast_energy_hasSum H hH0 hH1 f hf t
  have ht := hs.summable.sum_le_tsum ({m} : Finset ℕ) (fun n hn => by positivity)
  simp only [Finset.sum_singleton,hs.tsum_eq] at ht
  have hp := pow_le_pow_left₀ (show 0≤(t : ℝ)^(predictionPower H)/4 by positivity)
    (linear_forecast_dual_lower H hH0 hH1 t ht0 ht1) m
  have he := (mul_le_mul_of_nonneg_left hp
    (show 0≤(coefficient (terminalDirection H hH0 hH1) f m)^2*(m.factorial : ℝ) by positivity)).trans ht
  rw [div_pow,← Real.rpow_mul_natCast t.coe_nonneg] at he
  calc
    _ = (coefficient (terminalDirection H hH0 hH1) f m)^2*(m.factorial : ℝ)*
      ((t : ℝ)^(predictionPower H*(m : ℝ))/(4 : ℝ)^m) := by ring
    _ ≤ _ := he

theorem no_higher_dual_prediction_increment_bound (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (f : GaussianL2) (hf : f∈singleGenerated (terminalDirection H hH0 hH1))
    (hc : coefficient (terminalDirection H hH0 hH1) f 0=0)
    (m : ℕ) (hcm : coefficient (terminalDirection H hH0 hH1) f m≠0)
    (α : ℝ) (hα : predictionPower H*(m : ℝ)<α) (C δ : ℝ) (hδ : 0<δ) :
    ∃ t : ℝ≥0, 0<t ∧ (t : ℝ)<δ ∧ t≤1 ∧
      C*(t : ℝ)^α < ‖forecast H hH0 hH1 f t-forecast H hH0 hH1 f 0‖^2 := by
  let β := predictionPower H*(m : ℝ)
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
  exact hm.trans_le (terminal_forecast_dual_lower H hH0 hH1 f hf ⟨x,hxp.le⟩ hxp hx1.le m)

theorem exists_positive_terminal_rank (H : ℝ) (hH0 : 0<H) (hH1 : H<1)
    (f : GaussianL2) (hf : f∈singleGenerated (terminalDirection H hH0 hH1))
    (hc : coefficient (terminalDirection H hH0 hH1) f 0=0) (hf0 : f≠0) :
    ∃ m : ℕ, 0<m ∧ coefficient (terminalDirection H hH0 hH1) f m≠0 ∧
      ∀ n<m, coefficient (terminalDirection H hH0 hH1) f n=0 := by
  classical
  have hex : ∃ n : ℕ, coefficient (terminalDirection H hH0 hH1) f n≠0 := by
    by_contra hno
    push_neg at hno
    have hs := terminal_expansion_hasSum (terminalDirection H hH0 hH1)
      (terminalDirection_unit H hH0 hH1) f hf
    simp_rw [hno,zero_smul] at hs
    exact hf0 (hs.unique hasSum_zero)
  refine ⟨Nat.find hex, ?_,Nat.find_spec hex, ?_⟩
  · apply Nat.pos_of_ne_zero
    intro hz
    have he := Nat.find_spec hex
    rw [hz,hc] at he
    exact he rfl
  · intro n hn
    exact not_not.mp (Nat.find_min hex hn)

end OperatorDerivativeRewrite.Foundation.FractionalDualRegimePrediction
