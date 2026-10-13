import Foundation.FractionalGaussianProcess
import Foundation.GaussianConditionalGraph

/-! Quantitative lower bounds for actual conditional predictions of fractional
Gaussian terminal coordinates. A Gaussian L² derivative alone does not justify
the manuscript's higher-order conditional-prediction remainder estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalPredictionObstruction
open InfiniteGaussian GaussianConditionalGraph FractionalGaussianProcess
open FractionalSpectralKernel FractionalSpectralGeometry SeparableHilbertEmbedding
attribute [local instance] spectralSpace_secondCountable
variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

def pastDirections (t : ℝ≥0) (r : Set.Iic t) : CoefficientSpace := direction H hH0 hH1 r

def forecast (t : ℝ≥0) : GaussianL2 :=
  conditionalProjection (pastDirections H hH0 hH1 t) (value H hH0 hH1 1)

theorem forecast_condExp (t : ℝ≥0) :
    forecast H hH0 hH1 t =ᵐ[gaussianProduct]
      gaussianProduct[value H hH0 hH1 1 |
        MeasurableSpace.comap (firstChaosFamily (pastDirections H hH0 hH1 t)) inferInstance] :=
  conditionalProjection_ae_condExp _ _

theorem current_mem_generated (t : ℝ≥0) :
    value H hH0 hH1 t ∈ generated (pastDirections H hH0 hH1 t) := by
  have he : familyPolynomialEmbedding (pastDirections H hH0 hH1 t)
      (MvPolynomial.X (⟨t, by simp⟩ : Set.Iic t)) = value H hH0 hH1 t := by
    apply Lp.ext
    simpa [familyPolynomialEmbedding, isonormalCylinder, MvPolynomial.eval_X,
      pastDirections, value] using
      isonormalCylinderL2_coeFn (pastDirections H hH0 hH1 t)
        (MvPolynomial.X (⟨t, by simp⟩ : Set.Iic t))
  rw [← he]
  exact familyPolynomial_aestronglyMeasurable _ _

theorem forecast_pairing (t : ℝ≥0) :
    inner ℝ (forecast H hH0 hH1 t) (value H hH0 hH1 t) =
      FractionalSpectralGeometry.covariance H 1 t := by
  have he := (generated (pastDirections H hH0 hH1 t)).starProjection_inner_eq_zero
    (value H hH0 hH1 1) (value H hH0 hH1 t) (current_mem_generated H hH0 hH1 t)
  rw [inner_sub_left] at he
  have hv : inner ℝ (value H hH0 hH1 1) (value H hH0 hH1 t) =
      FractionalSpectralGeometry.covariance H 1 t := by
    rw [value, value, firstChaosEmbedding.inner_map_map]
    change inner ℝ (hilbertEmbedding SpectralSpace _) (hilbertEmbedding SpectralSpace _) = _
    rw [(hilbertEmbedding SpectralSpace).inner_map_map, normalized_inner]
    rfl
  change inner ℝ (value H hH0 hH1 1) (value H hH0 hH1 t) -
    inner ℝ (forecast H hH0 hH1 t) (value H hH0 hH1 t) = 0 at he
  linarith

theorem terminal_covariance_lower (hpos : 0 < H) (t : ℝ≥0) (ht : t ≤ 1) :
    (t:ℝ)^(2*H) / 2 ≤ FractionalSpectralGeometry.covariance H 1 t := by
  have hp : (1-(t:ℝ))^(2*H) ≤ 1 :=
    Real.rpow_le_one (by exact sub_nonneg.mpr ht) (by linarith [t.coe_nonneg]) (by positivity)
  unfold FractionalSpectralGeometry.covariance
  rw [abs_one, Real.one_rpow, abs_of_nonneg t.coe_nonneg,
    abs_of_nonpos (sub_nonpos.mpr (show (t:ℝ) ≤ 1 from ht)), neg_sub]
  linarith

/-- Actual conditional predictions have at least this variance at small times. -/
theorem forecast_norm_sq_lower (t : ℝ≥0) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (t:ℝ)^(2*H) / 4 ≤ ‖forecast H hH0 hH1 t‖ ^ 2 := by
  have hr : 0 < (t:ℝ)^(2*H) := Real.rpow_pos_of_pos ht0 _
  have hl := terminal_covariance_lower H hH0 t ht1
  have hc := real_inner_le_norm (forecast H hH0 hH1 t) (value H hH0 hH1 t)
  rw [forecast_pairing] at hc
  have hnorm : ‖value H hH0 hH1 t‖^2 = (t:ℝ)^(2*H) := by
    rw [value, firstChaosEmbedding.norm_map]
    simp only [direction, (hilbertEmbedding SpectralSpace).norm_map, normalized_norm_sq,
      abs_of_nonneg t.coe_nonneg]
  have hs : ((t:ℝ)^(2*H)/2)^2 ≤
      (‖forecast H hH0 hH1 t‖ * ‖value H hH0 hH1 t‖)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (hl.trans hc)
  rw [mul_pow, hnorm] at hs
  nlinarith

/-- No uniform higher-order power bound is possible, even on an arbitrarily
small positive time interval. This is a quantitative theorem, not asymptotic notation. -/
theorem no_higher_power_bound (α : ℝ) (hα : 2*H < α) (C δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ≥0, 0 < t ∧ (t:ℝ) < δ ∧ t ≤ 1 ∧
      C * (t:ℝ)^α < ‖forecast H hH0 hH1 t‖^2 := by
  have hc : Continuous (fun x : ℝ => C * x^(α-2*H)) :=
    continuous_const.mul (Real.continuous_rpow_const (by linarith))
  have ht : Tendsto (fun x : ℝ => C * x^(α-2*H)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0) := by
    simpa [Real.zero_rpow (by linarith : α-2*H ≠ 0)] using (hc.tendsto (0:ℝ)).mono_left (show nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhds (0:ℝ) from inf_le_left)
  have hsmall := ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4))
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x := self_mem_nhdsWithin
  have hδ' : ∀ᶠ x : ℝ in 𝓝[>] 0, x < δ :=
    (eventually_lt_nhds hδ).filter_mono inf_le_left
  have hone : ∀ᶠ x : ℝ in 𝓝[>] 0, x < 1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono inf_le_left
  obtain ⟨x, hxp, hxd, hx1, hxc⟩ := (hpos.and (hδ'.and (hone.and hsmall))).exists
  refine ⟨⟨x, hxp.le⟩, hxp, hxd, hx1.le, ?_⟩
  have hr : 0 < x^(2*H) := Real.rpow_pos_of_pos hxp _
  have hm := mul_lt_mul_of_pos_right hxc hr
  have he : x^(α-2*H) * x^(2*H) = x^α := by
    rw [← Real.rpow_add hxp, sub_add_cancel]
  rw [mul_assoc, he] at hm
  have hl := forecast_norm_sq_lower H hH0 hH1 ⟨x, hxp.le⟩ hxp hx1.le
  change x^(2*H)/4 ≤ _ at hl
  exact hm.trans_le (by nlinarith)


theorem pastDirections_zero (r : Set.Iic (0 : ℝ≥0)) : pastDirections H hH0 hH1 0 r = 0 := by
  have hr : (r : ℝ≥0) = 0 := le_antisymm r.property (by positivity)
  simp [pastDirections, hr, direction, normalized_zero]

theorem zero_past_polynomial_constant (p : MvPolynomial (Set.Iic (0 : ℝ≥0)) ℝ) :
    familyPolynomialEmbedding (pastDirections H hH0 hH1 0) p =
      MvPolynomial.eval (fun _ => 0) p • gaussianOne := by
  apply Lp.ext
  filter_upwards [isonormalCylinderL2_coeFn (pastDirections H hH0 hH1 0) p,
    Lp.coeFn_smul (MvPolynomial.eval (fun _ => (0:ℝ)) p) gaussianOne,
    gaussianOne_coeFn, (Lp.coeFn_zero ℝ 2 gaussianProduct)] with ω hp hs ho hz
  change isonormalCylinderL2 _ p ω = _ at hp ⊢
  rw [hp, hs]
  simp only [Pi.smul_apply, smul_eq_mul, ho, mul_one]
  simp only [isonormalCylinder, pastDirections_zero, map_zero, hz, Pi.zero_apply]

theorem forecast_zero : forecast H hH0 hH1 0 = 0 := by
  have hker : generated (pastDirections H hH0 hH1 0) ≤
      (innerSL ℝ (value H hH0 hH1 1)).ker := by
    rw [generated, ← familyPolynomial_closure]
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨p, rfl⟩
      change inner ℝ (value H hH0 hH1 1) (familyPolynomialEmbedding _ p) = 0
      rw [zero_past_polynomial_constant, inner_smul_right, real_inner_comm,
        gaussianOne_inner_eq_integral]
      change _ * (∫ ω, process H hH0 hH1 1 ω ∂gaussianProduct) = 0
      rw [process_centered, mul_zero]
    · exact (innerSL ℝ (value H hH0 hH1 1)).isClosed_ker
  change (generated _).starProjection _ = 0
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  simpa only [sub_zero] using (show inner ℝ (value H hH0 hH1 1) w = 0 from hker hw)

/-- The actual prediction increments at the initial time admit no power-square
bound above 2H. This concerns a genuine conditional expectation, not arbitrary data. -/
theorem no_higher_prediction_increment_bound (α : ℝ) (hα : 2*H < α)
    (C δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ≥0, 0 < t ∧ (t:ℝ) < δ ∧ t ≤ 1 ∧
      C * (t:ℝ)^α < ‖forecast H hH0 hH1 t - forecast H hH0 hH1 0‖^2 := by
  simpa only [forecast_zero, sub_zero] using no_higher_power_bound H hH0 hH1 α hα C δ hδ
end OperatorDerivativeRewrite.Foundation.FractionalPredictionObstruction
