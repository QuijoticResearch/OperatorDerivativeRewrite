import Foundation.FractionalWickCovariance
import Foundation.FractionalPredictionObstruction

/-! Nonlinear Gaussian prediction lower bounds from one observed Wick
coordinate, without independence or invertible observation covariance. -/
noncomputable section
open MeasureTheory
open scoped NNReal
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.GaussianWickPredictionBound
open InfiniteGaussian GaussianTimeSpaceHermite GaussianConditionalGraph

theorem observed_wick_mem {I : Type*} (h : I → CoefficientSpace) (i : I) (n : ℕ) :
    (wick (h i) n : GaussianL2) ∈ generated h := by
  let p := MvPolynomial.rename (fun _ : Unit => i) (polynomial (‖h i‖^2) n)
  have he : familyPolynomialEmbedding h p = (wick (h i) n : GaussianL2) := by
    apply Lp.ext
    filter_upwards [isonormalCylinderL2_coeFn h p,
      core_coeFn (h i) (‖h i‖^2) n] with ω hp hw
    change isonormalCylinderL2 h p ω = (core (h i) (‖h i‖^2) n : GaussianL2) ω
    rw [hp, hw]
    simp [p, isonormalCylinder, value, MvPolynomial.eval_rename, Function.comp_def]
  rw [← he]
  exact familyPolynomial_aestronglyMeasurable h p

theorem forecast_wick_pairing {I : Type*} (h : I → CoefficientSpace) (i : I)
    (u : CoefficientSpace) (n : ℕ) :
    inner ℝ (conditionalProjection h (wick u n)) (wick (h i) n : GaussianL2) =
      (n.factorial : ℝ)*(inner ℝ u (h i))^n := by
  have he := (generated h).starProjection_inner_eq_zero (wick u n)
    (wick (h i) n) (observed_wick_mem h i n)
  rw [inner_sub_left, wick_inner, if_pos rfl] at he
  change (n.factorial : ℝ)*(inner ℝ u (h i))^n -
    inner ℝ (conditionalProjection h (wick u n)) (wick (h i) n : GaussianL2) = 0 at he
  linarith

/-- Quantitative prediction from one observed coordinate. The denominator
has not been divided out, so zero observation directions are also allowed. -/
theorem forecast_wick_energy_lower {I : Type*} (h : I → CoefficientSpace) (i : I)
    (u : CoefficientSpace) (n : ℕ) :
    ((n.factorial : ℝ)*(inner ℝ u (h i))^n)^2 ≤
      ‖conditionalProjection h (wick u n)‖^2 *
        ((n.factorial : ℝ)*(‖h i‖^2)^n) := by
  have hc := abs_real_inner_le_norm (conditionalProjection h (wick u n))
    (wick (h i) n : GaussianL2)
  rw [forecast_wick_pairing] at hc
  have he := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hc
  simp only [sq_abs, mul_pow] at he
  have hn : ‖(wick (h i) n : GaussianL2)‖^2 =
      (n.factorial : ℝ)*(‖h i‖^2)^n := by
    rw [← real_inner_self_eq_norm_sq, wick_inner, if_pos rfl, real_inner_self_eq_norm_sq]
  rw [hn] at he
  simpa only [mul_pow] using he

namespace Fractional
open FractionalWickCovariance FractionalPredictionObstruction FractionalGaussianProcess
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def forecast (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ≥0) (n : ℕ) : GaussianL2 :=
  conditionalProjection (pastDirections H hH0 hH1 t) (cylinder H hH0 hH1 1 n)

theorem forecast_covariance_lower (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (t : ℝ≥0) (n : ℕ) :
    ((n.factorial : ℝ)*(FractionalSpectralGeometry.covariance H 1 t)^n)^2 ≤
      ‖forecast H hH0 hH1 t n‖^2 *
        ((n.factorial : ℝ)*((t : ℝ)^(2*H))^n) := by
  have h := forecast_wick_energy_lower (pastDirections H hH0 hH1 t)
    (⟨t, by simp⟩ : Set.Iic t) (direction H hH0 hH1 1) n
  have hn : ‖direction H hH0 hH1 t‖^2 = (t : ℝ)^(2*H) := by
    simp only [direction, (SeparableHilbertEmbedding.hilbertEmbedding
      FractionalSpectralKernel.SpectralSpace).norm_map, FractionalSpectralGeometry.normalized_norm_sq,
      abs_of_nonneg t.coe_nonneg]
  simp only [pastDirections] at h
  change ((n.factorial : ℝ)*(inner ℝ (direction H hH0 hH1 1)
      (direction H hH0 hH1 t))^n)^2 ≤ _ at h
  rw [direction_inner, hn] at h
  exact h

theorem forecast_norm_sq_lower (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    (n.factorial : ℝ)*
      ((FractionalSpectralGeometry.covariance H 1 t)^2 / (t : ℝ)^(2*H))^n ≤
        ‖forecast H hH0 hH1 t n‖^2 := by
  have h := forecast_covariance_lower H hH0 hH1 t n
  have hA : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hV : 0 < ((t : ℝ)^(2*H))^n := pow_pos (Real.rpow_pos_of_pos ht _) n
  simp only [mul_pow] at h
  have he : (n.factorial : ℝ)*((FractionalSpectralGeometry.covariance H 1 t)^n)^2 ≤
      ‖forecast H hH0 hH1 t n‖^2*((t : ℝ)^(2*H))^n := by
    apply (mul_le_mul_iff_right₀ hA).mp
    nlinarith [h]
  have hd := (div_le_iff₀ hV).mpr he
  simpa only [div_pow, mul_div_assoc, ← pow_mul, Nat.mul_comm] using hd

/-- Every Wick degree retains a quantitatively nonzero past prediction at
small times. The lower power is H times the chaos degree at the norm level. -/
theorem forecast_small_time_lower (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (t : ℝ≥0) (ht0 : 0 < t) (ht1 : t ≤ 1) (n : ℕ) :
    (n.factorial : ℝ)*((t : ℝ)^(2*H))^n/(4 : ℝ)^n ≤
      ‖forecast H hH0 hH1 t n‖^2 := by
  have hV : 0 < (t : ℝ)^(2*H) := Real.rpow_pos_of_pos ht0 _
  have hl := terminal_covariance_lower H hH0 t ht1
  have hc : 0 ≤ FractionalSpectralGeometry.covariance H 1 t := by linarith
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ (t : ℝ)^(2*H)/2) hc).mpr hl
  have hb : (t : ℝ)^(2*H)/4 ≤
      (FractionalSpectralGeometry.covariance H 1 t)^2/(t : ℝ)^(2*H) := by
    apply (le_div_iff₀ hV).mpr
    nlinarith [hs]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (t : ℝ)^(2*H)/4) hb n
  have he := (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n.factorial)).trans
    (forecast_norm_sq_lower H hH0 hH1 t ht0 n)
  simpa only [div_pow, mul_div_assoc] using he

end Fractional

end OperatorDerivativeRewrite.Foundation.GaussianWickPredictionBound
