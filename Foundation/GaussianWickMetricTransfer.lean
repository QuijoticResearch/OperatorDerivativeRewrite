import Foundation.GaussianWickContinuity
import Foundation.FractionalWickCovariance

/-! Positive-correlation metric comparison in every normalized Wick degree. -/
noncomputable section
open MeasureTheory
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianWickMetricTransfer
open InfiniteGaussian GaussianTimeSpaceHermite

private theorem one_sub_pow_upper (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (n : ℕ) :
    1-ρ^n ≤ (n : ℝ)*(1-ρ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := pow_le_one₀ h0 h1 (n := n)
    have hm := mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hp)
    rw [pow_succ]
    push_cast
    nlinarith

private theorem one_sub_pow_lower (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (n : ℕ) :
    1-ρ ≤ 1-ρ^(n+1) := by
  have hp := pow_le_one₀ h0 h1 (n := n)
  have hm := mul_le_mul_of_nonneg_right hp h0
  rw [pow_succ]
  nlinarith

theorem unit_positive_correlation_bounds (h k : CoefficientSpace) (hh : ‖h‖=1) (hk : ‖k‖=1)
    (hc : 0 ≤ inner ℝ h k) (n : ℕ) :
    ((n+1).factorial : ℝ)*‖h-k‖^2 ≤
        ‖(wick h (n+1) : GaussianL2)-(wick k (n+1) : GaussianL2)‖^2 ∧
      ‖(wick h (n+1) : GaussianL2)-(wick k (n+1) : GaussianL2)‖^2 ≤
        (n+1 : ℝ)*((n+1).factorial : ℝ)*‖h-k‖^2 := by
  have hi := real_inner_le_norm h k
  rw [hh,hk,one_mul] at hi
  have hl := one_sub_pow_lower (inner ℝ h k) hc hi n
  have hu := one_sub_pow_upper (inner ℝ h k) hc hi (n+1)
  have hfac : (0 : ℝ) ≤ (n+1).factorial := by positivity
  have hlm := mul_le_mul_of_nonneg_left hl hfac
  have hum := mul_le_mul_of_nonneg_left hu hfac
  push_cast at hum
  rw [GaussianWickContinuity.wick_distance_sq,norm_sub_sq_real,hh,hk]
  simp only [one_pow]
  constructor <;> nlinarith

def unitDirection (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ≥0) : CoefficientSpace :=
  ‖FractionalGaussianProcess.direction H hH0 hH1 t‖⁻¹ •
    FractionalGaussianProcess.direction H hH0 hH1 t

theorem fractional_direction_norm_pos (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (t : ℝ≥0) (ht : 0 < t) : 0 < ‖FractionalGaussianProcess.direction H hH0 hH1 t‖ := by
  have hs : ‖FractionalGaussianProcess.direction H hH0 hH1 t‖^2=|(t : ℝ)|^(2*H) := by
    unfold FractionalGaussianProcess.direction
    rw [LinearIsometry.norm_map,FractionalSpectralGeometry.normalized_norm_sq]
  have hp : 0 < |(t : ℝ)|^(2*H) := Real.rpow_pos_of_pos (abs_pos.mpr (ne_of_gt ht)) _
  nlinarith [norm_nonneg (FractionalGaussianProcess.direction H hH0 hH1 t)]

theorem unitDirection_norm (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (t : ℝ≥0) (ht : 0 < t) : ‖unitDirection H hH0 hH1 t‖=1 := by
  rw [unitDirection,norm_smul,Real.norm_eq_abs,abs_of_pos
    (inv_pos.mpr (fractional_direction_norm_pos H hH0 hH1 t ht)),
    inv_mul_cancel₀ (ne_of_gt (fractional_direction_norm_pos H hH0 hH1 t ht))]

theorem fractional_covariance_nonneg (H : ℝ) (hH0 : 0 < H) (s t : ℝ≥0) :
    0 ≤ FractionalSpectralGeometry.covariance H s t := by
  unfold FractionalSpectralGeometry.covariance
  rw [abs_of_nonneg s.coe_nonneg,abs_of_nonneg t.coe_nonneg]
  rcases le_total s t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from h))]
    have hp := Real.rpow_le_rpow (sub_nonneg.mpr (show (s : ℝ) ≤ t from h))
      (show (t : ℝ)-s ≤ t by linarith [s.coe_nonneg]) (show 0 ≤ 2*H by positivity)
    have hs := Real.rpow_nonneg s.coe_nonneg (2*H)
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (show (t : ℝ) ≤ s from h)),neg_sub]
    have hp := Real.rpow_le_rpow (sub_nonneg.mpr (show (t : ℝ) ≤ s from h))
      (show (s : ℝ)-t ≤ s by linarith [t.coe_nonneg]) (show 0 ≤ 2*H by positivity)
    have ht := Real.rpow_nonneg t.coe_nonneg (2*H)
    linarith

theorem fractional_unit_correlation_nonneg (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (s t : ℝ≥0) :
    0 ≤ inner ℝ (unitDirection H hH0 hH1 s) (unitDirection H hH0 hH1 t) := by
  rw [unitDirection,unitDirection,real_inner_smul_left,real_inner_smul_right,
    FractionalWickCovariance.direction_inner]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (fractional_covariance_nonneg H hH0 s t))

theorem fractional_unit_wick_bounds (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) (n : ℕ) :
    ((n+1).factorial : ℝ)*‖unitDirection H hH0 hH1 s-unitDirection H hH0 hH1 t‖^2 ≤
        ‖(wick (unitDirection H hH0 hH1 s) (n+1) : GaussianL2)-
          (wick (unitDirection H hH0 hH1 t) (n+1) : GaussianL2)‖^2 ∧
      ‖(wick (unitDirection H hH0 hH1 s) (n+1) : GaussianL2)-
          (wick (unitDirection H hH0 hH1 t) (n+1) : GaussianL2)‖^2 ≤
        (n+1 : ℝ)*((n+1).factorial : ℝ)*
          ‖unitDirection H hH0 hH1 s-unitDirection H hH0 hH1 t‖^2 :=
  unit_positive_correlation_bounds _ _ (unitDirection_norm H hH0 hH1 s hs)
    (unitDirection_norm H hH0 hH1 t ht) (fractional_unit_correlation_nonneg H hH0 hH1 s t) n

end OperatorDerivativeRewrite.Foundation.GaussianWickMetricTransfer
