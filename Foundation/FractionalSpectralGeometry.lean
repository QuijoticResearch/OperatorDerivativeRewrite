import Foundation.FractionalSpectralKernel
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact spectral increment geometry and fractional covariance. The covariance
is derived from actual L² vectors, never supplied as a positive-definiteness assumption. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FractionalSpectralGeometry
open FractionalSpectralKernel

theorem wave_sub_norm_sq (u v : ℝ) :
    ‖wave u - wave v‖ ^ 2 = ‖wave (u-v)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, wave_norm_sq, Real.cos_sub]
  simp [wave, Fin.sum_univ_two]
  nlinarith [Real.sin_sq_add_cos_sq u, Real.sin_sq_add_cos_sq v]

theorem kernel_sub_norm_sq (H s t x : ℝ) :
    ‖kernel H t x - kernel H s x‖ ^ 2 = ‖kernel H (t-s) x‖ ^ 2 := by
  by_cases hx : 0 < x
  · simp only [kernel, indicator_of_mem (show x ∈ Ioi (0:ℝ) from hx), raw,
      ← smul_sub, norm_smul, mul_pow]
    rw [wave_sub_norm_sq, show t*x-s*x = (t-s)*x by ring]
  · simp [kernel, hx]

theorem kernel_neg_norm_sq (H t x : ℝ) :
    ‖kernel H (-t) x‖ ^ 2 = ‖kernel H t x‖ ^ 2 := by
  by_cases hx : 0 < x
  · simp only [kernel, indicator_of_mem (show x ∈ Ioi (0:ℝ) from hx)]
    rw [raw_norm_sq H (-t) x hx, raw_norm_sq H t x hx, wave_norm_sq, wave_norm_sq]
    simp only [neg_mul, Real.cos_neg]
  · simp [kernel, hx]

theorem kernel_scale_norm_sq (H t x : ℝ) (ht : 0 < t) :
    ‖kernel H t x‖ ^ 2 = t ^ (2*H+1) * ‖kernel H 1 (t*x)‖ ^ 2 := by
  by_cases hx : 0 < x
  · have htx := mul_pos ht hx
    simp only [kernel, indicator_of_mem (show x ∈ Ioi (0:ℝ) from hx),
      indicator_of_mem (show t*x ∈ Ioi (0:ℝ) from htx)]
    rw [raw_norm_sq H t x hx, raw_norm_sq H 1 (t*x) htx, one_mul,
      Real.mul_rpow ht.le hx.le]
    have he : t^(2*H+1) * t^(-2*H-1) = 1 := by
      rw [← Real.rpow_add ht, show 2*H+1+(-2*H-1) = 0 by ring, Real.rpow_zero]
    nlinarith [congrArg (fun z : ℝ => z * (x^(-2*H-1) * ‖wave (t*x)‖^2)) he]
  · have htx : ¬ 0 < t*x := not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos ht.le (not_lt.mp hx))
    simp [kernel, hx, htx]

theorem vector_sub_norm_sq (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (s t : ℝ) :
    ‖vector H hH0 hH1 t - vector H hH0 hH1 s‖ ^ 2 = ‖vector H hH0 hH1 (t-s)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, vector_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (vector H hH0 hH1 t) (vector H hH0 hH1 s),
    vector_coeFn H hH0 hH1 t, vector_coeFn H hH0 hH1 s] with x hd ht hs
  simp only [Pi.sub_apply] at hd
  rw [hd, ht, hs, real_inner_self_eq_norm_sq, kernel_sub_norm_sq]

theorem vector_neg_norm_sq (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ) :
    ‖vector H hH0 hH1 (-t)‖ ^ 2 = ‖vector H hH0 hH1 t‖ ^ 2 := by
  simp_rw [vector_norm_sq_integral, kernel_neg_norm_sq]

theorem vector_pos_norm_sq (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ) (ht : 0 < t) :
    ‖vector H hH0 hH1 t‖ ^ 2 = t^(2*H) * ‖vector H hH0 hH1 1‖ ^ 2 := by
  rw [vector_norm_sq_integral, vector_norm_sq_integral]
  simp_rw [kernel_scale_norm_sq H t _ ht]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x : ℝ => ‖kernel H 1 x‖ ^ 2) t,
    abs_of_pos (inv_pos.mpr ht), smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
  congr 1
  ring

theorem vector_norm_sq (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ) :
    ‖vector H hH0 hH1 t‖ ^ 2 = |t|^(2*H) * ‖vector H hH0 hH1 1‖ ^ 2 := by
  rcases lt_trichotomy 0 t with ht | ht | ht
  · rw [abs_of_pos ht]
    exact vector_pos_norm_sq H hH0 hH1 t ht
  · subst t
    simp [vector_zero, Real.zero_rpow (by positivity : 2*H ≠ 0)]
  · rw [abs_of_neg ht, ← vector_neg_norm_sq H hH0 hH1 t]
    exact vector_pos_norm_sq H hH0 hH1 (-t) (neg_pos.mpr ht)

def normalized (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ) : SpectralSpace :=
  ‖vector H hH0 hH1 1‖⁻¹ • vector H hH0 hH1 t

theorem normalized_norm_sq (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ) :
    ‖normalized H hH0 hH1 t‖ ^ 2 = |t|^(2*H) := by
  have hn := norm_ne_zero_iff.mpr (vector_one_ne_zero H hH0 hH1)
  rw [normalized, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, vector_norm_sq]
  field_simp

theorem normalized_sub_norm_sq (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (s t : ℝ) :
    ‖normalized H hH0 hH1 t - normalized H hH0 hH1 s‖ ^ 2 = |t-s|^(2*H) := by
  rw [normalized, normalized, ← smul_sub, norm_smul, mul_pow, vector_sub_norm_sq]
  simpa only [normalized, norm_smul, mul_pow] using normalized_norm_sq H hH0 hH1 (t-s)

def covariance (H s t : ℝ) : ℝ := (|s|^(2*H) + |t|^(2*H) - |t-s|^(2*H)) / 2

theorem normalized_inner (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (s t : ℝ) :
    inner ℝ (normalized H hH0 hH1 s) (normalized H hH0 hH1 t) = covariance H s t := by
  have he := norm_sub_sq_real (normalized H hH0 hH1 t) (normalized H hH0 hH1 s)
  rw [normalized_sub_norm_sq, normalized_norm_sq, normalized_norm_sq, real_inner_comm] at he
  unfold covariance
  linarith


theorem normalized_zero (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    normalized H hH0 hH1 0 = 0 := by simp [normalized, vector_zero]

theorem normalized_sub_norm (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (s t : ℝ) :
    ‖normalized H hH0 hH1 t - normalized H hH0 hH1 s‖ = |t-s|^H := by
  have he := normalized_sub_norm_sq H hH0 hH1 s t
  have hp : (|t-s|^H)^2 = |t-s|^(2*H) := by
    rw [← Real.rpow_mul_natCast (abs_nonneg (t-s))]
    congr 1
    ring
  nlinarith [norm_nonneg (normalized H hH0 hH1 t - normalized H hH0 hH1 s),
    Real.rpow_nonneg (abs_nonneg (t-s)) H]

theorem normalized_continuous (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    Continuous (normalized H hH0 hH1) := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [normalized_sub_norm]
  have hc : Continuous (fun t : ℝ => |t-s|^H) :=
    (Real.continuous_rpow_const hH0.le).comp
      (continuous_abs.comp (continuous_id.sub (show Continuous (fun _ : ℝ => s) from continuous_const)))
  simpa only [sub_self, abs_zero, Real.zero_rpow hH0.ne'] using hc.tendsto s

theorem covariance_symm (H s t : ℝ) : covariance H s t = covariance H t s := by
  unfold covariance
  rw [abs_sub_comm t s]
  ring

/-- The fractional covariance is positive semidefinite because it is the Gram
kernel of actual Hilbert vectors. No positive-definiteness axiom is used. -/
theorem covariance_positive {ι : Type*} [Fintype ι] (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) (t : ι → ℝ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * covariance H (t i) (t j) := by
  have he : 0 ≤ inner ℝ (∑ i, c i • normalized H hH0 hH1 (t i))
      (∑ i, c i • normalized H hH0 hH1 (t i)) := real_inner_self_nonneg
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    normalized_inner, mul_assoc, Finset.mul_sum] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [covariance_symm H (t i) (t j)]
  ring
end OperatorDerivativeRewrite.Foundation.FractionalSpectralGeometry
