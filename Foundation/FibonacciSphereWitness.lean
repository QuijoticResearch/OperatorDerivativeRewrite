import Foundation.LabelledShearCentroid
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact normalized Fibonacci centers and four rational covering witnesses at J=16. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FibonacciSphereWitness

def golden : ℝ := (1+Real.sqrt 5)/2

def phase (j : ℕ) : ℝ := 2*Real.pi*j/golden

def height (J : ℕ) (j : Fin J) : ℝ := 1-(2*(j.val:ℝ)+1)/J

def radius (J : ℕ) (j : Fin J) : ℝ := Real.sqrt (1-height J j^2)

def center (J : ℕ) (j : Fin J) : Fin 3 → ℝ :=
  ![radius J j*Real.cos (phase j.val),radius J j*Real.sin (phase j.val),height J j]

theorem height_bounds (J : ℕ) (j : Fin J) : -1 ≤ height J j ∧ height J j ≤ 1 := by
  have hJ : (0:ℝ) < J := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hj : (j.val:ℝ)+1 ≤ J := by exact_mod_cast j.isLt
  dsimp [height]
  constructor
  · apply sub_le_iff_le_add'.mp
    have h : (2*(j.val:ℝ)+1)/J ≤ 2 := (div_le_iff₀ hJ).2 (by linarith)
    linarith
  · have h : 0 ≤ (2*(j.val:ℝ)+1)/J := by positivity
    linarith

theorem radius_sq (J : ℕ) (j : Fin J) : radius J j^2=1-height J j^2 := by
  apply Real.sq_sqrt
  obtain ⟨hl,hu⟩ := height_bounds J j
  nlinarith [mul_nonneg (by linarith : 0 ≤ height J j+1) (by linarith : 0 ≤ 1-height J j)]

theorem center_unit (J : ℕ) (j : Fin J) : ∑ q : Fin 3, (center J j q)^2=1 := by
  simp only [Fin.sum_univ_three,center,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Matrix.head_cons,Matrix.head_fin_const]
  nlinarith [Real.sin_sq_add_cos_sq (phase j.val),radius_sq J j]

theorem center_source_formula (J : ℕ) (j : Fin J) :
    center J j = ![Real.sin (Real.arccos (height J j))*Real.cos (phase j.val),
      Real.sin (Real.arccos (height J j))*Real.sin (phase j.val),
      Real.cos (Real.arccos (height J j))] := by
  obtain ⟨hl,hu⟩ := height_bounds J j
  simp only [Real.sin_arccos,Real.cos_arccos hl hu,center,radius]

theorem golden_inverse : 1/golden=(Real.sqrt 5-1)/2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5:ℝ)
  have hg : golden ≠ 0 := by dsimp [golden]; positivity
  apply (div_eq_iff hg).2
  dsimp [golden]
  nlinarith

theorem phase_alternative (j : ℕ) : phase j=j*Real.pi*(Real.sqrt 5-1) := by
  dsimp [phase]
  rw [div_eq_mul_one_div,golden_inverse]
  ring

theorem sqrt_five_bounds : (67:ℝ)/30 ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ 161/72 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5:ℝ)
  constructor <;> nlinarith

theorem cos_small {d : ℝ} (hl : -(1:ℝ)/2 ≤ d) (hu : d ≤ 1/2) : 7/8 ≤ Real.cos d := by
  have hb := mul_nonneg (by linarith : 0 ≤ d+1/2) (by linarith : 0 ≤ 1/2-d)
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := d)]

theorem witness_seven : (3:ℝ)/4 ≤ center 16 ⟨7,by decide⟩ 1 := by
  let d : ℝ := Real.pi*(7*Real.sqrt 5-31/2)
  obtain ⟨hl,hu⟩ := sqrt_five_bounds
  have hd0 : 0 ≤ 7*Real.sqrt 5-31/2 := by linarith
  have hd1 : 7*Real.sqrt 5-31/2 ≤ (11:ℝ)/72 := by linarith
  have hdl : -(1:ℝ)/2 ≤ d := by
    have hp := mul_nonneg Real.pi_pos.le hd0
    dsimp [d]
    linarith
  have hdu : d ≤ 1/2 := by
    have hp := mul_le_mul_of_nonneg_left hd1 Real.pi_pos.le
    dsimp [d]
    nlinarith [Real.pi_lt_d2]
  have hcos := cos_small hdl hdu
  have he : phase 7=(d+Real.pi/2)+(4:ℕ)*(2*Real.pi) := by
    rw [phase_alternative]
    dsimp [d]
    norm_num
    ring
  have hsin : Real.sin (phase 7)=Real.cos d := by
    rw [he,Real.sin_add_nat_mul_two_pi,Real.sin_add_pi_div_two]
  have hr : (7:ℝ)/8 ≤ radius 16 ⟨7,by decide⟩ := by
    have hs := radius_sq 16 ⟨7,by decide⟩
    have hn := Real.sqrt_nonneg (1-height 16 ⟨7,by decide⟩^2)
    have heh : height 16 ⟨7,by decide⟩=(1:ℝ)/16 := by norm_num [height]
    rw [heh] at hs
    change 0 ≤ radius 16 ⟨7,by decide⟩ at hn
    nlinarith
  change (3:ℝ)/4 ≤ radius 16 ⟨7,by decide⟩*Real.sin (phase 7)
  rw [hsin]
  nlinarith [mul_le_mul hr hcos (by norm_num : (0:ℝ) ≤ 7/8) (by linarith)]

theorem witness_six : (3:ℝ)/4 ≤ -center 16 ⟨6,by decide⟩ 1 := by
  let d : ℝ := Real.pi*(6*Real.sqrt 5-27/2)
  obtain ⟨hl,hu⟩ := sqrt_five_bounds
  have hd0 : -(1:ℝ)/10 ≤ 6*Real.sqrt 5-27/2 := by linarith
  have hd1 : 6*Real.sqrt 5-27/2 ≤ 0 := by linarith
  have hdl : -(1:ℝ)/2 ≤ d := by
    have hp := mul_le_mul_of_nonneg_left hd0 Real.pi_pos.le
    dsimp [d]
    nlinarith [Real.pi_lt_d2]
  have hdu : d ≤ 1/2 := by
    have hp := mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hd1
    dsimp [d]
    linarith
  have hcos := cos_small hdl hdu
  have he : phase 6=((d+Real.pi/2)+Real.pi)+(3:ℕ)*(2*Real.pi) := by
    rw [phase_alternative]
    dsimp [d]
    norm_num
    ring
  have hsin : Real.sin (phase 6) = -Real.cos d := by
    rw [he,Real.sin_add_nat_mul_two_pi,Real.sin_add_pi,Real.sin_add_pi_div_two]
  have hr : (7:ℝ)/8 ≤ radius 16 ⟨6,by decide⟩ := by
    have hs := radius_sq 16 ⟨6,by decide⟩
    have hn := Real.sqrt_nonneg (1-height 16 ⟨6,by decide⟩^2)
    have heh : height 16 ⟨6,by decide⟩=(3:ℝ)/16 := by norm_num [height]
    rw [heh] at hs
    change 0 ≤ radius 16 ⟨6,by decide⟩ at hn
    nlinarith
  change (3:ℝ)/4 ≤ -(radius 16 ⟨6,by decide⟩*Real.sin (phase 6))
  rw [hsin,mul_neg,neg_neg]
  nlinarith [mul_le_mul hr hcos (by norm_num : (0:ℝ) ≤ 7/8) (by linarith)]

theorem witness_north : (3:ℝ)/4 ≤ center 16 ⟨0,by decide⟩ 2 := by
  norm_num [center,height]

theorem witness_south : (3:ℝ)/4 ≤ -center 16 ⟨15,by decide⟩ 2 := by
  norm_num [center,height]

end OperatorDerivativeRewrite.Foundation.FibonacciSphereWitness
