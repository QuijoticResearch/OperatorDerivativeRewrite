import Foundation.ComplexFourthRootNoise

/-! Exact multi-channel representation on the actual four-point probability noise. -/
noncomputable section
open MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.ComplexRootMarkRepresentation
open ComplexFourthRootNoise

def fourthMoment (a : ℝ) : ℂ := -4*(a : ℂ)^4

def coefficient (a : ℝ) (g : Fin 4 → ℂ) (r : Fin 3) : ℂ :=
  (∫ k, g k*(noise a k)^(3-r.val) ∂probability) / fourthMoment a

theorem fourthMoment_ne_zero (a : ℝ) (ha : a ≠ 0) : fourthMoment a ≠ 0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ha))

theorem basis_identity (a : ℝ) (g : Fin 4 → ℂ) (k : Fin 4) :
    fourthMoment a * (g k - ∫ j, g j ∂probability) =
      (∫ j, g j*(noise a j)^3 ∂probability)*noise a k +
      (∫ j, g j*(noise a j)^2 ∂probability)*(noise a k)^2 +
      (∫ j, g j*noise a j ∂probability)*(noise a k)^3 := by
  simp only [integral_formula]
  fin_cases k <;> norm_num [fourthMoment, noise, root] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem centered_representation (a : ℝ) (ha : a ≠ 0) (g : Fin 4 → ℂ) (k : Fin 4) :
    g k - (∫ j, g j ∂probability) =
      coefficient a g 0 * noise a k + coefficient a g 1 * (noise a k)^2 +
      coefficient a g 2 * (noise a k)^3 := by
  have hK := fourthMoment_ne_zero a ha
  have he := basis_identity a g k
  simp only [coefficient, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num only
  field_simp [hK]
  linear_combination he

theorem channel_sum_moment (a : ℝ) (d : Fin 3 → ℂ) (r : Fin 3) :
    (∫ k, (d 0*noise a k+d 1*(noise a k)^2+d 2*(noise a k)^3) *
      (noise a k)^(3-r.val) ∂probability) = fourthMoment a*d r := by
  rw [integral_formula]
  fin_cases r <;> norm_num [fourthMoment, noise, root] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem channel_unique (a : ℝ) (ha : a ≠ 0) (d e : Fin 3 → ℂ)
    (h : ∀ k : Fin 4, d 0*noise a k+d 1*(noise a k)^2+d 2*(noise a k)^3 =
      e 0*noise a k+e 1*(noise a k)^2+e 2*(noise a k)^3) : d = e := by
  funext r
  have he : (∫ k, (d 0*noise a k+d 1*(noise a k)^2+d 2*(noise a k)^3) *
      (noise a k)^(3-r.val) ∂probability) =
      ∫ k, (e 0*noise a k+e 1*(noise a k)^2+e 2*(noise a k)^3) *
        (noise a k)^(3-r.val) ∂probability :=
    integral_congr_ae (Eventually.of_forall fun k => congrArg (·*(noise a k)^(3-r.val)) (h k))
  rw [channel_sum_moment, channel_sum_moment] at he
  exact mul_left_cancel₀ (fourthMoment_ne_zero a ha) he

theorem unique_representer (a : ℝ) (ha : a ≠ 0) (g : Fin 4 → ℂ) (d : Fin 3 → ℂ)
    (h : ∀ k : Fin 4, g k-(∫ j, g j ∂probability) =
      d 0*noise a k+d 1*(noise a k)^2+d 2*(noise a k)^3) : d = coefficient a g := by
  apply channel_unique a ha
  intro k
  exact (h k).symm.trans (centered_representation a ha g k)

theorem no_single_noise_representation (a : ℝ) (ha : a ≠ 0) :
    ¬ ∃ c : ℂ, ∀ k : Fin 4, (noise a k)^2 = c*noise a k := by
  rintro ⟨c,hc⟩
  have he : (∫ k, (noise a k)^4 ∂probability) =
      c*(∫ k, (noise a k)^3 ∂probability) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with k
    calc
      _ = (noise a k)^2*(noise a k)^2 := by ring
      _ = (c*noise a k)*(noise a k)^2 := by rw [hc k]
      _ = _ := by ring
  rw [fourth, third, mul_zero] at he
  exact fourthMoment_ne_zero a ha he

end OperatorDerivativeRewrite.Foundation.ComplexRootMarkRepresentation
