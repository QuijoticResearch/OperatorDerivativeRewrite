import Foundation.RiemannEvenGrowingMoment
import Foundation.RiemannQuarticZeroStrip

/-! Uniform actual cosine approximation on a growing frequency disk and
the resulting saddle-scaled imaginary-zero bound. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenGrowingFourier
open RiemannEvenDomain RiemannEvenRealSaddle RiemannEvenWeightedTails
open RiemannEvenGrowingMoment RiemannEvenFourierMoment

theorem actual_centered_moment_mono (m : ℕ) (t u B D : ℝ)
    (hu : 0 ≤ u) (hB : 0 ≤ B) (hBD : B ≤ D) :
    (∫ v : ℝ in Ici 0, |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v) ≤
      ∫ v : ℝ in Ici 0, |v-u| * Real.exp (D*|v-u|) * weighted m 0 t 0 v := by
  apply setIntegral_mono_on
    (actual_centered_exponential_moment_integrable m t u B hu hB)
    (actual_centered_exponential_moment_integrable m t u D hu (hB.trans hBD)) measurableSet_Ici
  intro v hv
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBD (abs_nonneg (v-u)))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (abs_nonneg (v-u))) (weighted_pos m t v hv).le

theorem uniform_growing_normalized_cosine (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted m 0 t 0) (Ici 0) u → ∀ z : ℂ, ‖z‖ ≤ u →
      ‖RiemannEvenFlow.flow m t z/RiemannEvenFlow.flow m t 0-Complex.cos ((u : ℂ)*z)‖ <
        ε*Real.exp (u*|z.im|) := by
  filter_upwards [normalized_growing_moment_eventually_small m hm ε hε] with t ht
  intro u hu hmax z hz
  have hu0 : 0 ≤ u := hu
  have hM := RiemannEvenNormalizedCompact.actual_flow_zero_pos m t
  have hi := actual_centered_moment_mono m t u ‖z‖ u hu0 (norm_nonneg z) hz
  have hnonneg : 0 ≤ ∫ v : ℝ in Ici 0,
      |v-u| * Real.exp (‖z‖*|v-u|) * weighted m 0 t 0 v := by
    apply setIntegral_nonneg_ae measurableSet_Ici
    exact Eventually.of_forall (fun v hv =>
      mul_nonneg (by positivity) (weighted_pos m t v hv).le)
  have hscaled := mul_le_mul hz (div_le_div_of_nonneg_right hi hM.le)
    (div_nonneg hnonneg hM.le) hu0
  have hb := actual_normalized_cosine_error_bound m t u z hu0
  have hsmall := ht u hu hmax
  calc
    _ ≤ (Real.exp (u*|z.im|)*‖z‖)*
        ((∫ v : ℝ in Ici 0, |v-u| * Real.exp (‖z‖*|v-u|) * weighted m 0 t 0 v)/
          (RiemannEvenFlow.flow m t 0).re) := hb
    _ ≤ Real.exp (u*|z.im|)*(u*((∫ v : ℝ in Ici 0,
        |v-u| * Real.exp (u*|v-u|) * weighted m 0 t 0 v)/(RiemannEvenFlow.flow m t 0).re)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscaled (Real.exp_pos (u*|z.im|)).le
    _ < ε*Real.exp (u*|z.im|) := by
      simpa only [mul_comm] using mul_lt_mul_of_pos_left hsmall (Real.exp_pos (u*|z.im|))

theorem exp_abs_le_two_cosh (x : ℝ) : Real.exp |x| ≤ 2*Real.cosh x := by
  rw [Real.cosh_eq]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    linarith [Real.exp_pos x]

theorem actual_growing_zero_strip (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted m 0 t 0) (Ici 0) u → ∀ z : ℂ, ‖z‖ ≤ u →
      RiemannEvenFlow.flow m t z = 0 → u*|z.im| ≤ δ := by
  let ε : ℝ := min (1/4) (δ/4)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  filter_upwards [uniform_growing_normalized_cosine m hm ε hε] with t ht
  intro u hu hmax z hz hzero
  have h := ht u hu hmax z hz
  rw [hzero,zero_div,zero_sub,norm_neg] at h
  have hi : ((u : ℂ)*z).im = u*z.im := by simp [Complex.mul_im]
  have habs : |u*z.im| = u*|z.im| := by rw [abs_mul,abs_of_nonneg hu]
  have he := exp_abs_le_two_cosh (u*z.im)
  rw [habs] at he
  have hcos : ‖Complex.cos ((u : ℂ)*z)‖ ≤ (2*ε)*Real.cosh (((u : ℂ)*z).im) := by
    rw [hi]
    nlinarith
  have h2 := min_le_left (1/4 : ℝ) (δ/4)
  have hstrip := RiemannQuarticZeroStrip.small_cos_im ((u : ℂ)*z) (2*ε)
    (by positivity) (by dsimp [ε]; linarith) hcos
  rw [hi,habs] at hstrip
  have hδbound := min_le_right (1/4 : ℝ) (δ/4)
  dsimp [ε] at hstrip
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannEvenGrowingFourier
