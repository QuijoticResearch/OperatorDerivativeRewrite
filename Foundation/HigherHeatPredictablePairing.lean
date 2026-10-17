import Foundation.HigherHeatFourierCovariance

/-! Actual predictable signed integration and a bilinear Fourier covariance rule. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPredictablePairing
open HigherHeatL2 HigherHeatSignedLaws HigherHeatFourierInnovations HigherHeatFourierCovariance
open SignedDensityIntegral

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem integral_separable (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hG : Measurable G) (C : ℝ) (hb : ∀ w, ‖G w‖ ≤ C)
    (W : ℝ → ℂ) (hW : Measurable W) (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ z, ‖W z‖ ≤ B) :
    (∫ᵛ w, G w.1*W w.2 ∂<•extendedLaw μ past m hm t ht)=
      (∫ w, (past w:ℂ)*G w ∂μ)*(∫ z : ℝ, W z*(realKernel m hm t ht z:ℂ)) := by
  have hd := hi.mul_prod ((realKernel m hm t ht).integrable (μ := volume))
  have hdm : Measurable (fun w : Ω × ℝ => past w.1*realKernel m hm t ht w.2) :=
    (hp.comp measurable_fst).mul ((realKernel m hm t ht).continuous.measurable.comp measurable_snd)
  have hgm : Measurable (fun w : Ω × ℝ => G w.1*W w.2) :=
    (hG.comp measurable_fst).mul (hW.comp measurable_snd)
  have hgb (w : Ω × ℝ) : ‖G w.1*W w.2‖ ≤ C*B := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hwb w.2) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (hb w.1) hB)
  rw [extendedLaw,integral_density (μ.prod volume) _ hd hdm _ hgm (C*B) hgb]
  have he : (fun w : Ω × ℝ => (past w.1*realKernel m hm t ht w.2) • (G w.1*W w.2))=
      (fun w : Ω × ℝ => ((past w.1:ℂ)*G w.1)*(W w.2*(realKernel m hm t ht w.2:ℂ))) := by
    funext w
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring
  rw [he]
  exact integral_prod_mul (fun w => (past w:ℂ)*G w) (fun z => W z*(realKernel m hm t ht z:ℂ))

theorem product_innovation_bound (m : ℕ) (t : ℝ≥0) (ξ η z : ℝ) :
    ‖innovation m t ξ z*innovation m t η z‖ ≤ 4 := by
  rw [norm_mul]
  nlinarith [innovation_bound m t ξ z,innovation_bound m t η z,norm_nonneg (innovation m t ξ z),
    norm_nonneg (innovation m t η z)]

theorem innovation_pairing (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ η : ℝ)
    (G : Ω → ℂ) (hG : Measurable G) (C : ℝ) (hb : ∀ w, ‖G w‖ ≤ C) :
    (∫ᵛ w, G w.1*(innovation m t ξ w.2*innovation m t η w.2)
      ∂<•extendedLaw μ past m hm t ht)=
      (∫ w, (past w:ℂ)*G w ∂μ)*covariance m t ξ η := by
  rw [integral_separable μ past hp hi m hm t ht G hG C hb
    (fun z => innovation m t ξ z*innovation m t η z)
    ((innovation_measurable m t ξ).mul (innovation_measurable m t η))
    4 (by norm_num) (product_innovation_bound m t ξ η),kernel_product]

theorem covariance_bound (m : ℕ) (t : ℝ≥0) (ξ η : ℝ) : ‖covariance m t ξ η‖ ≤ 2 := by
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  have h := mul_le_one₀ (symbol_norm_le m t ξ) (norm_nonneg (symbol m t η))
    (symbol_norm_le m t η)
  linarith [symbol_norm_le m t (ξ+η)]

theorem compensated_product_zero (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ η : ℝ)
    (G : Ω → ℂ) (hG : Measurable G) (C : ℝ) (hb : ∀ w, ‖G w‖ ≤ C) :
    (∫ᵛ w, G w.1*(innovation m t ξ w.2*innovation m t η w.2-covariance m t ξ η)
      ∂<•extendedLaw μ past m hm t ht)=0 := by
  have hbW (z : ℝ) : ‖innovation m t ξ z*innovation m t η z-covariance m t ξ η‖ ≤ 6 :=
    (norm_sub_le _ _).trans (by linarith [product_innovation_bound m t ξ η z,covariance_bound m t ξ η])
  calc
    _ = (∫ w, (past w:ℂ)*G w ∂μ)*
        (∫ z : ℝ, (innovation m t ξ z*innovation m t η z-covariance m t ξ η)*
          (realKernel m hm t ht z:ℂ)) :=
      integral_separable μ past hp hi m hm t ht G hG C hb
        (fun z => innovation m t ξ z*innovation m t η z-covariance m t ξ η)
        (((innovation_measurable m t ξ).mul (innovation_measurable m t η)).sub measurable_const)
        6 (by norm_num) hbW
    _ = 0 := by rw [centered_product_zero,mul_zero]

end OperatorDerivativeRewrite.Foundation.HigherHeatPredictablePairing
