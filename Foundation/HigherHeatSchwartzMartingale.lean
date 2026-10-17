import Foundation.HigherHeatBackwardSchwartz
import Foundation.HigherHeatIntegrableGains

/-! Actual weak signed-kernel martingale identities for general backward Schwartz fields. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped NNReal Topology SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzMartingale
open HigherHeatSignedLaws HigherHeatFourierInnovations SignedAbsoluteIntegration HigherHeatBackwardSchwartz

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem weighted_integrable (past : Ω → ℝ) (hp : Measurable past)
    (G : Ω → ℂ) (hiG : Integrable G (absoluteDensity μ past)) :
    Integrable (fun w => (past w:ℂ)*G w) μ := by
  let s : Ω → ℂ := fun w => if 0 ≤ past w then 1 else -1
  have hsm : Measurable s := Measurable.ite (measurableSet_le measurable_const hp)
    measurable_const measurable_const
  have hsb (w : Ω) : ‖s w‖ ≤ 1 := by dsimp only [s]; split_ifs <;> norm_num
  have hi := (absolute_integrable_iff μ past hp G).mp hiG
  apply (hi.bdd_mul hsm.aestronglyMeasurable (Eventually.of_forall hsb)).congr
  exact Eventually.of_forall fun w => by
    change s w*(|past w| • G w)=(past w:ℂ)*G w
    by_cases hw : 0 ≤ past w
    · simp only [s,if_pos hw,abs_of_nonneg hw,Complex.real_smul,one_mul]
    · simp only [s,if_neg hw,abs_of_neg (lt_of_not_ge hw),Complex.real_smul,Complex.ofReal_neg]
      ring

theorem bounded_joint_absolute_integrable (past : Ω → ℝ) (hp : Measurable past)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hiG : Integrable G (absoluteDensity μ past))
    (Φ : Ω × ℝ → ℂ) (hΦ : Measurable Φ) (B : ℝ) (hb : ∀ w, ‖Φ w‖ ≤ B) :
    Integrable (fun w => G w.1*Φ w)
      (absoluteDensity (μ.prod volume) (fun w => past w.1*realKernel m hm t ht w.2)) := by
  have hmK := (realKernel m hm t ht).continuous.measurable
  have hdm := (hp.comp measurable_fst).mul (hmK.comp measurable_snd)
  apply (absolute_integrable_iff (μ.prod volume) _ hdm _).mpr
  have hG := (absolute_integrable_iff μ past hp G).mp hiG
  have hK : Integrable (fun z : ℝ => ((|realKernel m hm t ht z|:ℝ):ℂ)) := by
    apply (((realKernel m hm t ht).integrable (μ := volume)).norm.ofReal).congr
    exact Eventually.of_forall fun z => by
      change ((‖realKernel m hm t ht z‖:ℝ):ℂ)=((|realKernel m hm t ht z|:ℝ):ℂ)
      rw [Real.norm_eq_abs]
  apply ((hG.mul_prod hK).mul_bdd hΦ.aestronglyMeasurable (Eventually.of_forall hb)).congr
  exact Eventually.of_forall fun w => by
    change (|past w.1| • G w.1)*((|realKernel m hm t ht w.2|:ℝ):ℂ)*Φ w=
      |past w.1*realKernel m hm t ht w.2| • (G w.1*Φ w)
    simp only [Complex.real_smul,abs_mul,Complex.ofReal_mul]
    ring

theorem joint_kernel_zero (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hiG : Integrable G (absoluteDensity μ past))
    (Φ : Ω × ℝ → ℂ) (hΦ : Measurable Φ) (B : ℝ) (hb : ∀ w, ‖Φ w‖ ≤ B)
    (hz : ∀ w, (∫ z : ℝ, Φ (w,z)*(realKernel m hm t ht z:ℂ))=0) :
    (∫ᵛ w, G w.1*Φ w ∂<•extendedLaw μ past m hm t ht)=0 := by
  have hd := hi.mul_prod ((realKernel m hm t ht).integrable (μ := volume))
  have hdm : Measurable (fun w : Ω × ℝ => past w.1*realKernel m hm t ht w.2) :=
    (hp.comp measurable_fst).mul ((realKernel m hm t ht).continuous.measurable.comp measurable_snd)
  rw [extendedLaw,SignedAbsoluteIntegration.integral_density (μ.prod volume) _ hd hdm _
    (bounded_joint_absolute_integrable μ past hp m hm t ht G hiG Φ hΦ B hb)]
  have he : (fun w : Ω × ℝ => (past w.1*realKernel m hm t ht w.2) • (G w.1*Φ w))=
      (fun w : Ω × ℝ => ((past w.1:ℂ)*G w.1)*(Φ w*(realKernel m hm t ht w.2:ℂ))) := by
    funext w
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring
  have hF : Integrable (fun w : Ω × ℝ => ((past w.1:ℂ)*G w.1)*
      (Φ w*(realKernel m hm t ht w.2:ℂ))) (μ.prod volume) := by
    have h := ((weighted_integrable μ past hp G hiG).mul_prod
      ((realKernel m hm t ht).integrable (μ := volume)).ofReal).mul_bdd
        hΦ.aestronglyMeasurable (Eventually.of_forall hb)
    apply h.congr
    exact Eventually.of_forall fun w => by
      change ((past w.1:ℂ)*G w.1)*(realKernel m hm t ht w.2:ℂ)*Φ w=
        ((past w.1:ℂ)*G w.1)*(Φ w*(realKernel m hm t ht w.2:ℂ))
      ring
  rw [he]
  calc
    _ = ∫ w, (∫ z : ℝ, ((past w:ℂ)*G w)*(Φ (w,z)*(realKernel m hm t ht z:ℂ))) ∂μ :=
      integral_prod _ hF
    _ = 0 := by
      have hs (w : Ω) : (∫ z : ℝ, ((past w:ℂ)*G w)*(Φ (w,z)*(realKernel m hm t ht z:ℂ)))=0 := by
        rw [integral_const_mul,hz,mul_zero]
      simp_rw [hs]
      simp

theorem backward_gain_zero (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (T s t : ℝ≥0) (hst : s < t) (ht : t ≤ T)
    (f : 𝓢(ℝ,ℂ)) (X : Ω → ℝ) (hX : Measurable X)
    (G : Ω → ℂ) (hiG : Integrable G (absoluteDensity μ past)) :
    (∫ᵛ w, G w.1*gain m hm T s t f (X w.1) w.2
      ∂<•extendedLaw μ past m hm (t-s) (tsub_pos_iff_lt.mpr hst))=0 := by
  refine joint_kernel_zero μ past hp hi m hm (t-s) (tsub_pos_iff_lt.mpr hst) G hiG
    (fun w => gain m hm T s t f (X w.1) w.2) ?_ (2*∫ ξ : ℝ, ‖𝓕 f ξ‖) ?_ ?_
  · exact ((backward m hm T t f).continuous.measurable.comp
      ((hX.comp measurable_fst).add measurable_snd)).sub
      ((backward m hm T s f).continuous.measurable.comp (hX.comp measurable_fst))
  · exact fun w => gain_bound m hm T s t f (X w.1) w.2
  · exact fun w => gain_kernel_zero m hm T s t hst ht f (X w)

theorem finite_past_gain_zero {ι : Type*} [Fintype ι] (m : ℕ) (hm : 0 < m)
    (times : ι → ℝ≥0) (htimes : ∀ i, 0 < times i) (T s t : ℝ≥0)
    (hst : s < t) (ht : t ≤ T) (f : 𝓢(ℝ,ℂ)) (G : (ι → ℝ) → ℂ)
    (hiG : Integrable G (absoluteDensity (Measure.pi (fun _ : ι => volume))
      (incrementDensity m hm times htimes))) :
    (∫ᵛ w, G w.1*gain m hm T s t f (∑ i, w.1 i) w.2
      ∂<•extendedLaw (Measure.pi (fun _ : ι => volume)) (incrementDensity m hm times htimes)
        m hm (t-s) (tsub_pos_iff_lt.mpr hst))=0 := by
  apply backward_gain_zero (μ := Measure.pi (fun _ : ι => volume)) (incrementDensity m hm times htimes)
    (by unfold incrementDensity; fun_prop) (incrementDensity_integrable m hm times htimes)
    m hm T s t hst ht f (fun w => ∑ i, w i) (by fun_prop) G hiG

theorem increment_process_gain_zero {ι : Type*} [Fintype ι] (m : ℕ) (hm : 0 < m)
    (times : ι → ℝ≥0) (htimes : ∀ i, 0 < times i) (T t : ℝ≥0)
    (hst : (∑ i, times i) < t) (ht : t ≤ T) (f : 𝓢(ℝ,ℂ)) (G : (ι → ℝ) → ℂ)
    (hiG : Integrable G (absoluteDensity (Measure.pi (fun _ : ι => volume))
      (incrementDensity m hm times htimes))) :
    (∫ᵛ w, G w.1*gain m hm T (∑ i, times i) t f (∑ i, w.1 i) w.2
      ∂<•extendedLaw (Measure.pi (fun _ : ι => volume)) (incrementDensity m hm times htimes)
        m hm (t-(∑ i, times i)) (tsub_pos_iff_lt.mpr hst))=0 :=
  finite_past_gain_zero m hm times htimes T (∑ i, times i) t hst ht f G hiG

end OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzMartingale
