import Foundation.HigherHeatBackwardFourier

/-! Actual signed Fourier innovations and zero-mean gains against arbitrary cylindrical pasts. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierInnovations
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatL2
open HigherHeatBackwardFourier SignedDensityIntegral

def innovation (m : ℕ) (t : ℝ≥0) (ξ z : ℝ) : ℂ := phase ξ z-symbol m t ξ

theorem innovation_measurable (m : ℕ) (t : ℝ≥0) (ξ : ℝ) : Measurable (innovation m t ξ) :=
  (phase_continuous ξ).measurable.sub measurable_const

theorem innovation_bound (m : ℕ) (t : ℝ≥0) (ξ z : ℝ) : ‖innovation m t ξ z‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by rw [phase_norm]; linarith [symbol_norm_le m t ξ])

theorem kernel_innovation_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ : ℝ) :
    Integrable (fun z => innovation m t ξ z*(realKernel m hm t ht z : ℂ)) := by
  have h := (kernel_phase_integrable m hm t ht ξ).sub
    ((realKernel m hm t ht).integrable.ofReal.const_mul (symbol m t ξ))
  convert h using 1
  funext z
  change (phase ξ z-symbol m t ξ)*(realKernel m hm t ht z:ℂ) =
    phase ξ z*(realKernel m hm t ht z:ℂ)-symbol m t ξ*(realKernel m hm t ht z:ℂ)
  ring

theorem kernel_innovation_zero (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ : ℝ) :
    (∫ z : ℝ, innovation m t ξ z*(realKernel m hm t ht z : ℂ))=0 := by
  have he : (fun z => innovation m t ξ z*(realKernel m hm t ht z:ℂ)) =
      (fun z => phase ξ z*(realKernel m hm t ht z:ℂ)) -
      (fun z => symbol m t ξ*(realKernel m hm t ht z:ℂ)) := by
    funext z
    change (phase ξ z-symbol m t ξ)*(realKernel m hm t ht z:ℂ) = _
    simp only [Pi.sub_apply]
    ring
  rw [he]
  have hs := integral_sub (kernel_phase_integrable m hm t ht ξ)
      ((realKernel m hm t ht).integrable.ofReal.const_mul (symbol m t ξ))
  change (∫ z, phase ξ z*(realKernel m hm t ht z:ℂ)-
      symbol m t ξ*(realKernel m hm t ht z:ℂ))=0
  calc
    _ = (∫ z, phase ξ z*(realKernel m hm t ht z:ℂ)) -
        (∫ z, symbol m t ξ*(realKernel m hm t ht z:ℂ)) := hs
    _ = 0 := by
      rw [kernel_fourier,integral_const_mul,integral_complex_ofReal,realKernel_integral]
      simp

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

def extendedLaw (past : Ω → ℝ) (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    SignedMeasure (Ω × ℝ) :=
  (μ.prod volume).withDensityᵥ (fun w => past w.1*realKernel m hm t ht w.2)

theorem predictable_gain_zero (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ : ℝ)
    (G : Ω → ℂ) (hG : Measurable G) (C : ℝ) (hb : ∀ w, ‖G w‖ ≤ C) :
    (∫ᵛ w, G w.1*innovation m t ξ w.2 ∂<•extendedLaw μ past m hm t ht)=0 := by
  have hd := hi.mul_prod ((realKernel m hm t ht).integrable (μ := volume))
  have hdm : Measurable (fun w : Ω × ℝ => past w.1*realKernel m hm t ht w.2) :=
    (hp.comp measurable_fst).mul ((realKernel m hm t ht).continuous.measurable.comp measurable_snd)
  have hgm : Measurable (fun w : Ω × ℝ => G w.1*innovation m t ξ w.2) :=
    (hG.comp measurable_fst).mul ((innovation_measurable m t ξ).comp measurable_snd)
  have hgb (w : Ω × ℝ) : ‖G w.1*innovation m t ξ w.2‖ ≤ 2*C := by
    rw [norm_mul]
    calc
      _ ≤ ‖G w.1‖*2 := mul_le_mul_of_nonneg_left (innovation_bound m t ξ w.2) (norm_nonneg _)
      _ ≤ C*2 := mul_le_mul_of_nonneg_right (hb w.1) (by norm_num)
      _ = _ := by ring
  rw [extendedLaw,integral_density (μ.prod volume) _ hd hdm _ hgm (2*C) hgb]
  have he : (fun w : Ω × ℝ => (past w.1*realKernel m hm t ht w.2) •
      (G w.1*innovation m t ξ w.2)) =
      (fun w : Ω × ℝ => ((past w.1:ℂ)*G w.1)*
        (innovation m t ξ w.2*(realKernel m hm t ht w.2:ℂ))) := by
    funext w
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring
  rw [he]
  calc
    _ = (∫ w, (past w:ℂ)*G w ∂μ)*
        (∫ z, innovation m t ξ z*(realKernel m hm t ht z:ℂ)) :=
      integral_prod_mul (fun w => (past w:ℂ)*G w)
        (fun z => innovation m t ξ z*(realKernel m hm t ht z:ℂ))
    _ = 0 := by rw [kernel_innovation_zero,mul_zero]

theorem actual_past_gain_zero {ι : Type*} [Fintype ι] (m : ℕ) (hm : 0 < m)
    (times : ι → ℝ≥0) (htimes : ∀ i, 0 < times i) (t : ℝ≥0) (ht : 0 < t) (ξ : ℝ)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (C : ℝ) (hb : ∀ w, ‖G w‖ ≤ C) :
    (∫ᵛ w, G w.1*innovation m t ξ w.2 ∂<•extendedLaw (Measure.pi (fun _ : ι => volume))
      (incrementDensity m hm times htimes) m hm t ht)=0 := by
  apply predictable_gain_zero
    (μ := Measure.pi (fun _ : ι => volume)) (incrementDensity m hm times htimes)
    (by unfold incrementDensity; fun_prop) (incrementDensity_integrable m hm times htimes)
    m hm t ht ξ G hG C hb

theorem backward_gain_factor (m : ℕ) (T s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ T)
    (ξ x z : ℝ) :
    backwardCharacter m T t ξ (x+z)-backwardCharacter m T s ξ x=
      symbol m (T-t) ξ*phase ξ x*innovation m (t-s) ξ z := by
  have he : (T-t)+(t-s)=T-s := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,NNReal.coe_sub ht,NNReal.coe_sub hst,NNReal.coe_sub (hst.trans ht)]
    ring
  have hs := symbol_add m (T-t) (t-s) ξ
  rw [he] at hs
  simp only [backwardCharacter,hs,phase_add,innovation]
  ring

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierInnovations
