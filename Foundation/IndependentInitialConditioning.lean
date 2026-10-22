import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! Adding an independent initial factor leaves an actual scalar conditional
expectation unchanged. The product sigma algebra and probability law are explicit. -/
noncomputable section
open MeasureTheory Set Filter
namespace OperatorDerivativeRewrite.Foundation.IndependentInitialConditioning
set_option backward.isDefEq.respectTransparency false
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include μ

theorem conditional_snd (n : MeasurableSpace Y) (hn : n ≤ mY) (f g : Y → ℝ)
    (hf : Integrable f ν) (hg : Integrable g ν) (hgm : StronglyMeasurable[n] g)
    (he : ν[f | n] =ᵐ[ν] g) :
    (@Measure.prod X Y mX mY μ ν)[(fun z : X × Y => f z.2) | mX.prod n]
      =ᵐ[@Measure.prod X Y mX mY μ ν] fun z => g z.2 := by
  let : MeasurableSpace Y := mY
  have hm : mX.prod n ≤ mX.prod mY := by
    exact sup_le_sup le_rfl (MeasurableSpace.comap_mono hn)
  have hi : Integrable (fun z : X × Y => f z.2 - g z.2) (μ.prod ν) :=
    (measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable (hf.sub hg)
  have hb (B : Set Y) (hB : MeasurableSet[n] B) : (∫ y in B, f y - g y ∂ν) = 0 := by
    rw [integral_sub hf.integrableOn hg.integrableOn]
    have hc := setIntegral_condExp hn hf hB
    have heq : (∫ y in B, ν[f | n] y ∂ν) = ∫ y in B, g y ∂ν :=
      integral_congr_ae (ae_restrict_of_ae he)
    rw [heq] at hc
    exact sub_eq_zero.mpr hc.symm
  have hu : (∫ z : X × Y, f z.2 - g z.2 ∂μ.prod ν) = 0 := by
    calc
      _ = μ.real univ • ∫ y, f y - g y ∂ν := integral_fun_snd (fun y => f y - g y)
      _ = 0 := by
        have h : (∫ y, f y - g y ∂ν) = 0 := by
          simpa only [setIntegral_univ] using hb univ MeasurableSet.univ
        rw [h, smul_zero]
  have hall : ∀ A : Set (X × Y), MeasurableSet[mX.prod n] A →
      (∫ z in A, f z.2 - g z.2 ∂μ.prod ν) = 0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => (∫ z in A, f z.2 - g z.2 ∂μ.prod ν) = 0)
      (@generateFrom_prod X Y mX n).symm
      (@isPiSystem_prod X Y mX n) (by simp) ?_ ?_ ?_
    · intro A hA
      obtain ⟨S, hS, B, hB, rfl⟩ := hA
      have hmul : (fun z : X × Y => f z.2 - g z.2) =
          fun z => (1 : ℝ) * (f z.2 - g z.2) := by funext z; simp
      rw [hmul]
      calc
        _ = (∫ x in S, (1 : ℝ) ∂μ) * ∫ y in B, f y - g y ∂ν :=
          setIntegral_prod_mul (fun _ : X => (1 : ℝ)) (fun y => f y - g y) S B
        _ = 0 := by rw [hb B hB, mul_zero]
    · intro A hA hz
      rw [setIntegral_compl (hm A hA) hi, hu, hz, sub_self]
    · intro A hd hmA hz
      rw [integral_iUnion (fun k => hm _ (hmA k)) hd hi.integrableOn]
      simp only [hz, tsum_zero]
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm
    ((measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable hf)
  · exact fun _ _ _ =>
      ((measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable hg).integrableOn
  · intro A hA _
    have h := hall A hA
    change (∫ z in A, (f ∘ Prod.snd) z - (g ∘ Prod.snd) z ∂μ.prod ν) = 0 at h
    rw [integral_sub
      ((measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable hf).integrableOn
      ((measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable hg).integrableOn] at h
    exact (sub_eq_zero.mp h).symm
  · exact (hgm.comp_measurable (show @Measurable (X × Y) Y (mX.prod n) n Prod.snd from
      measurable_snd)).aestronglyMeasurable

end OperatorDerivativeRewrite.Foundation.IndependentInitialConditioning
