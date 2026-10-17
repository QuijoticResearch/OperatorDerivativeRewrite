import Foundation.SignedDensityIntegral
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Uniqueness of actual finite signed laws from their characteristic integrals. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.SignedFourierUniqueness
open SignedDensityIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def character (L : StrongDual ℝ E) (x : E) : ℂ := Complex.exp ((L x : ℂ)*Complex.I)

theorem character_measurable (L : StrongDual ℝ E) : Measurable (character L) := by
  unfold character
  fun_prop

theorem character_norm (L : StrongDual ℝ E) (x : E) : ‖character L x‖=1 := by
  simp [character,Complex.norm_exp]

theorem character_integrable (μ : Measure E) [IsFiniteMeasure μ] (L : StrongDual ℝ E) :
    Integrable (character L) μ := Integrable.of_bound (character_measurable L).aestronglyMeasurable 1
      (Eventually.of_forall fun x => (character_norm L x).le)

def signedCharFun (ν : SignedMeasure E) (L : StrongDual ℝ E) : ℂ :=
  ∫ᵛ x, character L x ∂<•ν

theorem signedCharFun_jordan (ν : SignedMeasure E) (L : StrongDual ℝ E) :
    signedCharFun ν L=charFunDual ν.toJordanDecomposition.posPart L-
      charFunDual ν.toJordanDecomposition.negPart L := by
  unfold signedCharFun
  conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure,
    VectorMeasure.integral_sub_vectorMeasure
      (bounded_signed_integrable _ _ (character_measurable L) 1 (fun x => (character_norm L x).le))
      (bounded_signed_integrable _ _ (character_measurable L) 1 (fun x => (character_norm L x).le)),
    VectorMeasure.integral_toSignedMeasure,VectorMeasure.integral_toSignedMeasure]
  rfl

theorem signed_ext [SecondCountableTopology E] [CompleteSpace E]
    (ν μ : SignedMeasure E) (h : signedCharFun ν=signedCharFun μ) : ν=μ := by
  have hc : charFunDual (ν.toJordanDecomposition.posPart+μ.toJordanDecomposition.negPart) =
      charFunDual (μ.toJordanDecomposition.posPart+ν.toJordanDecomposition.negPart) := by
    funext L
    simp only [charFunDual_apply]
    change (∫ x, character L x ∂(ν.toJordanDecomposition.posPart+μ.toJordanDecomposition.negPart)) =
      ∫ x, character L x ∂(μ.toJordanDecomposition.posPart+ν.toJordanDecomposition.negPart)
    rw [integral_add_measure (character_integrable _ L) (character_integrable _ L),
      integral_add_measure (character_integrable _ L) (character_integrable _ L)]
    have hh := congrFun h L
    rw [signedCharFun_jordan,signedCharFun_jordan] at hh
    exact sub_eq_sub_iff_add_eq_add.mp hh
  have hm := Measure.ext_of_charFunDual hc
  ext A hA
  rw [SignedMeasure.apply_eq_posPart_real_sub_negPart_real _ hA,
    SignedMeasure.apply_eq_posPart_real_sub_negPart_real _ hA]
  have hv := congrArg (fun ρ : Measure E => ρ.real A) hm
  rw [measureReal_add_apply,measureReal_add_apply] at hv
  exact sub_eq_sub_iff_add_eq_add.mpr hv

open scoped Classical
variable {ι : Type*} [Fintype ι]

def finiteFrequencies (L : StrongDual ℝ (ι → ℝ)) (i : ι) : ℝ := by
  classical
  exact -(L (Pi.single i 1))/(2*Real.pi)

theorem finite_dual_sum (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = ∑ i, x i*L (Pi.single i 1) := by
  classical
  calc
    L x = L (∑ i, Pi.single i (x i)) := congrArg L (Finset.univ_sum_single x).symm
    _ = ∑ i, L (Pi.single i (x i)) := by rw [map_sum]
    _ = ∑ i, x i*L (Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have he : Pi.single i (x i) = x i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
        ext j
        by_cases hj : j=i <;> simp [hj,Pi.single_apply]
      rw [he,map_smul]
      rfl

theorem finite_character (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    character L x=configurationPhase (finiteFrequencies L) x := by
  classical
  have hp : (2*Real.pi) ≠ 0 := by positivity
  have hs : (∑ i, finiteFrequencies L i*x i) = -(L x)/(2*Real.pi) := by
    rw [finite_dual_sum L x]
    unfold finiteFrequencies
    rw [← Finset.sum_neg_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [configurationPhase,hs,Real.fourierChar_apply,character]
  congr 1
  push_cast
  field_simp

theorem finite_signed_ext (ν μ : SignedMeasure (ι → ℝ))
    (h : ∀ ξ : ι → ℝ, (∫ᵛ x, configurationPhase ξ x ∂<•ν) =
      ∫ᵛ x, configurationPhase ξ x ∂<•μ) : ν=μ := by
  apply signed_ext ν μ
  funext L
  unfold signedCharFun
  simp_rw [finite_character]
  exact h (finiteFrequencies L)

end OperatorDerivativeRewrite.Foundation.SignedFourierUniqueness
