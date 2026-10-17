import Foundation.GaussianDensityTranslation
import Foundation.GaussianRandomTerminalMeasure

/-! The corrected terminal noise is independent standard Gaussian under the constructed measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianCorrectedTerminalLaw
open InfiniteGaussian GaussianTimeProcess GaussianCore GaussianRandomDensityKernel
  GaussianDensityTranslation GaussianRandomTerminalMeasure
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Q := Q_probability

def corrected (p : ℝ × ℝ) : ℝ × ℝ := (p.1,p.2+Real.sin p.1)

def correctedCoordinates : SampleSpace → ℝ × ℝ := corrected ∘ coordinates

def noise (ω : SampleSpace) : ℝ := process 2 ω-process 1 ω+Real.sin (process 1 ω)

theorem corrected_measurable : Measurable corrected := by
  unfold corrected
  fun_prop

theorem coordinates_measurable : Measurable coordinates :=
  (process_stronglyMeasurable 1).measurable.prodMk
    ((process_stronglyMeasurable 2).measurable.sub (process_stronglyMeasurable 1).measurable)

theorem correctedCoordinates_measurable : Measurable correctedCoordinates :=
  corrected_measurable.comp coordinates_measurable

theorem pair_weighted_lintegral (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, ENNReal.ofReal (pairDensity p)*f (corrected p) ∂γ.prod γ)=∫⁻ p, f p ∂γ.prod γ := by
  have hm : Measurable (fun p => ENNReal.ofReal (pairDensity p)*f (corrected p)) :=
    pairDensity_continuous.measurable.ennreal_ofReal.mul (hf.comp corrected_measurable)
  rw [lintegral_prod _ hm.aemeasurable,lintegral_prod f hf.aemeasurable]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    fiber_lintegral (Real.sin x) (fun z => f (x,z))
      (hf.comp (measurable_const.prodMk measurable_id)))

theorem corrected_lintegral (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (correctedCoordinates ω) ∂Q)=∫⁻ p, f p ∂γ.prod γ := by
  have hm : Measurable (fun p => ENNReal.ofReal (pairDensity p)*f (corrected p)) :=
    pairDensity_continuous.measurable.ennreal_ofReal.mul (hf.comp corrected_measurable)
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (density ω)*f (correctedCoordinates ω) ∂gaussianProduct :=
      lintegral_withDensity_eq_lintegral_mul gaussianProduct density_measurable.ennreal_ofReal
        (hf.comp correctedCoordinates_measurable)
    _ = ∫⁻ p, ENNReal.ofReal (pairDensity p)*f (corrected p) ∂γ.prod γ :=
      joint_law.lintegral_comp hm.aemeasurable
    _ = _ := pair_weighted_lintegral f hf

theorem corrected_hasLaw : HasLaw correctedCoordinates (γ.prod γ) Q := by
  refine ⟨correctedCoordinates_measurable.aemeasurable,?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf correctedCoordinates_measurable]
  exact corrected_lintegral f hf

theorem past_law_Q : HasLaw (process 1) γ Q := by
  have hf : HasLaw (Prod.fst : ℝ × ℝ → ℝ) γ (γ.prod γ) :=
    ⟨measurable_fst.aemeasurable,by simp⟩
  exact hf.comp corrected_hasLaw

theorem noise_law_Q : HasLaw noise γ Q := by
  have hs : HasLaw (Prod.snd : ℝ × ℝ → ℝ) γ (γ.prod γ) :=
    ⟨measurable_snd.aemeasurable,by simp⟩
  exact hs.comp corrected_hasLaw

theorem corrected_independent : IndepFun (process 1) noise Q := by
  apply (indepFun_iff_hasLaw_prodMk_prod past_law_Q noise_law_Q).mpr
  exact corrected_hasLaw

end OperatorDerivativeRewrite.Foundation.GaussianCorrectedTerminalLaw
