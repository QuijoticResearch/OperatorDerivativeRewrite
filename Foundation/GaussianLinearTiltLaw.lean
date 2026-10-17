import Foundation.GaussianLinearLikelihoodMoments

/-! The linear terminal tilt decorrelates the actual time-one and time-two observations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianLinearTiltLaw
open InfiniteGaussian GaussianTimeProcess GaussianCore GaussianRandomTerminalMeasure
  GaussianCriticalExponential GaussianLinearLikelihoodMoments GaussianPastKernelTransport
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def Qlinear : Measure SampleSpace :=
  gaussianProduct.withDensity (fun ω => ENNReal.ofReal (linearDensity ω))

theorem Qlinear_probability : IsProbabilityMeasure Qlinear := by
  constructor
  change gaussianProduct.withDensity (fun ω => ENNReal.ofReal (linearDensity ω)) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  exact linearDensity_normalized

local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

theorem Qlinear_ac_P : Qlinear ≪ gaussianProduct := withDensity_absolutelyContinuous _ _

theorem P_ac_Qlinear : gaussianProduct ≪ Qlinear := by
  apply withDensity_absolutelyContinuous' linearDensity_measurable.ennreal_ofReal.aemeasurable
  exact Filter.Eventually.of_forall
    (fun ω => (ENNReal.ofReal_pos.mpr (linearDensity_positive ω)).ne')

def observationPair : SampleSpace → ℝ × ℝ := shift id ∘ coordinates

theorem observationPair_measurable : Measurable observationPair :=
  (shift_measurable measurable_id).comp
    ((process_stronglyMeasurable 1).measurable.prodMk
      ((process_stronglyMeasurable 2).measurable.sub (process_stronglyMeasurable 1).measurable))

theorem observationPair_eq (ω : SampleSpace) :
    observationPair ω = (process 1 ω, process 2 ω) := by
  ext <;> simp [observationPair, shift, coordinates]

theorem observation_lintegral (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (observationPair ω) ∂Qlinear) = ∫⁻ p, f p ∂γ.prod γ := by
  have hm : Measurable (fun p => ENNReal.ofReal (linearPair p)*f (shift id p)) :=
    linearPair_measurable.ennreal_ofReal.mul (hf.comp (shift_measurable measurable_id))
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (linearDensity ω)*f (observationPair ω) ∂gaussianProduct :=
      lintegral_withDensity_eq_lintegral_mul gaussianProduct
        linearDensity_measurable.ennreal_ofReal (hf.comp observationPair_measurable)
    _ = ∫⁻ p, ENNReal.ofReal (linearPair p)*f (shift id p) ∂γ.prod γ :=
      joint_law.lintegral_comp hm.aemeasurable
    _ = _ := weighted_lintegral γ id measurable_id f hf

theorem observation_hasLaw : HasLaw observationPair (γ.prod γ) Qlinear := by
  refine ⟨observationPair_measurable.aemeasurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf observationPair_measurable]
  exact observation_lintegral f hf

theorem first_law : HasLaw (process 1) γ Qlinear := by
  have hf : HasLaw (Prod.fst : ℝ × ℝ → ℝ) γ (γ.prod γ) :=
    ⟨measurable_fst.aemeasurable, by simp⟩
  exact hf.comp observation_hasLaw

theorem second_law : HasLaw (process 2) γ Qlinear := by
  have hs : HasLaw (Prod.snd : ℝ × ℝ → ℝ) γ (γ.prod γ) :=
    ⟨measurable_snd.aemeasurable, by simp⟩
  have h := hs.comp observation_hasLaw
  change HasLaw (fun ω => process 2 ω-process 1 ω+process 1 ω) γ Qlinear at h
  simpa only [sub_add_cancel] using h

theorem observations_independent : IndepFun (process 1) (process 2) Qlinear := by
  apply (indepFun_iff_hasLaw_prodMk_prod first_law second_law).mpr
  exact observation_hasLaw.congr
    (Filter.Eventually.of_forall (fun ω => (observationPair_eq ω).symm))

end OperatorDerivativeRewrite.Foundation.GaussianLinearTiltLaw
