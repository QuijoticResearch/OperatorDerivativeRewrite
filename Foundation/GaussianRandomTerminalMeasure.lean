import Foundation.GaussianRandomDensityKernel
import Foundation.GaussianRandomDriftCausality

/-! A normalized equivalent terminal measure for the actual delayed Brownian step. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianRandomTerminalMeasure
open InfiniteGaussian GaussianTimeProcess GaussianPredictableFull GaussianRandomStepDrift
  VolterraRandomStepDrift GaussianRandomDensityKernel GaussianCore
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def coordinates (ω : SampleSpace) : ℝ × ℝ := (process 1 ω,process 2 ω-process 1 ω)

theorem future_law : HasLaw (fun ω => process 2 ω-process 1 ω) γ gaussianProduct := by
  have ht := process_increment_hasLaw 1 2
  norm_num at ht
  have hd : nndist (2 : ℝ) 1=1 := by
    apply NNReal.coe_injective
    change dist (2 : ℝ) 1=(1 : ℝ)
    norm_num [Real.dist_eq]
  rw [hd] at ht
  exact ht

theorem past_future_independent : IndepFun (process 1) (fun ω => process 2 ω-process 1 ω) gaussianProduct := by
  have ht := GaussianPredictableStep.pastCoefficient_indep_increment
    process_isPreBrownian (s := 1) (t := 2) (by norm_num)
    (a := fun z : Iic (1 : ℝ≥0) → ℝ => z ⟨1,by simp⟩)
    (measurable_pi_apply (⟨1,by simp⟩ : Iic (1 : ℝ≥0)))
  change IndepFun (process 1) (fun ω => process 2 ω-process 1 ω) gaussianProduct at ht
  exact ht

theorem joint_law : HasLaw coordinates (γ.prod γ) gaussianProduct :=
  past_future_independent.hasLaw_prod (process_hasLaw 1) future_law

def density : SampleSpace → ℝ := pairDensity ∘ coordinates

theorem density_measurable : Measurable density :=
  pairDensity_continuous.measurable.comp
    ((process_stronglyMeasurable 1).measurable.prodMk
      ((process_stronglyMeasurable 2).measurable.sub (process_stronglyMeasurable 1).measurable))

theorem density_positive (ω : SampleSpace) : 0<density ω := pairDensity_positive _

theorem density_integrable : Integrable density gaussianProduct :=
  joint_law.integrable_comp pairDensity_integrable

theorem density_integral : (∫ ω, density ω ∂gaussianProduct)=1 := by
  calc
    _ = ∫ p, pairDensity p ∂γ.prod γ :=
      joint_law.integral_comp pairDensity_continuous.measurable.aestronglyMeasurable
    _ = 1 := pairDensity_integral

def Q : Measure SampleSpace := gaussianProduct.withDensity (fun ω => ENNReal.ofReal (density ω))

theorem Q_probability : IsProbabilityMeasure Q := by
  constructor
  change gaussianProduct.withDensity (fun ω => ENNReal.ofReal (density ω)) univ=1
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal density_integrable
    (Filter.Eventually.of_forall (fun ω => (density_positive ω).le)),density_integral]
  norm_num

theorem Q_ac_P : Q≪gaussianProduct := withDensity_absolutelyContinuous _ _

theorem P_ac_Q : gaussianProduct≪Q := by
  apply withDensity_absolutelyContinuous'
    density_measurable.ennreal_ofReal.aemeasurable
  exact Filter.Eventually.of_forall (fun ω => (ENNReal.ofReal_pos.mpr (density_positive ω)).ne')

theorem density_terminal_form : density=ᵐ[gaussianProduct] fun ω =>
    Real.exp (-itoIntegral thetaField ω-(∫ s in (0 : ℝ)..2, rawTheta process s ω^2)/2) := by
  filter_upwards [stochastic_integral_value] with ω hω
  rw [hω,energy_two]
  simp only [density,Function.comp_apply,coordinates,pairDensity,kernel,coefficient,neg_mul]

theorem Q_drift_not_constant (c : ℝ) : ¬drift process 2=ᵐ[Q] fun _ => c :=
  drift_not_constant_of_ac process (process_hasLaw 1) Q P_ac_Q c

theorem Q_drift_variance_positive : 0<Var[drift process 2; Q] := by
  letI : IsProbabilityMeasure Q := Q_probability
  have hm : MemLp (drift process 2) 2 Q :=
    drift_memLp process (fun t => (process_stronglyMeasurable t).measurable)
  have hn : Var[drift process 2; Q]≠0 := by
    intro h
    exact Q_drift_not_constant _ (ae_eq_integral_of_variance_eq_zero hm h)
  exact lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hn)

end OperatorDerivativeRewrite.Foundation.GaussianRandomTerminalMeasure
