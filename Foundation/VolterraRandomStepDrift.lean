import Foundation.GaussianTimeProcess
import Foundation.GaussianPredictableStep
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! A bounded predictable delayed coefficient whose time-integrated drift is random. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.VolterraRandomStepDrift
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def coefficient (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ := Real.sin (B 1 ω)

def pastFunction : (Iic (1 : ℝ≥0) → ℝ) → ℝ := fun z => Real.sin (z ⟨1,by simp⟩)

def theta (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  GaussianPredictableStep.stepProcess B 1 2 pastFunction

def rawTheta (B : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  (Ioc (1 : ℝ) 2).indicator (fun _ => coefficient B ω) s

def drift (B : ℝ≥0 → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  -(∫ s in (0 : ℝ)..T, rawTheta B s ω)

theorem pastFunction_measurable : Measurable pastFunction := by
  exact Real.measurable_sin.comp (measurable_pi_apply (⟨1,by simp⟩ : Iic (1 : ℝ≥0)))

theorem past_coefficient (B : ℝ≥0 → Ω → ℝ) :
    GaussianPredictableStep.pastCoefficient B 1 pastFunction=coefficient B := rfl

theorem theta_predictable (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t)) :
    IsStronglyPredictable (Filtration.natural B (fun t => (hBm t).stronglyMeasurable)) (theta B) :=
  GaussianPredictableStep.stepProcess_stronglyPredictable hBm 1 2 pastFunction_measurable

theorem coefficient_measurable (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t)) :
    Measurable (coefficient B) := Real.measurable_sin.comp (hBm 1)

theorem coefficient_bound (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : |coefficient B ω|≤1 :=
  Real.abs_sin_le_one _

theorem coefficient_memLp (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t)) :
    MemLp (coefficient B) 2 μ := by
  apply (memLp_const (1 : ℝ)).mono' (coefficient_measurable B hBm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using coefficient_bound B ω)

theorem theta_eq_raw (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    theta B t ω=rawTheta B t ω := by
  have hm : (t : ℝ)∈Ioc (1 : ℝ) 2 ↔ t∈Ioc (1 : ℝ≥0) 2 := by
    change (1<(t : ℝ) ∧ (t : ℝ)≤2) ↔ (1<t ∧ t≤2)
    norm_cast
  by_cases ht : t∈Ioc (1 : ℝ≥0) 2
  · have hr := hm.mpr ht
    simp [theta,rawTheta,GaussianPredictableStep.stepProcess,past_coefficient,ht,hr]
  · have hr : (t : ℝ)∉Ioc (1 : ℝ) 2 := fun h => ht (hm.mp h)
    simp [theta,rawTheta,GaussianPredictableStep.stepProcess,past_coefficient,ht,hr]

theorem rawTheta_bound (B : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) : |rawTheta B s ω|≤1 := by
  by_cases h : s∈Ioc (1 : ℝ) 2
  · simpa [rawTheta,h] using coefficient_bound B ω
  · simp [rawTheta,h]

theorem integral_step (c : ℝ) :
    (∫ s in (0 : ℝ)..2, (Ioc (1 : ℝ) 2).indicator (fun _ => c) s)=c := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤2),
    integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc]
  have h : Ioc (1 : ℝ) 2⊆Ioc (0 : ℝ) 2 := by
    intro x hx
    exact ⟨lt_trans (by norm_num) hx.1,hx.2⟩
  rw [inter_eq_left.mpr h]
  norm_num

theorem drift_two (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : drift B 2 ω=-coefficient B ω := by
  change -(∫ s in (0 : ℝ)..2, (Ioc (1 : ℝ) 2).indicator (fun _ => coefficient B ω) s)=
    -coefficient B ω
  rw [integral_step]

theorem energy_two (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫ s in (0 : ℝ)..2, rawTheta B s ω^2)=coefficient B ω^2 := by
  have he : (fun s : ℝ => rawTheta B s ω^2)=
      (Ioc (1 : ℝ) 2).indicator (fun _ => coefficient B ω^2) := by
    funext s
    by_cases h : s∈Ioc (1 : ℝ) 2 <;> simp [rawTheta,h]
  rw [he,integral_step]

theorem energy_bound (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫ s in (0 : ℝ)..2, rawTheta B s ω^2)≤1 := by
  rw [energy_two]
  exact Real.sin_sq_le_one _

theorem novikov_integrable (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t)) :
    Integrable (fun ω => Real.exp ((∫ s in (0 : ℝ)..2, rawTheta B s ω^2)/2)) μ := by
  have he : (fun ω => Real.exp ((∫ s in (0 : ℝ)..2, rawTheta B s ω^2)/2))=
      fun ω => Real.exp (coefficient B ω^2/2) := by funext ω; rw [energy_two]
  rw [he]
  apply Integrable.mono' (integrable_const (Real.exp ((1 : ℝ)/2)))
    (((coefficient_measurable B hBm).pow_const 2).div_const 2).exp.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hs := Real.sin_sq_le_one (B 1 ω)
    change coefficient B ω^2≤1 at hs
    linarith)

theorem coefficient_not_constant (B : ℝ≥0 → Ω → ℝ)
    (hLaw : HasLaw (B 1) (gaussianReal 0 1) μ) (c : ℝ) :
    ¬coefficient B=ᵐ[μ] fun _ => c := by
  intro h
  have hm : Measurable (fun x : ℝ => Real.sin x=c) :=
    measurableSet_setOfPred.mp (measurableSet_eq_fun Real.measurable_sin measurable_const)
  have hg : (∀ᵐ x ∂gaussianReal 0 1, Real.sin x=c) := (hLaw.ae_iff hm).mp h
  have hv : Real.sin=ᵐ[(volume : Measure ℝ)] fun _ => c :=
    (gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num)).ae_le hg
  have he := MeasureTheory.Measure.eq_of_ae_eq hv Real.continuous_sin continuous_const
  have h0 := congrFun he 0
  have h1 := congrFun he (Real.pi/2)
  rw [Real.sin_zero] at h0
  rw [Real.sin_pi_div_two] at h1
  linarith

theorem drift_not_constant (B : ℝ≥0 → Ω → ℝ)
    (hLaw : HasLaw (B 1) (gaussianReal 0 1) μ) (c : ℝ) :
    ¬drift B 2=ᵐ[μ] fun _ => c := by
  intro h
  apply coefficient_not_constant B hLaw (-c)
  filter_upwards [h] with ω hω
  rw [drift_two] at hω
  linarith

theorem drift_memLp (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t)) :
    MemLp (drift B 2) 2 μ := by
  have he : drift B 2=-coefficient B := by funext ω; exact drift_two B ω
  rw [he]
  exact (coefficient_memLp B hBm).neg

theorem drift_variance_positive (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t))
    (hLaw : HasLaw (B 1) (gaussianReal 0 1) μ) : 0<Var[drift B 2; μ] := by
  have hn : Var[drift B 2; μ]≠0 := by
    intro h
    exact drift_not_constant B hLaw _ (ae_eq_integral_of_variance_eq_zero (drift_memLp B hBm) h)
  exact lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hn)

theorem drift_not_constant_of_ac (B : ℝ≥0 → Ω → ℝ)
    (hLaw : HasLaw (B 1) (gaussianReal 0 1) μ) (ν : Measure Ω) (hμν : μ≪ν) (c : ℝ) :
    ¬drift B 2=ᵐ[ν] fun _ => c := by
  intro h
  exact drift_not_constant B hLaw c (hμν.ae_le h)

theorem actual_drift_not_constant (c : ℝ) :
    ¬drift GaussianTimeProcess.process 2=ᵐ[InfiniteGaussian.gaussianProduct] fun _ => c :=
  drift_not_constant _ (GaussianTimeProcess.process_hasLaw 1) c

end OperatorDerivativeRewrite.Foundation.VolterraRandomStepDrift
