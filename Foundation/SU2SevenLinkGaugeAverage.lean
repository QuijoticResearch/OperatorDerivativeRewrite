import Foundation.SU2SevenLinkMixing
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-! Actual gauge-randomized Markov kernels. Gauge averaging cannot change
any already gauge-invariant native covariance mode. No quotient/OS identification. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkGaugeAverage
open QuaternionSU2Representation SU2SevenLinkTransfer SU2SevenLinkGroundTransform
open SU2SevenLinkL2Transfer SU2SevenLinkVacuum
abbrev Gauge := Fin 6 → SU2

private instance su2_secondCountable : SecondCountableTopology SU2 := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  exact homeomorph.symm.secondCountableTopology
private instance state_borel : BorelSpace State := by infer_instance

private theorem action_measurable : Measurable (fun p : State × Gauge => gaugeAction p.2 p.1) := by
  apply Continuous.measurable
  unfold gaugeAction
  fun_prop

def gaugeHaar : Measure Gauge := Measure.pi (fun _ => law)
instance gaugeHaar_probability : IsProbabilityMeasure gaugeHaar := by unfold gaugeHaar; infer_instance

variable (ν : Measure Gauge) [IsProbabilityMeasure ν]
def randomizer : Kernel State State :=
  (Kernel.id ×ₖ Kernel.const State ν).map (fun p => gaugeAction p.2 p.1)

theorem randomizer_markov : IsMarkovKernel (randomizer ν) :=
  Kernel.IsMarkovKernel.map _ action_measurable

private instance randomizer_inst : IsMarkovKernel (randomizer ν) := randomizer_markov ν

theorem randomizer_apply (s : State) :
    randomizer ν s=ν.map (fun g => gaugeAction g s) := by
  rw [randomizer,Kernel.map_apply _ action_measurable,Kernel.prod_apply,
    Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map action_measurable measurable_prodMk_left]
  rfl

theorem randomizer_integral (f : State → ℝ) (hf : Measurable f) (s : State) :
    (∫ r,f r ∂randomizer ν s)=∫ g,f (gaugeAction g s) ∂ν := by
  have hm : Measurable (fun g : Gauge => gaugeAction g s) := by
    change Measurable ((fun p : State × Gauge => gaugeAction p.2 p.1) ∘ Prod.mk s)
    exact action_measurable.comp (measurable_const.prodMk measurable_id)
  rw [randomizer_apply]
  exact integral_map hm.aemeasurable hf.aestronglyMeasurable

variable {β t : ℝ} (d : GroundData β t)
private instance kernel_markov : IsMarkovKernel d.kernel := d.kernel_markov
private instance stationary_probability : IsProbabilityMeasure d.stationary := d.stationary_probability

def averagedKernel : Kernel State State := d.kernel ∘ₖ randomizer ν

theorem averagedKernel_markov : IsMarkovKernel (averagedKernel ν d) := by
  unfold averagedKernel
  infer_instance

private instance averaged_inst : IsMarkovKernel (averagedKernel ν d) := averagedKernel_markov ν d

theorem averaged_integral (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s,|f s| ≤ B) (s : State) :
    (∫ r,f r ∂averagedKernel ν d s)=∫ g,transfer d f (gaugeAction g s) ∂ν := by
  have hi : Integrable f (averagedKernel ν d s) := Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun r => by simpa only [Real.norm_eq_abs] using hb r)
  rw [averagedKernel,Kernel.integral_comp hi]
  exact randomizer_integral ν _ (transfer_measurable d f hf) s

theorem averaged_stationary (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s,|f s| ≤ B) :
    (∫ s,∫ r,f r ∂averagedKernel ν d s ∂d.stationary)=∫ s,f s ∂d.stationary := by
  simp_rw [averaged_integral ν d f hf B hb]
  have hi : Integrable (fun p : State × Gauge => transfer d f (gaugeAction p.2 p.1))
      (d.stationary.prod ν) := Integrable.of_bound
    ((transfer_measurable d f hf).comp action_measurable).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using transfer_bound d f B hb (gaugeAction p.2 p.1))
  rw [integral_integral_swap hi]
  simp_rw [stationary_integral_gauge d]
  simp only [integral_const,probReal_univ,one_smul]
  exact d.kernel_stationary f hf B hb

theorem invariant_integral (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s,|f s| ≤ B)
    (hg : ∀ (g : Gauge) s,f (gaugeAction g s)=f s) (s : State) :
    (∫ r,f r ∂averagedKernel ν d s)=transfer d f s := by
  rw [averaged_integral ν d f hf B hb]
  have he (g : Gauge) : transfer d f (gaugeAction g s)=transfer d f s := by
    change (∫ r,f r ∂d.kernel (gaugeAction g s))=_
    rw [kernel_integral_gauge d g f hf]
    simp_rw [hg g]
    rfl
  simp_rw [he]
  simp

def averagedSteps : ℕ → (State → ℝ) → State → ℝ
  | 0,f => f
  | n+1,f => fun s => ∫ r,averagedSteps n f r ∂averagedKernel ν d s

/-- Every actual time iterate agrees on invariant probes, for ANY probability
on gauge transformations, in particular the full six-vertex Haar law. -/
theorem invariant_steps (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s,|f s| ≤ B)
    (hg : ∀ (g : Gauge) s,f (gaugeAction g s)=f s) (n : ℕ) :
    averagedSteps ν d n f=nativeSteps d n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [averagedSteps,ih]
    funext s
    exact invariant_integral ν d _ (nativeSteps_measurable d n f hf) B
      (nativeSteps_bound d n f B hb) (nativeSteps_gauge d n f hf hg) s

/-- The existing native slow-mode obstruction survives actual gauge averaging,
including full product-Haar averaging at all six vertices. -/
theorem no_uniform_averaged_steps (n : ℕ) (q R : ℝ) (hq : q < 1) :
    ∃ β t : ℝ, R < β ∧ 0 < t ∧ t ≤ 1 ∧
      let v := (data β t).evenized
      let f := v.observable (SU2SevenLinkSpatialSeparation.oddA β)
        (SU2SevenLinkSpatialSeparation.oddB β)
      (∀ (g : Gauge) s,f (gaugeAction g s)=f s) ∧
      (∫ s,f s ∂v.stationary)=0 ∧ 0 < (∫ s,(f s)^2 ∂v.stationary) ∧
      q < (∫ s,f s*averagedSteps ν v n f s ∂v.stationary)/(∫ s,(f s)^2 ∂v.stationary) := by
  obtain ⟨β,t,hβ,ht,ht1,hg,hm,hv,hqv⟩ := SU2SevenLinkIteration.no_uniform_fixed_steps n q R hq
  let v := (data β t).evenized
  let A := SU2SevenLinkSpatialSeparation.oddA β
  let B := SU2SevenLinkSpatialSeparation.oddB β
  refine ⟨β,t,hβ,ht,ht1,hg,hm,hv,?_⟩
  rw [invariant_steps ν v _ (v.observable_measurable A B) _ (v.observable_bound A B) hg]
  exact hqv

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkGaugeAverage
