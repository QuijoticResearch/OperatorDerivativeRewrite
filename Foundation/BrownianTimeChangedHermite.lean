import Foundation.BrownianTimeChangedVariance
import Foundation.AmbientMartingaleModification
import Foundation.StickyNaturalMartingales

/-! All actual time-space Hermite martingales survive the endogenous clock.
The time argument is the random operational clock, not deterministic physical time. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianTimeChangedHermite
open InfiniteGaussian IBMConstructedSources GaussianTimeSpaceHermite
open BrownianMassRandomTimeChange BrownianMassClockStoppingTime
open BrownianTimeChangedMartingales ContinuousTimeChangeMartingale
open StickyNaturalClock StickyNaturalMartingales
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
  BrownianMassRandomTimeChange.inverse BrownianRandomMassClock.mass
  GaussianTimeSpaceHermite.value

theorem value_joint_continuous (n : ℕ) : Continuous (fun z : ℝ × ℝ => value n z.1 z.2) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa only [value_zero] using (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ)))
  | one => simpa only [value_one] using (continuous_fst : Continuous (fun z : ℝ × ℝ => z.1))
  | more n hn hn1 =>
    simp only [value_recursion]
    exact (continuous_fst.mul hn1).sub
      ((continuous_const.mul continuous_snd).mul hn)

def originalValue (n : ℕ) (t : ℝ≥0) (ω : SampleSpace) : ℝ :=
  value n (clockPath ω t) t

theorem original_measurable (n : ℕ) (t : ℝ≥0) : Measurable (originalValue n t) := by
  change Measurable (fun ω => value n (clockPath ω t) (t : ℝ))
  have hp : Measurable (fun ω => (clockPath ω t,(t : ℝ))) :=
    (BrownianAugmentedMartingales.brownian_coordinate_measurable t).prodMk measurable_const
  exact (value_joint_continuous n).measurable.comp hp

theorem original_continuous (n : ℕ) (ω : SampleSpace) :
    Continuous (fun t => originalValue n t ω) :=
  (value_joint_continuous n).comp
    ((clockPath ω).continuous.prodMk continuous_subtype_val)

theorem original_coordinate_ae (n : ℕ) (t : ℝ≥0) : originalValue n t =ᵐ[gaussianProduct]
    (fun ω => value n (GaussianTimeProcess.process t ω) t) :=
  (clockPath_coordinate_ae t).mono (fun _ h => congrArg (fun x => value n x t) h)

theorem original_martingale (n : ℕ) :
    Martingale (originalValue n) augmentedPast gaussianProduct :=
  AmbientMartingaleModification.martingale_modification gaussianProduct
    GaussianTimeProcess.naturalFiltration _ _ (GaussianHermiteMartingale.hermite_martingale n)
    (original_measurable n) (original_coordinate_ae n)

def changedValue (n : ℕ) (κ t : ℝ≥0) (ω : SampleSpace) : ℝ :=
  value n (changedPath κ ω t) (inverse κ ω t)

theorem changed_martingale (n : ℕ) (κ : ℝ≥0) :
    Martingale (changedValue n κ) (physicalPast κ) gaussianProduct :=
  ContinuousTimeChangeMartingale.changed_martingale gaussianProduct augmentedPast
    (originalValue n) (fun t ω => inverse κ ω t) (inverse_isStoppingTime κ)
    (fun ω => inverse_monotone κ ω) (original_martingale n) (original_continuous n)
    (fun t ω => inverse_le κ ω t)

theorem changed_natural_martingale (n : ℕ) (κ : ℝ≥0) :
    Martingale (changedValue n κ) (augmentedNaturalPast κ) gaussianProduct := by
  have hm := AmbientMartingaleModification.martingale_augmented gaussianProduct
    (physicalPast κ) _ (changed_martingale n κ)
  apply shrink gaussianProduct (augmentedNaturalPast κ) _ (augmented_le_physical κ) _ hm
  intro t
  exact ((value_joint_continuous n).measurable.comp
    ((state_augmented_adapted κ t).measurable.prodMk
      (continuous_subtype_val.measurable.comp (inverse_observed_past κ t)))).stronglyMeasurable

theorem value_four (x t : ℝ) : value 4 x t = x^4-6*t*x^2+3*t^2 := by
  rw [value_recursion 2,value_recursion 1,value_two,value_one]
  ring

theorem changed_fourth_integrable (κ t : ℝ≥0) : Integrable
    (fun ω => (changedPath κ ω t)^4-6*(inverse κ ω t : ℝ)*(changedPath κ ω t)^2+
      3*(inverse κ ω t : ℝ)^2) gaussianProduct := by
  have he : changedValue 4 κ t = (fun ω =>
      (changedPath κ ω t)^4-6*(inverse κ ω t : ℝ)*(changedPath κ ω t)^2+
        3*(inverse κ ω t : ℝ)^2) := by
    funext ω
    exact value_four _ _
  rw [← he]
  exact (changed_martingale 4 κ).integrable t

end OperatorDerivativeRewrite.Foundation.BrownianTimeChangedHermite
