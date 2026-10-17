import Foundation.QuarticDualSemigroup
import Foundation.HigherHeatInitialObservable
import Mathlib.Analysis.Distribution.TemperedDistribution

/-! Genuine tempered-distribution coordinate duals, including their initial singularity. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.QuarticDualDistributions
open HigherHeatSpatialGenerator HigherHeatSchwartzJets QuarticAppellDualDensity
open HigherHeatSchwartzCalculus

def jetCLM : ℕ → 𝓢(ℝ,ℂ) →L[ℂ] 𝓢(ℝ,ℂ)
  | 0 => ContinuousLinearMap.id ℂ _
  | n+1 => (SchwartzMap.derivCLM ℂ ℂ).comp (jetCLM n)

theorem jetCLM_apply (n : ℕ) (f : 𝓢(ℝ,ℂ)) : jetCLM n f = jet n f := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [jetCLM, ContinuousLinearMap.comp_apply, jet, ih]

def initial (n : ℕ) : 𝓢'(ℝ,ℂ) :=
  ((n.factorial:ℂ)⁻¹) •
    PointwiseConvergenceCLM.precomp ℂ (jetCLM n) (TemperedDistribution.delta (0:ℝ))

theorem initial_apply (n : ℕ) (f : 𝓢(ℝ,ℂ)) :
    initial n f = jet n f 0 / (n.factorial:ℂ) := by
  change (n.factorial:ℂ)⁻¹ * (TemperedDistribution.delta (0:ℝ)) (jetCLM n f) = _
  rw [jetCLM_apply, TemperedDistribution.delta_apply]
  ring

theorem density_test (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (f : 𝓢(ℝ,ℂ)) :
    (density t ht n : 𝓢'(ℝ,ℂ)) f = mean 2 t (jet n f) / (n.factorial:ℂ) := by
  let K := GaussianSchwartzKernel.evenKernel 2 (by norm_num) t ht
  have hi : (∫ x : ℝ, f x * jet n K x) =
      (-1:ℂ)^n * (∫ x : ℝ, jet n f x * K x) := by
    calc
      _ = ∫ x : ℝ, jet n K x * f x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => mul_comm _ _
      _ = (-1:ℂ)^n * (∫ x : ℝ, K x * jet n f x) := integral_jet_mul n K f
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => mul_comm _ _
  have hs : (-1:ℂ)^n * (-1:ℂ)^n = 1 := by rw [← mul_pow]; norm_num
  rw [SchwartzMap.coe_apply]
  calc
    _ = ((-1:ℂ)^n / (n.factorial:ℂ)) * (∫ x : ℝ, f x * jet n K x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [density, SchwartzMap.smul_apply, smul_eq_mul, K]
        ring
    _ = (∫ x : ℝ, jet n f x * K x) / (n.factorial:ℂ) := by
      rw [hi]
      calc
        _ = ((-1:ℂ)^n * (-1:ℂ)^n) *
          ((∫ x : ℝ, jet n f x * K x) / (n.factorial:ℂ)) := by ring
        _ = _ := by rw [hs, one_mul]
    _ = _ := by
      rw [mean_eq_kernel 2 (by norm_num) t ht]
      simp only [HigherHeatSignedLaws.realKernel_coe, K]

def realized (n : ℕ) (t : ℝ≥0) : 𝓢'(ℝ,ℂ) :=
  if ht : 0 < t then (density t ht n : 𝓢'(ℝ,ℂ)) else initial n

theorem realized_apply (n : ℕ) (t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    realized n t f = mean 2 t (jet n f) / (n.factorial:ℂ) := by
  by_cases ht : 0 < t
  · rw [realized, dif_pos ht, density_test]
  · have ht0 : t=0 := le_antisymm (le_of_not_gt ht) (by positivity)
    subst t
    simp [realized, initial_apply, HigherHeatInitialObservable.mean_zero]

theorem realized_initial (n : ℕ) : realized n 0 = initial n := by simp [realized]

theorem realized_positive (n : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    realized n t = (density t ht n : 𝓢'(ℝ,ℂ)) := by simp [realized, ht]

theorem realized_continuous (n : ℕ) : Continuous (realized n) := by
  apply PointwiseConvergenceCLM.continuous_of_continuous_eval
  intro f
  simp only [realized_apply]
  exact (HigherHeatSchwartzContinuity.mean_continuous 2 (by norm_num) (jet n f)).div_const _

theorem realized_observable_generator (n : ℕ) (f : 𝓢(ℝ,ℂ)) (T : ℝ) (hT : 0 ≤ T) :
    HasDerivWithinAt (fun t : ℝ => realized n t.toNNReal f)
      (mean 2 T.toNNReal (differential 2 (jet n f)) / (n.factorial:ℂ)) (Set.Ici 0) T := by
  simp only [realized_apply]
  exact (HigherHeatInitialObservable.observable_hasDerivWithinAt 2 (jet n f) T hT).div_const _

end OperatorDerivativeRewrite.Foundation.QuarticDualDistributions
