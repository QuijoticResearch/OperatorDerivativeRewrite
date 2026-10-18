import Foundation.GaussianSchwartzKernel
import Foundation.HigherHeatSchwartzJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! A single Schwartz cutoff sequence with bounded jets of every order. -/
noncomputable section
open Filter
open scoped SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.SchwartzGaussianCutoff
open GaussianSchwartzKernel HigherHeatSpatialGenerator

def scale (n : ℕ) : ℝ := 1 / ((n : ℝ)+1)

theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

theorem scale_le_one (n : ℕ) : scale n ≤ 1 := by
  unfold scale
  apply (div_le_one (by positivity)).mpr
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem scale_tendsto_zero : Tendsto scale atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

def scalarEquiv (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv

def cutoff (n : ℕ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (scalarEquiv (scale n) (scale_pos n).ne') complexSchwartz

theorem cutoff_apply (n : ℕ) (x : ℝ) : cutoff n x = complexSchwartz (scale n * x) := rfl

theorem cutoff_jet (k n : ℕ) (x : ℝ) :
    iteratedDeriv k (cutoff n : ℝ → ℂ) x =
      scale n ^ k • iteratedDeriv k (complexSchwartz : ℝ → ℂ) (scale n * x) := by
  have he : (cutoff n : ℝ → ℂ) = (fun y => complexSchwartz (scale n*y)) := funext (cutoff_apply n)
  rw [he, iteratedDeriv_comp_const_smul (complexSchwartz.smooth k) (scale n)]

def jetBound (k : ℕ) : ℝ := SchwartzMap.seminorm ℂ 0 0 (jet k complexSchwartz)

theorem base_jet_bound (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (complexSchwartz : ℝ → ℂ) x‖ ≤ jetBound k := by
  rw [← jet_coe]
  exact SchwartzMap.norm_le_seminorm ℂ _ x

theorem jetBound_nonneg (k : ℕ) : 0 ≤ jetBound k :=
  (norm_nonneg _).trans (base_jet_bound k 0)

theorem cutoff_jet_bound (k n : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (cutoff n : ℝ → ℂ) x‖ ≤ jetBound k := by
  rw [cutoff_jet, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos (scale_pos n)]
  calc
    _ ≤ 1 * jetBound k := mul_le_mul
      (pow_le_one₀ (scale_pos n).le (scale_le_one n)) (base_jet_bound k _)
      (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem cutoff_jet_tendsto (k : ℕ) (x : ℝ) :
    Tendsto (fun n => iteratedDeriv k (cutoff n : ℝ → ℂ) x) atTop
      (𝓝 (if k = 0 then (1 : ℂ) else 0)) := by
  have harg : Tendsto (fun n => scale n * x) atTop (𝓝 0) := by
    simpa using scale_tendsto_zero.mul_const x
  have hc : Continuous (iteratedDeriv k (complexSchwartz : ℝ → ℂ)) := by
    rw [← jet_coe]
    exact (jet k complexSchwartz).continuous
  have hj := hc.continuousAt.tendsto.comp harg
  by_cases hk : k = 0
  · subst k
    have hzero : complexSchwartz 0 = (1 : ℂ) := by simp [complexSchwartz_apply, gaussian]
    have ht : Tendsto (fun n => complexSchwartz (scale n * x)) atTop (𝓝 (1 : ℂ)) := by
      simpa only [iteratedDeriv_zero, Function.comp_def, hzero] using hj
    simpa only [cutoff_jet, pow_zero, one_smul, iteratedDeriv_zero, ite_true] using ht
  · have hs : Tendsto (fun n => scale n ^ k) atTop (𝓝 0) := by
      simpa [zero_pow hk] using scale_tendsto_zero.pow k
    simpa only [Function.comp_def, cutoff_jet, hk, ite_false, zero_smul] using hs.smul hj

end OperatorDerivativeRewrite.Foundation.SchwartzGaussianCutoff
