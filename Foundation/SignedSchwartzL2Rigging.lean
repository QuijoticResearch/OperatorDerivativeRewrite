import Foundation.SignedSchwartzHigherWeights
import Foundation.MultiplierCore
import Mathlib.Analysis.Distribution.TemperedDistribution

/-! Actual L2 rigging for a signed Schwartz density, using bounded coefficients without a score. -/
noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzL2Rigging
open SignedAbsoluteIntegration

def measure (K : 𝓢(ℝ,ℝ)) : Measure ℝ := absoluteDensity volume K

instance finiteMeasure (K : 𝓢(ℝ,ℝ)) : IsFiniteMeasure (measure K) := by
  change IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal |K x|))
  have hi : Integrable (fun x : ℝ => |K x|) := by
    simpa only [Real.norm_eq_abs] using K.integrable.norm
  exact isFiniteMeasure_withDensity_ofReal hi.2

abbrev H (K : 𝓢(ℝ,ℝ)) := Lp ℂ 2 (measure K)

theorem kernel_nonzero_ae (K : 𝓢(ℝ,ℝ)) : ∀ᵐ x ∂measure K, K x≠0 := by
  have hm : Measurable (fun x : ℝ => |K x|) := by
    simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
  apply (ae_withDensity_iff hm.ennreal_ofReal).mpr
  exact Eventually.of_forall fun x hx hz => by simpa [hz] using hx

theorem abs_memLp_top (K : 𝓢(ℝ,ℝ)) : MemLp (fun x : ℝ => |K x|) ∞ (measure K) := by
  simpa only [Real.norm_eq_abs] using (K.memLp ∞ (measure K)).norm

def drift (K : 𝓢(ℝ,ℝ)) (x : ℝ) : ℝ :=
  if 0 ≤ K x then 2*deriv K x else -(2*deriv K x)

theorem drift_measurable (K : 𝓢(ℝ,ℝ)) : Measurable (drift K) := by
  have he : (fun x : ℝ => deriv K x) = (SchwartzMap.derivCLM ℝ ℝ K : ℝ → ℝ) := by
    funext x
    rw [SchwartzMap.derivCLM_apply]
  have hd : Measurable (fun x : ℝ => deriv K x) := by
    rw [he]
    exact (SchwartzMap.derivCLM ℝ ℝ K).continuous.measurable
  exact Measurable.ite (measurableSet_le measurable_const K.continuous.measurable)
    (measurable_const.mul hd) (measurable_const.mul hd).neg

theorem drift_density (K : 𝓢(ℝ,ℝ)) (x : ℝ) : |K x| * drift K x=2*K x*deriv K x := by
  by_cases hx : 0 ≤ K x
  · rw [drift, if_pos hx, abs_of_nonneg hx]
    ring
  · rw [drift, if_neg hx, abs_of_neg (lt_of_not_ge hx)]
    ring

theorem drift_memLp_top (K : 𝓢(ℝ,ℝ)) : MemLp (drift K) ∞ (measure K) := by
  apply memLp_top_of_bound (drift_measurable K).aestronglyMeasurable
    (2*SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ K))
  apply Eventually.of_forall
  intro x
  have hb := SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.derivCLM ℝ ℝ K) x
  rw [SchwartzMap.derivCLM_apply] at hb
  have he : ‖drift K x‖ = 2*‖deriv K x‖ := by
    unfold drift
    split_ifs <;> simp [norm_mul]
  rw [he]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

def distributionEmbedding (K : 𝓢(ℝ,ℝ)) : H K →L[ℝ] 𝓢'(ℝ,ℂ) :=
  (Lp.toTemperedDistributionCLM ℂ (measure K) 2).restrictScalars ℝ

theorem distributionEmbedding_injective (K : 𝓢(ℝ,ℝ)) :
    Function.Injective (distributionEmbedding K) := by
  have hi : Function.Injective (Lp.toTemperedDistributionCLM ℂ (measure K) 2) :=
    LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := measure K) (p := 2))
  exact hi

def embed (K : 𝓢(ℝ,ℝ)) : H K →L[ℝ] 𝓢'(ℝ,ℂ) :=
  (distributionEmbedding K).comp (boundedMultiplier (H := ℂ) (fun x => |K x|) (abs_memLp_top K))

def driftEmbedding (K : 𝓢(ℝ,ℝ)) : H K →L[ℝ] 𝓢'(ℝ,ℂ) :=
  (distributionEmbedding K).comp (boundedMultiplier (H := ℂ) (drift K) (drift_memLp_top K))

theorem embed_injective (K : 𝓢(ℝ,ℝ)) : Function.Injective (embed K) := by
  intro u v huv
  have hh := distributionEmbedding_injective K huv
  change boundedMultiplier (H := ℂ) (fun x => |K x|) (abs_memLp_top K) u =
    boundedMultiplier (H := ℂ) (fun x => |K x|) (abs_memLp_top K) v at hh
  apply Lp.ext
  filter_upwards [boundedMultiplier_coeFn (H := ℂ) (fun x => |K x|) (abs_memLp_top K) u,
    boundedMultiplier_coeFn (H := ℂ) (fun x => |K x|) (abs_memLp_top K) v,
    kernel_nonzero_ae K] with x hu hv hx
  have he : |K x| • u x = |K x| • v x := by
    calc
      _ = (boundedMultiplier (H := ℂ) (fun y => |K y|) (abs_memLp_top K) u) x := hu.symm
      _ = (boundedMultiplier (H := ℂ) (fun y => |K y|) (abs_memLp_top K) v) x :=
        congrArg (fun w : H K => w x) hh
      _ = _ := hv
  rw [Complex.real_smul, Complex.real_smul] at he
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)) he

end OperatorDerivativeRewrite.Foundation.SignedSchwartzL2Rigging
