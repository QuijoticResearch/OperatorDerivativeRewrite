import Foundation.SignedSchwartzLogDerivative
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! A transverse zero obstructs square integrability of a signed logarithmic derivative. -/
noncomputable section
open MeasureTheory Filter Set
open scoped SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.SignedScoreSimpleZero
open SignedSchwartzLogDerivative SignedAbsoluteIntegration

theorem local_bounds (K : 𝓢(ℝ,ℝ)) (hz : K 0=0) (hd : deriv K 0≠0) :
    ∃ C > 0, ∃ c > 0, ∃ δ > 0, ∀ x ∈ Ioo (0:ℝ) δ,
      |K x| ≤ C*x ∧ K x≠0 ∧ c ≤ |deriv K x| := by
  obtain ⟨C, hC, hb⟩ := (K.hasDerivAt 0).isBigO_sub.exists_pos
  have hk : ∀ᶠ x in 𝓝 (0:ℝ), |K x| ≤ C*|x| := by
    simpa only [hz, sub_zero, Real.norm_eq_abs] using hb.bound
  have hc : 0 < |deriv K 0|/2 := by positivity
  have hdc : Continuous (fun x : ℝ => |deriv K x|) := by
    have he : (fun x : ℝ => deriv K x) = (SchwartzMap.derivCLM ℝ ℝ K : ℝ → ℝ) := by
      funext x
      rw [SchwartzMap.derivCLM_apply]
    have hh : Continuous (fun x : ℝ => deriv K x) := by
      rw [he]
      exact (SchwartzMap.derivCLM ℝ ℝ K).continuous
    exact hh.abs
  have hh : ∀ᶠ x in 𝓝 (0:ℝ), |deriv K 0|/2 < |deriv K x| :=
    hdc.continuousAt.eventually (Ioi_mem_nhds (by linarith [abs_pos.mpr hd]))
  have hn : ∀ᶠ x in 𝓝[≠] (0:ℝ), K x≠0 := (K.hasDerivAt 0).eventually_ne hd
  have he : ∀ᶠ x in 𝓝[>] (0:ℝ),
      |K x| ≤ C*|x| ∧ K x≠0 ∧ |deriv K 0|/2 ≤ |deriv K x| := by
    filter_upwards [hk.filter_mono nhdsWithin_le_nhds,
      hn.filter_mono (nhdsGT_le_nhdsNE 0), hh.filter_mono nhdsWithin_le_nhds] with x hx hnx hdx
    exact ⟨hx, hnx, hdx.le⟩
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨C, hC, |deriv K 0|/2, hc, δ, hδ, fun x hx => ?_⟩
  simpa only [mem_setOf_eq, abs_of_pos hx.1] using hsub hx

theorem fisher_not_integrable (K : 𝓢(ℝ,ℝ)) (hz : K 0=0) (hd : deriv K 0≠0) :
    ¬ Integrable (fun x : ℝ => (deriv K x)^2 / |K x|) := by
  intro hi
  obtain ⟨C, hC, c, hc, δ, hδ, hb⟩ := local_bounds K hz hd
  have hInv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioo 0 δ) := by
    apply ((hi.const_mul (C/c^2)).integrableOn).mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    obtain ⟨hk, hkn, hdk⟩ := hb x hx
    have hka : 0 < |K x| := abs_pos.mpr hkn
    have hs : c^2 ≤ (deriv K x)^2 := by nlinarith [sq_abs (deriv K x)]
    have hm := mul_le_mul hk hs (sq_nonneg c) (le_of_lt (mul_pos hC hx.1))
    simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hx.1]
    rw [← one_div x]
    have he : (C/c^2)*((deriv K x)^2/|K x|) =
        (C*(deriv K x)^2)/(c^2*|K x|) := by ring
    rw [he]
    apply (div_le_div_iff₀ hx.1 (mul_pos (sq_pos_of_pos hc) hka)).mpr
    nlinarith [hm]
  have hh : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 δ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).mpr hInv
  simpa [intervalIntegrable_inv_iff, ne_of_lt hδ] using hh

theorem score_not_memLp_two (K : 𝓢(ℝ,ℝ)) (hz : K 0=0) (hd : deriv K 0≠0) :
    ¬ MemLp (fun x : ℝ => (score K x:ℂ)) 2 (absoluteDensity volume K) := by
  intro hp
  have hi := (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  have hmabs : Measurable (fun x : ℝ => |K x|) := by
    simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
  have ht := (integrable_withDensity_iff_integrable_smul₀' hmabs.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hi
  apply fisher_not_integrable K hz hd
  apply ht.congr
  filter_upwards [score_cancel K] with x hx
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  by_cases hzero : K x=0
  · have hdzero : deriv K x=0 := by simpa only [hzero, zero_mul, neg_eq_zero] using hx.symm
    simp [hzero, hdzero]
  · simp only [smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, score,
      div_pow, neg_sq]
    rw [← sq_abs (K x)]
    field_simp [abs_ne_zero.mpr hzero]

end OperatorDerivativeRewrite.Foundation.SignedScoreSimpleZero
