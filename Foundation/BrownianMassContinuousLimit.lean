import Foundation.BrownianMassFastSubsequence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! A measurable continuous path limit of the constructed smooth mass paths.
Occupation and support identities are not assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianMassContinuousLimit
open InfiniteGaussian BrownianSmoothMassPath BrownianMassFastSubsequence

def Good (ω : SampleSpace) : Prop := ∀ᶠ j : ℕ in atTop,
  ∀ t : ℝ≥0, t ≤ (j + 1 : ℝ≥0) →
    ‖path (subsequence j) ω t - path (subsequence (j + 1)) ω t‖ ≤ (tolerance j : ℝ)

theorem good_ae : ∀ᵐ ω ∂gaussianProduct, Good ω := ae_eventual_increment

def restriction (T : ℝ≥0) (ω : SampleSpace) (j : ℕ) : C(Icc (0 : ℝ≥0) T, ℝ) :=
  ⟨fun t => path (subsequence j) ω t,
    (path (subsequence j) ω).continuous.comp continuous_subtype_val⟩

theorem restriction_cauchy {ω : SampleSpace} (hg : Good ω) (T : ℝ≥0) :
    CauchySeq (restriction T ω) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hg
  obtain ⟨K, hK⟩ := exists_nat_gt (T : ℝ)
  let J := max N K
  apply (cauchySeq_shift J).mp
  apply cauchySeq_of_le_geometric (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ J) (by norm_num)
  intro j
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  have ht' : t.val ≤ ((j + J : ℕ) : ℝ≥0) + 1 := by
    have hKT : T ≤ (K : ℝ≥0) := by exact_mod_cast hK.le
    have hj : (K : ℝ≥0) ≤ ((j + J : ℕ) : ℝ≥0) + 1 := by
      exact_mod_cast (show K ≤ j + J + 1 by dsimp [J]; omega)
    exact t.property.2.trans (hKT.trans hj)
  have h := hN (j + J) (by dsimp [J]; omega) t.val ht'
  have he : j + 1 + J = j + J + 1 := by omega
  simpa only [restriction, ContinuousMap.coe_mk, Real.dist_eq, ← Real.norm_eq_abs,
    he, tolerance, NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat,
    pow_add, mul_comm] using h

theorem selected_cauchy {ω : SampleSpace} (hg : Good ω) :
    CauchySeq (fun j => path (subsequence j) ω) := by
  apply (Metric.uniformity_basis_dist.compactConvergenceUniformity
    (α := ℝ≥0)).cauchySeq_iff.mpr
  rintro ⟨K, ε⟩ ⟨hK, hε⟩
  obtain ⟨T, hT⟩ := hK.bddAbove
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (restriction_cauchy hg T) ε hε
  refine ⟨N, fun n hn m hm t ht => ?_⟩
  exact (ContinuousMap.dist_apply_le_dist (f := restriction T ω n)
    (g := restriction T ω m) ⟨t, ⟨t.property, hT ht⟩⟩).trans_lt (hN n hn m hm)

def rawLimit (ω : SampleSpace) : C(ℝ≥0, ℝ) := by
  classical
  exact if hg : Good ω then
    Classical.choose (cauchySeq_tendsto_of_complete (selected_cauchy hg)) else 0

theorem rawLimit_tendsto {ω : SampleSpace} (hg : Good ω) :
    Tendsto (fun j => path (subsequence j) ω) atTop (𝓝 (rawLimit ω)) := by
  simp only [rawLimit, dite_eq_left hg]
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete (selected_cauchy hg))

theorem rawLimit_aemeasurable : AEMeasurable rawLimit gaussianProduct := by
  apply aemeasurable_of_tendsto_metrizable_ae'
    (fun j => (path_measurable (subsequence j)).aemeasurable)
  exact good_ae.mono (fun _ hg => rawLimit_tendsto hg)

def limitPath : SampleSpace → C(ℝ≥0, ℝ) := rawLimit_aemeasurable.mk rawLimit

theorem limitPath_measurable : Measurable limitPath := rawLimit_aemeasurable.measurable_mk

theorem limitPath_tendsto : ∀ᵐ ω ∂gaussianProduct,
    Tendsto (fun j => path (subsequence j) ω) atTop (𝓝 (limitPath ω)) := by
  filter_upwards [good_ae, rawLimit_aemeasurable.ae_eq_mk] with ω hg he
  change rawLimit ω = limitPath ω at he
  rw [← he]
  exact rawLimit_tendsto hg

theorem limitPath_uniform : ∀ᵐ ω ∂gaussianProduct, ∀ T : ℝ≥0,
    TendstoUniformlyOn (fun j t => path (subsequence j) ω t) (limitPath ω)
      atTop (Icc 0 T) := by
  filter_upwards [limitPath_tendsto] with ω hω T
  exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hω _ isCompact_Icc

theorem limitPath_properties : ∀ᵐ ω ∂gaussianProduct,
    limitPath ω 0 = 0 ∧ Monotone (limitPath ω) ∧ ∀ t, 0 ≤ limitPath ω t := by
  filter_upwards [limitPath_tendsto] with ω hω
  have ht (t : ℝ≥0) : Tendsto (fun j => path (subsequence j) ω t) atTop (𝓝 (limitPath ω t)) := by
    have he : Continuous (fun f : C(ℝ≥0, ℝ) => f t) := by fun_prop
    exact he.continuousAt.tendsto.comp hω
  have hz : limitPath ω 0 = 0 := by
    have h := ht 0
    simp only [path_zero] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine ⟨hz, fun s t hst => ?_, fun t => ?_⟩
  · exact le_of_tendsto_of_tendsto' (ht s) (ht t) (fun j => path_monotone _ ω hst)
  · exact ge_of_tendsto' (ht t) (fun j => path_nonneg _ ω t)

end OperatorDerivativeRewrite.Foundation.BrownianMassContinuousLimit
