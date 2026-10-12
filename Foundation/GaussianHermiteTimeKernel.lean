import Foundation.GaussianHermiteTimeIntegral
import Foundation.BochnerL2Fubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The actual Volterra kernel for time-integrated Hermite predictable fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianHermiteTimeKernel
open InfiniteGaussian GaussianTimeSpaceHermite GaussianHermiteStochasticSums
open GaussianHermiteRepresentation GaussianHermiteIntegrand GaussianHermiteTimeIntegral
open GaussianPredictableFull GaussianTimeProductL2 GaussianProductDerivative GaussianBochnerDerivative
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem continuous_interval_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℝ → E) (hf : Continuous f) (T : ℝ≥0) :
    MemLp ((Ioc 0 (T : ℝ)).indicator f) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Ioc]
  exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable.restrict).mpr
    ((hf.norm.pow 2).intervalIntegrable 0 (T : ℝ)).1

def kernel (q : ℝ → ℝ) (n : ℕ) : ℝ × ℝ → GaussianL2 :=
  {z : ℝ × ℝ | 0 < z.2 ∧ z.2 ≤ z.1}.indicator
    (fun z => q z.1 • (brownianCore z.2.toNNReal n : GaussianL2))

theorem kernel_stronglyMeasurable (q : ℝ → ℝ) (hq : Continuous q) (n : ℕ) :
    StronglyMeasurable (kernel q n) := by
  apply ((hq.comp continuous_fst).smul
    ((brownianCore_continuous n).comp (continuous_real_toNNReal.comp continuous_snd))).stronglyMeasurable.indicator
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst)

theorem kernel_slice (q : ℝ → ℝ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    scalarCurry (q t • (hermiteIntegrand n t.toNNReal : TimeProbabilityL2))
      =ᵐ[volume] fun x => kernel q n (t, x) := by
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (q t) (scalarCurry (hermiteIntegrand n t.toNNReal)),
    hermiteIntegrand_slices n t.toNNReal] with x hs hx
  rw [hs]
  change q t • scalarCurry (hermiteIntegrand n t.toNNReal : TimeProbabilityL2) x = _
  rw [hx]
  simp only [horizonValue, Real.coe_toNNReal _ ht]
  by_cases hp : 0 < x ∧ x ≤ t <;> simp [kernel, mem_Ioc, hp]

theorem kernel_bound (q : ℝ → ℝ) (n : ℕ) (T : ℝ≥0) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ t ∈ Icc 0 (T : ℝ), ‖q t‖ ≤ M) :
    ∀ᵐ z ∂(volume.restrict (Ioc 0 (T : ℝ))).prod volume,
      ‖kernel q n z‖ ≤ M * ‖horizonValue n T z.2‖ := by
  have ht := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := (volume : Measure ℝ))).ae
      (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [ht] with z hz
  change z.1 ∈ Ioc 0 (T : ℝ) at hz
  by_cases hk : 0 < z.2 ∧ z.2 ≤ z.1
  · have hx : z.2 ∈ Ioc 0 (T : ℝ) := ⟨hk.1, hk.2.trans hz.2⟩
    have hk' : z ∈ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 ≤ z.1} := hk
    simp only [kernel, indicator_of_mem hk', norm_smul, horizonValue, indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_right (hq z.1 ⟨hz.1.le, hz.2⟩)
      (norm_nonneg (brownianCore z.2.toNNReal n : GaussianL2))
  · have hk' : z ∉ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 ≤ z.1} := hk
    simp only [kernel, indicator_of_notMem hk', norm_zero]
    exact mul_nonneg hM (norm_nonneg (horizonValue n T z.2))

theorem kernel_column (a q : ℝ → ℝ) (hq : Continuous q)
    (ha : ∀ t, HasDerivAt a (q t) t) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    (∫ t in Ioc 0 (T : ℝ), kernel q n (t, x)) =
      (Ioc 0 (T : ℝ)).indicator
        (fun x => (a T - a x) • (brownianCore x.toNNReal n : GaussianL2)) x := by
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · rw [indicator_of_mem hx]
    have he : (fun t => kernel q n (t, x)) =
        (Ici x).indicator (fun t => q t • (brownianCore x.toNNReal n : GaussianL2)) := by
      funext t
      by_cases hxt : x ≤ t <;> simp [kernel, hx.1, hxt]
    rw [he, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hset : Ici x ∩ Ioc 0 (T : ℝ) = Icc x T := by
      ext t
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨hxt, _, ht⟩; exact ⟨hxt, ht⟩
      · rintro ⟨hxt, ht⟩; exact ⟨hxt, hx.1.trans_le hxt, ht⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.2,
      intervalIntegral.integral_smul_const,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => ha t) (hq.intervalIntegrable _ _)]
  · rw [indicator_of_notMem hx]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply indicator_of_notMem
    intro hk
    exact hx ⟨hk.1, hk.2.trans ht.2⟩

def tailField (a : ℝ → ℝ) (ha : Continuous a) (n : ℕ) (T : ℝ≥0) : TimeScalarL2 :=
  (continuous_interval_memLp
    (fun x => (a T - a x) • (brownianCore x.toNNReal n : GaussianL2))
    ((continuous_const.sub ha).smul ((brownianCore_continuous n).comp continuous_real_toNNReal)) T).toLp _

theorem tailField_coeFn (a : ℝ → ℝ) (ha : Continuous a) (n : ℕ) (T : ℝ≥0) :
    tailField a ha n T =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator
      (fun x => (a T - a x) • (brownianCore x.toNNReal n : GaussianL2)) := MemLp.coeFn_toLp _

theorem integratedHermite_slices (a q : ℝ → ℝ) (ha : Continuous a) (hq : Continuous q)
    (haq : ∀ t, HasDerivAt a (q t) t) (n : ℕ) (T : ℝ≥0) :
    scalarCurry (integratedHermite q n T : TimeProbabilityL2) = tailField a ha n T := by
  let L : fullPredictable →L[ℝ] TimeScalarL2 :=
    scalarCurry.toContinuousLinearEquiv.toContinuousLinearMap.comp fullPredictable.subtypeL
  have hL : scalarCurry (integratedHermite q n T : TimeProbabilityL2) =
      ∫ t in 0..(T : ℝ), L (q t • hermiteIntegrand n t.toNNReal) :=
    (L.intervalIntegral_comp_comm (hermite_time_integrable q hq n T)).symm
  rw [hL, intervalIntegral.integral_of_le T.coe_nonneg]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hq.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (q 0)).trans (hM 0 ⟨le_rfl, T.coe_nonneg⟩)
  have hB : MemLp (fun x => M * ‖horizonValue n T x‖) 2 volume :=
    (continuous_interval_memLp (fun x => (brownianCore x.toNNReal n : GaussianL2))
      ((brownianCore_continuous n).comp continuous_real_toNNReal) T).norm.const_mul M
  apply BochnerL2Fubini.integral_eq_of_slices (B := fun x => M * ‖horizonValue n T x‖)
    (g := kernel q n)
  · exact ((L.continuous.comp (hq.smul
      ((hermiteIntegrand_continuous n).comp continuous_real_toNNReal))).intervalIntegrable 0 T).1
  · exact (kernel_stronglyMeasurable q hq n).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact kernel_slice q n t ht.1.le
  · exact hB
  · exact kernel_bound q n T M hM0 hM
  · exact (tailField_coeFn a ha n T).trans (Filter.Eventually.of_forall fun x =>
      (kernel_column a q hq haq n T x).symm)

end OperatorDerivativeRewrite.Foundation.GaussianHermiteTimeKernel
