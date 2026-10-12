import Foundation.GaussianSmoothConditional

/-! Genuine stochastic Fubini for deterministic weights of continuous adapted
Gaussian-L2 curves. Joint kernel domination and column integrals are proved
before identifying the Bochner integral in the predictable Hilbert space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianContinuousStochasticFubini
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianBochnerDerivative GaussianContinuousIntegrands GaussianPredictableFull
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

variable (v : ℝ≥0 → GaussianL2) (hv : Continuous v)

def kernel (q : ℝ → ℝ) : ℝ × ℝ → GaussianL2 :=
  {z : ℝ × ℝ | 0 < z.2 ∧ z.2 ≤ z.1}.indicator
    (fun z => q z.1 • v z.2.toNNReal)

include hv in
theorem kernel_stronglyMeasurable (q : ℝ → ℝ) (hq : Continuous q) :
    StronglyMeasurable (kernel v q) := by
  apply ((hq.comp continuous_fst).smul
    (hv.comp (continuous_real_toNNReal.comp continuous_snd))).stronglyMeasurable.indicator
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst)

theorem kernel_bound (q : ℝ → ℝ) (T : ℝ≥0) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ t ∈ Icc 0 (T : ℝ), ‖q t‖ ≤ M) :
    ∀ᵐ z ∂(volume.restrict (Ioc 0 (T : ℝ))).prod volume,
      ‖kernel v q z‖ ≤ M * ‖horizonValue v T z.2‖ := by
  have ht := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := (volume : Measure ℝ))).ae
      (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [ht] with z hz
  change z.1 ∈ Ioc 0 (T : ℝ) at hz
  by_cases hk : 0 < z.2 ∧ z.2 ≤ z.1
  · have hx : z.2 ∈ Ioc 0 (T : ℝ) := ⟨hk.1, hk.2.trans hz.2⟩
    have hk' : z ∈ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 ≤ z.1} := hk
    simp only [kernel, indicator_of_mem hk', norm_smul, horizonValue, indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_right (hq z.1 ⟨hz.1.le, hz.2⟩) (norm_nonneg _)
  · have hk' : z ∉ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 ≤ z.1} := hk
    simp only [kernel, indicator_of_notMem hk', norm_zero]
    exact mul_nonneg hM (norm_nonneg _)

theorem kernel_column (a q : ℝ → ℝ) (hq : Continuous q)
    (ha : ∀ t, HasDerivAt a (q t) t) (T : ℝ≥0) (x : ℝ) :
    (∫ t in Ioc 0 (T : ℝ), kernel v q (t, x)) =
      (Ioc 0 (T : ℝ)).indicator (fun x => (a T - a x) • v x.toNNReal) x := by
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · rw [indicator_of_mem hx]
    have he : (fun t => kernel v q (t, x)) =
        (Ici x).indicator (fun t => q t • v x.toNNReal) := by
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
    exact indicator_of_notMem (fun hk => hx ⟨hk.1, hk.2.trans ht.2⟩) _

def tailField (a : ℝ → ℝ) (ha : Continuous a) (T : ℝ≥0) : TimeScalarL2 :=
  (GaussianHermiteTimeKernel.continuous_interval_memLp
    (fun x => (a T - a x) • v x.toNNReal)
    ((continuous_const.sub ha).smul (hv.comp continuous_real_toNNReal)) T).toLp _

theorem tailField_coeFn (a : ℝ → ℝ) (ha : Continuous a) (T : ℝ≥0) :
    tailField v hv a ha T =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun x => (a T - a x) • v x.toNNReal) := MemLp.coeFn_toLp _

variable (U : ℝ≥0 → fullPredictable) (hU : Continuous U)
  (hslice : ∀ t, scalarCurry (U t : TimeProbabilityL2) =ᵐ[volume] horizonValue v t)

include hslice in
theorem kernel_slice (q : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    scalarCurry (q t • (U t.toNNReal : TimeProbabilityL2)) =ᵐ[volume]
      fun x => kernel v q (t, x) := by
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (q t) (scalarCurry (U t.toNNReal)), hslice t.toNNReal]
    with x hs hx
  rw [hs]
  change q t • scalarCurry (U t.toNNReal : TimeProbabilityL2) x = _
  rw [hx]
  simp only [horizonValue, Real.coe_toNNReal _ ht]
  by_cases hp : 0 < x ∧ x ≤ t <;> simp [kernel, mem_Ioc, hp]

include hU hslice in
/-- The column formula is first proved by ordinary FTC; Fubini then identifies
it with the Bochner-L2 integral using a genuine square-integrable majorant. -/
theorem integrated_slices (a q : ℝ → ℝ) (ha : Continuous a) (hq : Continuous q)
    (haq : ∀ t, HasDerivAt a (q t) t) (T : ℝ≥0) :
    scalarCurry ((∫ t in 0..(T : ℝ), q t • U t.toNNReal : fullPredictable) : TimeProbabilityL2) =
      tailField v hv a ha T := by
  let L : fullPredictable →L[ℝ] TimeScalarL2 :=
    scalarCurry.toContinuousLinearEquiv.toContinuousLinearMap.comp fullPredictable.subtypeL
  have hL : scalarCurry ((∫ t in 0..(T : ℝ), q t • U t.toNNReal : fullPredictable) : TimeProbabilityL2) =
      ∫ t in 0..(T : ℝ), L (q t • U t.toNNReal) :=
    (L.intervalIntegral_comp_comm
      ((hq.smul (hU.comp continuous_real_toNNReal)).intervalIntegrable 0 T)).symm
  rw [hL, intervalIntegral.integral_of_le T.coe_nonneg]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hq.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (q 0)).trans (hM 0 ⟨le_rfl, T.coe_nonneg⟩)
  apply BochnerL2Fubini.integral_eq_of_slices
    (B := fun x => M * ‖horizonValue v T x‖) (g := kernel v q)
  · exact ((L.continuous.comp (hq.smul (hU.comp continuous_real_toNNReal))).intervalIntegrable 0 T).1
  · exact (kernel_stronglyMeasurable v hv q hq).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact kernel_slice v U hslice q t ht.1.le
  · exact (horizonValue_memLp v hv T).norm.const_mul M
  · exact kernel_bound v q T M hM0 hM
  · exact (tailField_coeFn v hv a ha T).trans (Filter.Eventually.of_forall fun x =>
      (kernel_column v a q hq haq T x).symm)

include hv hU hslice in
/-- Exact field identity for deterministic C1 weighting. The right side is
identified by running time slices, not by a prescribed stochastic value. -/
theorem weighted_slices (a q : ℝ → ℝ) (ha : Continuous a) (hq : Continuous q)
    (haq : ∀ t, HasDerivAt a (q t) t) (T : ℝ≥0) :
    scalarCurry ((a T • U T - ∫ t in 0..(T : ℝ), q t • U t.toNNReal : fullPredictable) : TimeProbabilityL2)
      =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator (fun x => a x • v x.toNNReal) := by
  change scalarCurry (a T • (U T : TimeProbabilityL2) -
    ((∫ t in 0..(T : ℝ), q t • U t.toNNReal : fullPredictable) : TimeProbabilityL2)) =ᵐ[volume] _
  rw [map_sub, map_smul, integrated_slices v hv U hU hslice a q ha hq haq T]
  filter_upwards [Lp.coeFn_sub (a T • scalarCurry (U T)) (tailField v hv a ha T),
    Lp.coeFn_smul (a T) (scalarCurry (U T)), hslice T, tailField_coeFn v hv a ha T]
      with x hs hm hu ht
  rw [hs]
  simp only [Pi.sub_apply, hm, Pi.smul_apply, hu, ht, horizonValue]
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · simp only [indicator_of_mem hx]
    module
  · simp [hx]

include hU in
/-- Justified bounded-linear-map Fubini for the existing J; continuity of U
and q supplies the actual Bochner integrability on each finite horizon. -/
theorem integral_weighted_field (a q : ℝ → ℝ) (hq : Continuous q) (T : ℝ≥0) :
    itoIntegral (a T • U T - ∫ t in 0..(T : ℝ), q t • U t.toNNReal) =
      a T • itoIntegral (U T) - ∫ t in 0..(T : ℝ), q t • itoIntegral (U t.toNNReal) := by
  rw [map_sub, map_smul]
  congr 1
  change itoIntegral.toContinuousLinearMap (∫ t in 0..(T : ℝ), q t • U t.toNNReal) = _
  have hi : IntervalIntegrable (fun t : ℝ => q t • U t.toNNReal) volume 0 T :=
    (hq.smul (hU.comp continuous_real_toNNReal)).intervalIntegrable 0 T
  rw [← itoIntegral.toContinuousLinearMap.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro t _
  exact map_smul itoIntegral (q t) (U t.toNNReal)

end OperatorDerivativeRewrite.Foundation.GaussianContinuousStochasticFubini


