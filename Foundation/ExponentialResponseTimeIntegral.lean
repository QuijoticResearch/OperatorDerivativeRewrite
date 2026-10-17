import Foundation.SPDEExponentialTimeContinuity
import Foundation.BochnerL2Fubini

/-! Actual Bochner time integration of exponential convolution profiles. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ExponentialResponseTimeIntegral
set_option backward.isDefEq.respectTransparency false
open GaussianTimeHilbert SPDEExponentialForcing SPDEExponentialTimeContinuity

def triangle (rate : ℝ≥0) (z : ℝ × ℝ) : ℝ :=
  {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}.indicator
    (fun p => Real.exp (-(rate : ℝ)*(p.1-p.2))) z

theorem triangle_measurable (rate : ℝ≥0) : StronglyMeasurable (triangle rate) := by
  apply (by fun_prop : StronglyMeasurable (fun p : ℝ × ℝ => Real.exp (-(rate : ℝ)*(p.1-p.2)))).indicator
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst)

theorem triangle_bound (rate T : ℝ≥0) (t u : ℝ) (ht : t ∈ Ioc 0 (T : ℝ)) :
    ‖triangle rate (t,u)‖ ≤ (Ioc 0 (T : ℝ)).indicator (fun _ => (1 : ℝ)) u := by
  by_cases hu : 0 < u ∧ u ≤ t
  · have hT : u ∈ Ioc 0 (T : ℝ) := ⟨hu.1, hu.2.trans ht.2⟩
    have htri : (t,u) ∈ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} := hu
    simp only [triangle, indicator_of_mem htri, indicator_of_mem hT,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr rate.coe_nonneg) (sub_nonneg.mpr hu.2))
  · have htri : (t,u) ∉ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} := hu
    simp only [triangle, indicator_of_notMem htri, norm_zero]
    by_cases hT : u ∈ Ioc 0 (T : ℝ) <;> simp [hT]

theorem scalar_primitive (rate : ℝ≥0) (hr : 0 < rate) (u t : ℝ) :
    HasDerivAt (fun t => -Real.exp (-(rate : ℝ)*(t-u))/(rate : ℝ))
      (Real.exp (-(rate : ℝ)*(t-u))) t := by
  have h := ((((hasDerivAt_id' t).sub_const u).const_mul (-(rate : ℝ))).exp.neg).div_const (rate : ℝ)
  convert h using 1 <;> first | rfl |
    (field_simp [(show (rate : ℝ) ≠ 0 from ne_of_gt hr)] <;> ring)

theorem column_exact (rate T : ℝ≥0) (hr : 0 < rate) (u : ℝ) :
    (∫ t in Ioc 0 (T : ℝ), triangle rate (t,u)) = (rate : ℝ)⁻¹*
      ((Ioc 0 (T : ℝ)).indicator (fun _ => (1 : ℝ)) u-response rate T u) := by
  by_cases hu : u ∈ Ioc 0 (T : ℝ)
  · have he : (fun t => triangle rate (t,u)) =
        (Ici u).indicator (fun t => Real.exp (-(rate : ℝ)*(t-u))) := by
      funext t
      by_cases hut : u ≤ t <;> simp [triangle, hu.1, hut]
    rw [he, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hset : Ici u ∩ Ioc 0 (T : ℝ) = Icc u T := by
      ext t
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨hut, _, ht⟩; exact ⟨hut, ht⟩
      · rintro ⟨hut, ht⟩; exact ⟨hut, hu.1.trans_le hut, ht⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu.2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => scalar_primitive rate hr u t)
        ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-(rate : ℝ)*(t-u)))).intervalIntegrable _ _)]
    simp only [sub_self, mul_zero, Real.exp_zero, response, indicator_of_mem hu]
    ring
  · have hz : (∫ t in Ioc 0 (T : ℝ), triangle rate (t,u)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      apply indicator_of_notMem
      exact fun h => hu ⟨h.1, h.2.trans ht.2⟩
    rw [hz]
    simp [response, hu]

def integratedProfile (rate T : ℝ≥0) : TimeHilbert :=
  (rate : ℝ)⁻¹ • (timeVector T-responseVector rate T)

theorem integratedProfile_coeFn (rate T : ℝ≥0) : integratedProfile rate T =ᵐ[volume]
    fun u => (rate : ℝ)⁻¹*((Ioc 0 (T : ℝ)).indicator (fun _ => (1 : ℝ)) u-response rate T u) := by
  filter_upwards [Lp.coeFn_smul (rate : ℝ)⁻¹ (timeVector T-responseVector rate T),
    Lp.coeFn_sub (timeVector T) (responseVector rate T), timeVector_coeFn T,
    responseVector_coeFn rate T] with u hsm hsub ht hr
  change (integratedProfile rate T : ℝ → ℝ) u = _
  change ((rate : ℝ)⁻¹ • (timeVector T-responseVector rate T) : TimeHilbert) u = _
  rw [hsm]
  change (rate : ℝ)⁻¹*(timeVector T-responseVector rate T) u = _
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [ht, hr]

theorem profile_intervalIntegrable (rate T : ℝ≥0) (hr : 0 < rate) :
    IntervalIntegrable (fun t : ℝ => responseVector rate t.toNNReal) volume 0 T :=
  ((responseVector_continuous rate hr).comp continuous_real_toNNReal).intervalIntegrable _ _

theorem integral_responseVector (rate T : ℝ≥0) (hr : 0 < rate) :
    (∫ t in 0..(T : ℝ), responseVector rate t.toNNReal) = integratedProfile rate T := by
  rw [intervalIntegral.integral_of_le T.coe_nonneg]
  apply BochnerL2Fubini.integral_eq_of_slices
    (g := triangle rate) (B := (Ioc 0 (T : ℝ)).indicator (fun _ => (1 : ℝ)))
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp
      (profile_intervalIntegrable rate T hr)
  · exact (triangle_measurable rate).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := responseVector_coeFn rate t.toNNReal
    have he : response rate t.toNNReal = fun u => triangle rate (t,u) := by
      funext u
      simp [response, triangle, Real.coe_toNNReal _ ht.1.le, Set.indicator_apply]
    rwa [he] at h
  · exact interval_indicator_memLp 0 T
  · have ht := (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := (volume : Measure ℝ))).ae
      (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [ht] with z hz
    exact triangle_bound rate T z.1 z.2 hz
  · exact (integratedProfile_coeFn rate T).trans
      (Eventually.of_forall fun u => (column_exact rate T hr u).symm)

end OperatorDerivativeRewrite.Foundation.ExponentialResponseTimeIntegral
