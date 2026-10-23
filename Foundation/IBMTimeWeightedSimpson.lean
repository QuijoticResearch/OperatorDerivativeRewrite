import Foundation.IBMUniformSimpsonProcess
import Foundation.IBMTimeWeightQuadrature

/-! Genuine time-weighted signed Simpson sums for actual reflected-clock IBM.
The time correction is a pathwise Lebesgue integral, not a formal drift. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMTimeWeightedSimpson
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMContinuousQuadrature IBMUniformSimpsonProcess IBMActualSimpson
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

def timeValue (g : ℝ → ℝ) (t : ℝ) (ω : JointSample) : ℝ :=
  lineIntegral g (Real.toNNReal t) ω

def weighted (h g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), h (time T (n + 1) i) * IBMSimpsonPeano.simpson g
    (ibmValue (grid (T / (n + 1)) i) ω) (ibmValue (grid (T / (n + 1)) (i + 1)) ω)

def pathSum (h g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), h (time T (n + 1) i) *
    (lineIntegral g (grid (T / (n + 1)) (i + 1)) ω -
      lineIntegral g (grid (T / (n + 1)) i) ω)

def weightedError (h g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  weighted h g T n ω - pathSum h g T n ω

def correction (h g : ℝ → ℝ) (T : ℝ≥0) (ω : JointSample) : ℝ :=
  ∫ t in (0 : ℝ)..(T : ℝ), deriv h t * timeValue g t ω

def target (h g : ℝ → ℝ) (T : ℝ≥0) (ω : JointSample) : ℝ :=
  h T * lineIntegral g T ω - correction h g T ω

theorem timeValue_continuous (g : ℝ → ℝ) (hg : Continuous g) (ω : JointSample) :
    Continuous (fun t => timeValue g t ω) :=
  (integral_continuous g hg ω).comp continuous_real_toNNReal

theorem timeValue_measurable (g : ℝ → ℝ) (hg : Continuous g) :
    Measurable (fun p : ℝ × JointSample => timeValue g p.1 p.2) :=
  (integral_jointly_measurable g hg).comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)

theorem weighted_measurable (h g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) (n : ℕ) :
    Measurable (weighted h g T n) := by
  have hc : Continuous (fun p : ℝ × ℝ => IBMSimpsonPeano.simpson g p.1 p.2) := by
    unfold IBMSimpsonPeano.simpson
    fun_prop
  have hm (r : ℝ≥0) : Measurable (ibmValue r) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  unfold weighted
  apply Finset.measurable_sum
  intro i hi
  exact (hc.measurable.comp
    ((hm (grid (T / (n + 1)) i)).prodMk (hm (grid (T / (n + 1)) (i + 1))))).const_mul _

theorem pathSum_measurable (h g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) (n : ℕ) :
    Measurable (pathSum h g T n) := by
  apply Finset.measurable_sum
  intro i hi
  exact ((lineIntegral_measurable g hg _).sub (lineIntegral_measurable g hg _)).const_mul _

theorem correction_integrable (h g : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (hg : Continuous g)
    (T : ℝ≥0) (ω : JointSample) :
    IntervalIntegrable (fun t => deriv h t * timeValue g t ω) volume 0 T :=
  ((hh.continuous_deriv (by norm_num)).mul (timeValue_continuous g hg ω)).intervalIntegrable _ _

theorem correction_measurable (h g : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (hg : Continuous g)
    (T : ℝ≥0) : Measurable (correction h g T) := by
  have hm := (((hh.continuous_deriv (by norm_num)).measurable.comp measurable_fst).mul
    (timeValue_measurable g hg)).stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict (Ioc (0 : ℝ) T))
  have he : correction h g T = fun ω =>
      ∫ t, deriv h t * timeValue g t ω ∂volume.restrict (Ioc (0 : ℝ) T) := by
    funext ω
    exact intervalIntegral.integral_of_le T.coe_nonneg
  rw [he]
  exact hm.measurable

theorem target_measurable (h g : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (hg : Continuous g)
    (T : ℝ≥0) : Measurable (target h g T) :=
  ((lineIntegral_measurable g hg T).const_mul _).sub (correction_measurable h g hh hg T)

theorem cumulative_cell_error (g : ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (ω : JointSample) :
    (∑ i ∈ Finset.range m, (IBMSimpsonPeano.simpson g
      (ibmValue (grid (T / (n + 1)) i) ω) (ibmValue (grid (T / (n + 1)) (i + 1)) ω) -
      (lineIntegral g (grid (T / (n + 1)) (i + 1)) ω -
        lineIntegral g (grid (T / (n + 1)) i) ω))) =
      IBMUniformSimpsonProcess.error g T n m ω := by
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub
    (fun i => lineIntegral g (grid (T / (n + 1)) i) ω)]
  simp only [grid, Nat.cast_zero, mul_zero, lineIntegral, intervalIntegral.integral_same,
    sub_zero, IBMUniformSimpsonProcess.error, prefixSums]

theorem weighted_error_bound (h g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample)
    {B K : ℝ} (hK : 0 ≤ K) (hB : ∀ t ∈ Icc 0 (T : ℝ), |h t| ≤ B)
    (hLip : ∀ x ∈ Icc 0 (T : ℝ), ∀ y ∈ Icc 0 (T : ℝ), |h y - h x| ≤ K * |y - x|) :
    |weightedError h g T n ω| ≤ maximum g T n ω * (B + K * T) := by
  have he := weighted_prefix_bound (fun i => h (time T (n + 1) i))
    (fun i => IBMSimpsonPeano.simpson g
      (ibmValue (grid (T / (n + 1)) i) ω) (ibmValue (grid (T / (n + 1)) (i + 1)) ω) -
      (lineIntegral g (grid (T / (n + 1)) (i + 1)) ω -
        lineIntegral g (grid (T / (n + 1)) i) ω))
    (n + 1) (by omega) (maximum g T n ω) B (K * T) (maximum_nonneg g T n ω)
    (fun i hi => hB _ (time_mem T.coe_nonneg (by omega) (by omega)))
    (by intro m hm; rw [cumulative_cell_error]; exact error_le_maximum g T n m hm ω)
    (variation_bound T.coe_nonneg hK h (n + 1) (by omega) hLip)
  simpa only [weightedError, weighted, pathSum, mul_sub, Finset.sum_sub_distrib] using he

theorem weighted_error_tendstoInMeasure (h g : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hg : ContDiff ℝ 3 g) {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (weightedError h g T) atTop (fun _ => (0 : ℝ)) := by
  obtain ⟨B, K, hB0, hK, hB, hd, hLip⟩ :=
    IBMTimeWeightQuadrature.compact_weight_bounds h hh T.coe_nonneg
  let C : ℝ := B + K * T
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply quartic_peano_tendstoInMeasure hT _
    (fun n => (weighted_measurable h g hg.continuous T n).sub
      (pathSum_measurable h g hg.continuous T n))
  intro ω ε hε
  have heta : 0 < ε / (C + 1) := by positivity
  filter_upwards [maximum_eventual_bound g hg T ω heta] with n hn
  have hcoef : ε / (C + 1) * C ≤ ε := by
    calc
      _ ≤ ε / (C + 1) * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) heta.le
      _ = ε := div_mul_cancel₀ _ (by positivity)
  have hq : 0 ≤ IBMUniformQuarticFamily.quartic T (n + 1) ω :=
    Finset.sum_nonneg fun _ _ => by positivity
  calc
    |weightedError h g T n ω| ≤ maximum g T n ω * C := weighted_error_bound h g T n ω hK hB hLip
    _ ≤ (ε / (C + 1) * IBMUniformQuarticFamily.quartic T (n + 1) ω) * C :=
      mul_le_mul_of_nonneg_right hn hC
    _ = (ε / (C + 1) * C) * IBMUniformQuarticFamily.quartic T (n + 1) ω := by ring
    _ ≤ ε * IBMUniformQuarticFamily.quartic T (n + 1) ω := mul_le_mul_of_nonneg_right hcoef hq

theorem pathSum_tendsto (h g : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (hg : Continuous g)
    (T : ℝ≥0) (ω : JointSample) :
    Tendsto (fun n => pathSum h g T n ω) atTop (𝓝 (target h g T ω)) := by
  have he (N i : ℕ) : timeValue g (time T N i) ω = lineIntegral g (grid (T / N) i) ω := by
    unfold timeValue
    rw [IBMContinuousWeightedQuartic.real_time_eq_grid, Real.toNNReal_coe]
  have hz : timeValue g 0 ω = 0 := by simp [timeValue, lineIntegral]
  have ht : timeValue g T ω = lineIntegral g T ω := by simp [timeValue]
  have hr := IBMTimeWeightQuadrature.increment_sum_tendsto h (fun t => timeValue g t ω)
    hh (timeValue_continuous g hg ω) T.coe_nonneg
  simpa only [he, hz, ht, mul_zero, sub_zero, pathSum, target, correction,
    Nat.cast_add, Nat.cast_one] using hr

/-- Actual time-dependent signed quadrature: the correction is a genuine
Lebesgue time integral against the continuous spatial integral process. -/
theorem weighted_tendstoInMeasure (h g : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hg : ContDiff ℝ 3 g) {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (weighted h g T) atTop (target h g T) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (weighted_measurable h g hg.continuous T n).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, he⟩ := ((weighted_error_tendstoInMeasure h g hh hg hT).comp
    hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [he] with ω hω
  have hp := (pathSum_tendsto h g hh hg.continuous T ω).comp (hns.comp hms).tendsto_atTop
  have ht := hω.add hp
  simpa only [Function.comp_def, weightedError, sub_add_cancel, zero_add] using ht

theorem derivative_lineIntegral (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (r : ℝ≥0)
    (ω : JointSample) : lineIntegral (deriv f) r ω = f (ibmValue r ω) - f (ibmValue 0 ω) :=
  intervalIntegral.integral_deriv_eq_sub (fun z hz => (hf.differentiable (by norm_num)) z)
    ((hf.continuous_deriv (by norm_num)).intervalIntegrable _ _)

theorem derivative_target_identity (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 4 f) (T : ℝ≥0) (ω : JointSample) :
    target h (deriv f) T ω = h T * f (ibmValue T ω) - h 0 * f (ibmValue 0 ω) -
      ∫ t in (0 : ℝ)..(T : ℝ), deriv h t * f (ibmValue (Real.toNNReal t) ω) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hder := hh.continuous_deriv (by norm_num)
  have hval : Continuous (fun t => f (ibmValue (Real.toNNReal t) ω)) :=
    hf.continuous.comp ((ibmValue_continuous ω).comp continuous_real_toNNReal)
  have hftc := intervalIntegral.integral_deriv_eq_sub
    (fun t ht => (hh.differentiable (by norm_num)) t) (hder.intervalIntegrable (0 : ℝ) T)
  have hc : correction h (deriv f) T ω =
      (∫ t in (0 : ℝ)..(T : ℝ), deriv h t * f (ibmValue (Real.toNNReal t) ω)) -
        (h T - h 0) * f (ibmValue 0 ω) := by
    unfold correction timeValue
    simp_rw [derivative_lineIntegral f hf1, mul_sub]
    have hi1 : IntervalIntegrable (fun t => deriv h t * f (ibmValue (Real.toNNReal t) ω))
        volume (0 : ℝ) T := (hder.mul hval).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t => deriv h t * f (ibmValue 0 ω))
        volume (0 : ℝ) T := (hder.mul_const _).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_mul_const, hftc]
  unfold target
  rw [derivative_lineIntegral f hf1, hc]
  ring

/-- A genuine separable time-space chain formula for h(t)f(Z_t), with C1
time weight and C4 spatial primitive, in original-law probability. -/
theorem derivative_weighted_tendstoInMeasure (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hf : ContDiff ℝ 4 f) {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (weighted h (deriv f) T) atTop
      (fun ω => h T * f (ibmValue T ω) - h 0 * f (ibmValue 0 ω) -
        ∫ t in (0 : ℝ)..(T : ℝ), deriv h t * f (ibmValue (Real.toNNReal t) ω)) :=
  (weighted_tendstoInMeasure h (deriv f) hh hf.deriv' hT).congr
    (fun _ => ae_of_all _ fun _ => rfl)
    (ae_of_all _ (derivative_target_identity h f hh hf T))

end OperatorDerivativeRewrite.Foundation.IBMTimeWeightedSimpson
