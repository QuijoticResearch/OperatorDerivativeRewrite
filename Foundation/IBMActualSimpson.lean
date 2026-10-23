import Foundation.IBMSimpsonPeano
import Foundation.IBMActualPeanoRemainder

/-! Actual signed spatial Simpson integration for C3 one-forms along IBM.
The finite sums use the real process and converge in its original joint law.
No adapted, time-dependent or arbitrary random integrand is asserted. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMActualSimpson
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMUniformQuarticFamily IBMUniformQuarticVariation IBMUniformFifthRemainder
open IBMSimpsonPeano
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

def sums (g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), simpson g (ibmValue (grid (T / (n + 1)) i) ω)
    (ibmValue (grid (T / (n + 1)) (i + 1)) ω)

def error (f : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  sums (deriv f) T n ω - (f (ibmValue T ω) - f (ibmValue 0 ω))

theorem sums_add (g h : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    sums (fun z => g z + h z) T n ω = sums g T n ω + sums h T n ω := by
  unfold sums simpson
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem sums_measurable (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) (n : ℕ) :
    Measurable (sums g T n) := by
  have hc : Continuous (fun p : ℝ × ℝ => simpson g p.1 p.2) := by
    unfold simpson
    fun_prop
  have hm (r : ℝ≥0) : Measurable (ibmValue r) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  unfold sums
  apply Finset.measurable_sum
  intro i hi
  exact hc.measurable.comp
    ((hm (grid (T / (n + 1)) i)).prodMk (hm (grid (T / (n + 1)) (i + 1))))

theorem error_measurable (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (T : ℝ≥0) (n : ℕ) :
    Measurable (error f T n) := by
  have hm (r : ℝ≥0) : Measurable (ibmValue r) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  exact (sums_measurable _ (hf.continuous_deriv (by norm_num)) T n).sub
    ((hf.continuous.measurable.comp (hm T)).sub (hf.continuous.measurable.comp (hm 0)))

theorem finite_error_identity (f : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    error f T n ω = ∑ i ∈ Finset.range (n + 1),
      (simpson (deriv f) (ibmValue (grid (T / (n + 1)) i) ω)
        (ibmValue (grid (T / (n + 1)) (i + 1)) ω) -
        (f (ibmValue (grid (T / (n + 1)) (i + 1)) ω) -
          f (ibmValue (grid (T / (n + 1)) i) ω))) := by
  have ht := Finset.sum_range_sub
    (fun i => f (ibmValue (grid (T / (n + 1)) i) ω)) (n + 1)
  have hend : grid (T / (n + 1)) (n + 1) = T := by
    unfold grid
    push_cast
    exact div_mul_cancel₀ T (by positivity)
  rw [hend] at ht
  have hz : grid (T / (n + 1)) 0 = 0 := by simp [grid]
  rw [hz] at ht
  unfold error sums
  rw [← ht, ← Finset.sum_sub_distrib]

theorem error_eventual_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (T : ℝ≥0)
    (ω : JointSample) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |error f T n ω| ≤ ε * quartic T (n + 1) ω := by
  let R := IBMContinuousBlockWeights.pathBound id continuous_id T ω
  obtain ⟨δ, hδ, hu⟩ := compact_error_bound f hf R ε hε
  filter_upwards [(mesh_tendsto T ω).eventually (gt_mem_nhds hδ)] with n hn
  rw [finite_error_identity]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [quartic, IBMUniformQuarticFamily.segment, Nat.cast_add, Nat.cast_one]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hb (j : ℕ) (hj : j ≤ n + 1) : |ibmValue (grid (T / (n + 1)) j) ω| ≤ R :=
    IBMContinuousBlockWeights.pathBound_bound id continuous_id T ω _
      (IBMActualPeanoRemainder.grid_le T n j hj)
  have hd : |ibmValue (grid (T / (n + 1)) (i + 1)) ω -
      ibmValue (grid (T / (n + 1)) i) ω| ≤ mesh T n ω :=
    Finset.le_sup' (fun k => |ibmValue (grid (T / (n + 1)) (k + 1)) ω -
      ibmValue (grid (T / (n + 1)) k) ω|) hi
  have h := hu (ibmValue (grid (T / (n + 1)) i) ω)
    (ibmValue (grid (T / (n + 1)) (i + 1)) ω)
    (hb i (by have := Finset.mem_range.mp hi; omega))
    (hb (i + 1) (by have := Finset.mem_range.mp hi; omega)) (hd.trans_lt hn)
  simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using h

/-- A vanishing samplewise Peano factor times actual quartic variation gives
probability decay. No envelope moments or measurable modulus are needed. -/
theorem quartic_peano_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T)
    (E : ℕ → JointSample → ℝ) (hE : ∀ n, Measurable (E n))
    (hbound : ∀ ω, ∀ ε > 0, ∀ᶠ n in atTop, |E n ω| ≤ ε * quartic T (n + 1) ω) :
    TendstoInMeasure jointMeasure E atTop (fun _ => (0 : ℝ)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (hE n).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, hq⟩ :=
    ((quartic_tendstoInMeasure hT).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hq] with ω hω
  have hQ : Tendsto (fun i => quartic T (ns (ms i) + 1) ω) atTop (𝓝 (3 * (T : ℝ))) := by
    simpa only [Function.comp_def] using hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B : ℝ := 3 * (T : ℝ) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have he : 0 < ε / (2 * B) := by positivity
  have hb := (hns.comp hms).tendsto_atTop.eventually (hbound ω _ he)
  filter_upwards [hb, hQ.eventually (gt_mem_nhds (by dsimp [B]; linarith :
    3 * (T : ℝ) < B))] with i hi hqi
  simp only [Function.comp_def] at hi
  rw [Real.dist_eq, sub_zero]
  have hm := mul_le_mul_of_nonneg_left hqi.le he.le
  have hr : (ε / (2 * B)) * B = ε / 2 := by field_simp
  linarith

theorem derivative_sums_tendstoInMeasure (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (sums (deriv f) T) atTop
      (fun ω => f (ibmValue T ω) - f (ibmValue 0 ω)) := by
  have he := tendstoInMeasure_iff_measureReal_norm.mp
    (quartic_peano_tendstoInMeasure hT (error f T) (error_measurable f hf T)
      (fun ω ε hε => error_eventual_bound f hf T ω hε))
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  simpa only [error, sub_zero] using he ε hε

def primitive (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ z in (0 : ℝ)..x, g z

theorem primitive_deriv (g : ℝ → ℝ) (hg : Continuous g) : deriv (primitive g) = g := by
  funext x
  exact intervalIntegral.deriv_integral_right (hg.intervalIntegrable 0 x)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem primitive_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) :
    ContDiff ℝ 4 (primitive g) := by
  apply (contDiff_succ_iff_deriv (n := 3)).mpr
  refine ⟨intervalIntegral.differentiable_integral_of_continuous hg.continuous, ?_, ?_⟩
  · norm_num
  · rw [primitive_deriv g hg.continuous]
    exact hg

def lineIntegral (g : ℝ → ℝ) (T : ℝ≥0) (ω : JointSample) : ℝ :=
  ∫ z in ibmValue 0 ω..ibmValue T ω, g z

theorem lineIntegral_eq_primitive (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0)
    (ω : JointSample) : lineIntegral g T ω =
      primitive g (ibmValue T ω) - primitive g (ibmValue 0 ω) := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable 0 (ibmValue 0 ω))
    (hg.intervalIntegrable (ibmValue 0 ω) (ibmValue T ω))
  unfold primitive lineIntegral
  linarith

theorem lineIntegral_measurable (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    Measurable (lineIntegral g T) := by
  have hc : Continuous (primitive g) :=
    (intervalIntegral.differentiable_integral_of_continuous hg).continuous
  have hm (r : ℝ≥0) : Measurable (ibmValue r) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  have he : lineIntegral g T = fun ω =>
      primitive g (ibmValue T ω) - primitive g (ibmValue 0 ω) :=
    funext (lineIntegral_eq_primitive g hg T)
  rw [he]
  exact (hc.measurable.comp (hm T)).sub (hc.measurable.comp (hm 0))

/-- Genuine signed spatial Simpson sums of ANY global C3 one-form converge
to its oriented endpoint integral, under the original actual IBM law. -/
theorem sums_tendstoInMeasure (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g)
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (sums g T) atTop (lineIntegral g T) := by
  have h := derivative_sums_tendstoInMeasure (primitive g) (primitive_contDiff g hg) hT
  rw [primitive_deriv g hg.continuous] at h
  exact h.congr (fun _ => ae_of_all _ fun _ => rfl)
    (ae_of_all _ fun ω => (lineIntegral_eq_primitive g hg.continuous T ω).symm)

/-- Integration by parts for the actual smooth spatial Simpson sums. Both
terms are separately constructed finite signed sums, not endpoint definitions. -/
theorem integration_by_parts_tendstoInMeasure (f g : ℝ → ℝ)
    (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g) {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure
      (fun n ω => sums (fun z => f z * deriv g z) T n ω +
        sums (fun z => g z * deriv f z) T n ω) atTop
      (fun ω => f (ibmValue T ω) * g (ibmValue T ω) -
        f (ibmValue 0 ω) * g (ibmValue 0 ω)) := by
  have he : deriv (fun z => f z * g z) = fun z =>
      f z * deriv g z + g z * deriv f z := by
    funext z
    rw [deriv_fun_mul ((hf.differentiable (by norm_num)) z)
      ((hg.differentiable (by norm_num)) z)]
    ring
  have h := derivative_sums_tendstoInMeasure (fun z => f z * g z) (hf.mul hg) hT
  rw [he] at h
  exact h.congr (fun n => ae_of_all _ fun ω => sums_add _ _ T n ω)
    (ae_of_all _ fun _ => rfl)

end OperatorDerivativeRewrite.Foundation.IBMActualSimpson
