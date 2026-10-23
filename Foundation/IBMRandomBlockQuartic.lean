import Foundation.IBMUniformPrefixMaximum

/-! Actual quartic sums with measurable random block coefficients. Their
physical-time comparison is the genuine Lebesgue integral of a step weight.
This does not yet pass to arbitrary continuous random weights. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMRandomBlockQuartic
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMUniformPrefixMaximum
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue
  IBMUniformPrefixQuartic.error

/-- A pointwise finite envelope suffices; no measurability or moment condition
is required on the envelope. The observable itself must be measurable. -/
theorem dominated_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T)
    (E : ℕ → JointSample → ℝ) (C : JointSample → ℝ)
    (hE : ∀ n, Measurable (E n))
    (hbound : ∀ n ω, |E n ω| ≤ C ω * maximum T n ω) :
    TendstoInMeasure jointMeasure E atTop (fun _ => (0 : ℝ)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (hE n).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, hmax⟩ :=
    ((maximum_tendstoInMeasure hT).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hmax] with ω hω
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun i => hbound (ns (ms i)) ω)
  simpa only [Function.comp_def, mul_zero] using hω.const_mul (C ω)

variable {ι : Type*}

def blockError (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ j ∈ I, a n j ω * (IBMUniformPrefixQuartic.error T n (u n j ω) ω -
    IBMUniformPrefixQuartic.error T n (l n j ω) ω)

def weightedQuartic (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ j ∈ I, a n j ω * (cumulative T n (u n j ω) ω - cumulative T n (l n j ω) ω)

def timeIntegral (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ j ∈ I, a n j ω * ((T : ℝ)/(n + 1) * ((u n j ω : ℝ) - l n j ω))

theorem blockError_measurable (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (ha : ∀ n j, Measurable (a n j)) (hl : ∀ n j, Measurable (l n j))
    (hu : ∀ n j, Measurable (u n j)) (n : ℕ) :
    Measurable (blockError T I a l u n) := by
  apply Finset.measurable_sum
  intro j hj
  exact (ha n j).mul ((selected_measurable T n _ (hu n j)).sub
    (selected_measurable T n _ (hl n j)))

theorem blockError_bound (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (hl : ∀ n j ω, l n j ω ≤ n + 1) (hu : ∀ n j ω, u n j ω ≤ n + 1)
    (n : ℕ) (ω : JointSample) :
    |blockError T I a l u n ω| ≤
      (2 * ∑ j ∈ I, |a n j ω|) * maximum T n ω := by
  have he (m : ℕ) (hm : m ≤ n + 1) :
      |IBMUniformPrefixQuartic.error T n m ω| ≤ maximum T n ω :=
    Finset.le_sup' (fun k => |IBMUniformPrefixQuartic.error T n k ω|)
      (Finset.mem_range.mpr (by omega))
  calc
    _ ≤ ∑ j ∈ I, |a n j ω * (IBMUniformPrefixQuartic.error T n (u n j ω) ω -
        IBMUniformPrefixQuartic.error T n (l n j ω) ω)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ I, |a n j ω| * (2 * maximum T n ω) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have h := abs_sub_le (IBMUniformPrefixQuartic.error T n (u n j ω) ω) 0
        (IBMUniformPrefixQuartic.error T n (l n j ω) ω)
      simp only [sub_zero, zero_sub, abs_neg] at h
      linarith [he _ (hu n j ω), he _ (hl n j ω)]
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Coefficients may depend on the grid and both sources, provided their
finite sum of absolute values has a pointwise finite envelope uniform in N. -/
theorem blockError_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (ha : ∀ n j, Measurable (a n j)) (hl : ∀ n j, Measurable (l n j))
    (hu : ∀ n j, Measurable (u n j))
    (hlN : ∀ n j ω, l n j ω ≤ n + 1) (huN : ∀ n j ω, u n j ω ≤ n + 1)
    (C : JointSample → ℝ) (hC : ∀ n ω, (∑ j ∈ I, |a n j ω|) ≤ C ω) :
    TendstoInMeasure jointMeasure (blockError T I a l u) atTop (fun _ => (0 : ℝ)) := by
  apply dominated_tendstoInMeasure hT _ (fun ω => 2*C ω)
    (blockError_measurable T I a l u ha hl hu)
  intro n ω
  exact (blockError_bound T I a l u hlN huN n ω).trans
    (mul_le_mul_of_nonneg_right (by linarith [hC n ω]) (maximum_nonneg T n ω))

theorem blockError_identity {T : ℝ≥0} (hT : 0 < T) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (n : ℕ) (ω : JointSample) :
    blockError T I a l u n ω =
      weightedQuartic T I a l u n ω - 3 * timeIntegral T I a l u n ω := by
  unfold blockError weightedQuartic timeIntegral
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [error_eq hT, error_eq hT]
  ring

theorem timeIntegral_measurable (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (ha : ∀ n j, Measurable (a n j)) (hl : ∀ n j, Measurable (l n j))
    (hu : ∀ n j, Measurable (u n j)) (n : ℕ) :
    Measurable (timeIntegral T I a l u n) := by
  have hcast : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
  apply Finset.measurable_sum
  intro j hj
  exact (ha n j).mul (((hcast.comp (hu n j)).sub
    (hcast.comp (hl n j))).const_mul _)

theorem weightedQuartic_measurable {T : ℝ≥0} (hT : 0 < T) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (ha : ∀ n j, Measurable (a n j)) (hl : ∀ n j, Measurable (l n j))
    (hu : ∀ n j, Measurable (u n j)) (n : ℕ) :
    Measurable (weightedQuartic T I a l u n) := by
  have he : weightedQuartic T I a l u n = fun ω =>
      blockError T I a l u n ω + 3 * timeIntegral T I a l u n ω := by
    funext ω
    have := blockError_identity hT I a l u n ω
    linarith
  rw [he]
  exact (blockError_measurable T I a l u ha hl hu n).add
    ((timeIntegral_measurable T I a l u ha hl hu n).const_mul 3)

/-- The block observable is a sum of actual fourth powers on the requested
index intervals. Ordered endpoints are essential for this Ico form. -/
theorem weightedQuartic_eq_Ico (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (n : ℕ) (ω : JointSample) (hlu : ∀ j ∈ I, l n j ω ≤ u n j ω) :
    weightedQuartic T I a l u n ω =
      ∑ j ∈ I, a n j ω * ∑ i ∈ Finset.Ico (l n j ω) (u n j ω),
        (ibmValue (grid (T/(n + 1)) (i + 1)) ω - ibmValue (grid (T/(n + 1)) i) ω)^4 := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_Ico_eq_sub _ (hlu j hj)]
  rfl

def stepWeight (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (n : ℕ) (ω : JointSample) (t : ℝ) : ℝ :=
  ∑ j ∈ I, (Ioc ((grid (T/(n + 1)) (l n j ω) : ℝ≥0) : ℝ)
    ((grid (T/(n + 1)) (u n j ω) : ℝ≥0) : ℝ)).indicator (fun _ => a n j ω) t

theorem stepWeight_integrable (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (n : ℕ) (ω : JointSample) : Integrable (stepWeight T I a l u n ω) := by
  apply integrable_finsetSum
  intro j hj
  exact (integrableOn_const (C := a n j ω)
    (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc

theorem timeIntegral_eq_integral (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (n : ℕ) (ω : JointSample) (hlu : ∀ j ∈ I, l n j ω ≤ u n j ω) :
    timeIntegral T I a l u n ω = ∫ t, stepWeight T I a l u n ω t := by
  unfold stepWeight timeIntegral
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_indicator_const _ measurableSet_Ioc,
      Real.volume_real_Ioc_of_le (by
        simp only [grid, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add,
          NNReal.coe_one, NNReal.coe_natCast]
        gcongr
        exact_mod_cast hlu j hj)]
    simp only [smul_eq_mul, grid, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add,
      NNReal.coe_one, NNReal.coe_natCast]
    ring
  · intro j hj
    exact (integrableOn_const (C := a n j ω)
      (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc

theorem stepIntegral_measurable (T : ℝ≥0) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (ha : ∀ n j, Measurable (a n j)) (hl : ∀ n j, Measurable (l n j))
    (hu : ∀ n j, Measurable (u n j)) (n : ℕ)
    (hlu : ∀ j ω, l n j ω ≤ u n j ω) :
    Measurable (fun ω => ∫ t, stepWeight T I a l u n ω t) := by
  have he : (fun ω => ∫ t, stepWeight T I a l u n ω t) = timeIntegral T I a l u n := by
    funext ω
    exact (timeIntegral_eq_integral T I a l u n ω (fun j _ => hlu j ω)).symm
  rw [he]
  exact timeIntegral_measurable T I a l u ha hl hu n

/-- A genuine random weighted quartic sum minus THREE times its actual
Lebesgue step-weight integral converges to zero in probability. -/
theorem weighted_step_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) (I : Finset ι)
    (a : ℕ → ι → JointSample → ℝ) (l u : ℕ → ι → JointSample → ℕ)
    (ha : ∀ n j, Measurable (a n j)) (hl : ∀ n j, Measurable (l n j))
    (hu : ∀ n j, Measurable (u n j))
    (hlN : ∀ n j ω, l n j ω ≤ n + 1) (huN : ∀ n j ω, u n j ω ≤ n + 1)
    (hlu : ∀ n j ω, l n j ω ≤ u n j ω)
    (C : JointSample → ℝ) (hC : ∀ n ω, (∑ j ∈ I, |a n j ω|) ≤ C ω) :
    TendstoInMeasure jointMeasure
      (fun n ω => weightedQuartic T I a l u n ω -
        3 * ∫ t, stepWeight T I a l u n ω t)
      atTop (fun _ => (0 : ℝ)) := by
  refine (blockError_tendstoInMeasure hT I a l u ha hl hu hlN huN C hC).congr
    (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl)
  rw [blockError_identity hT, timeIntegral_eq_integral T I a l u n ω (fun j _ => hlu n j ω)]

end OperatorDerivativeRewrite.Foundation.IBMRandomBlockQuartic
