import Foundation.IBMQuarticOccupationEnergy
import Foundation.IBMFoldedTransitionBound

/-! Finite spatial-traversal envelopes under the genuine Brownian clock law.
These discrete two-time bounds are distinct from continuous-time mollifier
covariance estimates. No random-mesh decay or quartic limit is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMClockTraversalEnvelope
open IBMFoldedTransitionBound IBMSpatialOverlap IBMQuarticOccupationEnergy
open InfiniteGaussian GaussianTimeProcess

def tent (δ x : ℝ) : ℝ := max (2 * δ - |x|) 0

theorem tent_nonneg (δ x : ℝ) : 0 ≤ tent δ x := le_max_right _ _

theorem tent_continuous (δ : ℝ) : Continuous (tent δ) := by
  unfold tent
  fun_prop

theorem tent_le {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : tent δ x ≤ 2 * δ := by
  unfold tent
  exact max_le (by linarith [abs_nonneg x]) (by positivity)

theorem tent_eq_zero {δ x : ℝ} (hx : x ∉ Icc (-2 * δ) (2 * δ)) :
    tent δ x = 0 := by
  unfold tent
  rw [max_eq_right]
  by_contra h
  apply hx
  have ha : |x| < 2 * δ := by linarith
  rcases abs_lt.mp ha with ⟨hl, hu⟩
  constructor <;> linarith

theorem tent_integrable {δ : ℝ} (hδ : 0 ≤ δ) : Integrable (tent δ) := by
  have hi : Integrable ((Icc (-2 * δ) (2 * δ)).indicator (fun _ : ℝ => 2 * δ)) :=
    (integrableOn_const (C := 2 * δ) (hs := measure_Icc_lt_top.ne)).integrable_indicator
      measurableSet_Icc
  apply hi.mono' (tent_continuous δ).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg δ x)]
    by_cases hx : x ∈ Icc (-2 * δ) (2 * δ)
    · rw [indicator_of_mem hx]
      exact tent_le hδ x
    · rw [indicator_of_notMem hx, tent_eq_zero hx]

theorem tent_mass_le {δ : ℝ} (hδ : 0 ≤ δ) : (∫ x, tent δ x) ≤ 8 * δ ^ 2 := by
  let f := (Icc (-2 * δ) (2 * δ)).indicator (fun _ : ℝ => 2 * δ)
  have hi : Integrable f :=
    (integrableOn_const (C := 2 * δ) (hs := measure_Icc_lt_top.ne)).integrable_indicator
      measurableSet_Icc
  calc
    _ ≤ ∫ x, f x := by
      apply integral_mono (tent_integrable hδ) hi
      intro x
      change tent δ x ≤ (Icc (-2 * δ) (2 * δ)).indicator (fun _ : ℝ => 2 * δ) x
      by_cases hx : x ∈ Icc (-2 * δ) (2 * δ)
      · rw [indicator_of_mem hx]
        exact tent_le hδ x
      · rw [indicator_of_notMem hx, tent_eq_zero hx]
    _ = _ := by
      simp only [f, integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
        Real.volume_real_Icc]
      rw [max_eq_left (by linarith : 0 ≤ 2 * δ - -2 * δ)]
      ring

/-- Two arbitrary oriented traversals with length at most delta have overlap
dominated by a triangular function of their starting-point separation. -/
theorem overlap_le_tent {a b c d δ : ℝ} (hδ : 0 ≤ δ)
    (hab : |b - a| ≤ δ) (hcd : |d - c| ≤ δ) :
    |signedOverlap a b c d| ≤ tent δ (a - c) := by
  have hab' := abs_le.mp hab
  have hcd' := abs_le.mp hcd
  have hu₁ : max a b ≤ a + δ := max_le (by linarith) (by linarith)
  have hl₁ : a - δ ≤ min a b := le_min (by linarith) (by linarith)
  have hu₂ : max c d ≤ c + δ := max_le (by linarith) (by linarith)
  have hl₂ : c - δ ≤ min c d := le_min (by linarith) (by linarith)
  rw [abs_overlap]
  apply max_le_max
  · rcases le_total a c with hac | hca
    · rw [abs_of_nonpos (sub_nonpos.mpr hac)]
      linarith [min_le_left (max a b) (max c d), le_max_right (min a b) (min c d)]
    · rw [abs_of_nonneg (sub_nonneg.mpr hca)]
      linarith [min_le_right (max a b) (max c d), le_max_left (min a b) (min c d)]
  · rfl

theorem shifted_integrable {δ : ℝ} (hδ : 0 ≤ δ) (r : ℝ) :
    Integrable (fun x => tent δ (r - x)) := by
  simpa only [neg_sub] using (tent_integrable hδ).comp_neg.comp_sub_right r

theorem shifted_mass (δ r : ℝ) :
    (∫ x, tent δ (r - x)) = ∫ x, tent δ x := by
  have hn := integral_neg_eq_self (fun x : ℝ => tent δ (r + x)) volume
  simpa only [sub_eq_add_neg] using
    hn.trans (integral_add_left_eq_self (μ := volume) (tent δ) r)

/-- A genuine folded Gaussian transition bound, uniform in the center and mean.
The constant16 uses a simple rectangular bound on the triangular kernel mass. -/
theorem folded_tent_average_le {δ : ℝ} (hδ : 0 ≤ δ) (r a : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x, tent δ (r - |x|) ∂gaussianReal a v) ≤ 16 * δ ^ 2 * peak v := by
  have hc : Continuous (fun x => tent δ (r - x)) :=
    (tent_continuous δ).comp (continuous_const.sub continuous_id)
  have h := folded_average_le a hv hc (shifted_integrable hδ r)
    (fun x => tent_nonneg δ (r - x))
  rw [shifted_mass] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (tent_mass_le hδ)
    (mul_nonneg (by norm_num) (peak_nonneg v))).trans_eq (by ring))

theorem clock_tent_integrable {δ : ℝ} (hδ : 0 ≤ δ) (s t : ℝ≥0) :
    Integrable (fun ω => tent δ (|process s ω| - |process t ω|)) gaussianProduct := by
  apply Integrable.of_bound
    ((tent_continuous δ).measurable.comp
      ((continuous_abs.measurable.comp (process_stronglyMeasurable s).measurable).sub
        (continuous_abs.measurable.comp
          (process_stronglyMeasurable t).measurable))).aestronglyMeasurable
    (2 * δ)
  exact ae_of_all _ fun ω => by
    change ‖tent δ (|process s ω| - |process t ω|)‖ ≤ 2 * δ
    rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _ _)]
    exact tent_le hδ _

/-- Derived from the verified independent increment law, not an assumed
conditional density. The two endpoint values are generally dependent. -/
theorem clock_tent_le {δ : ℝ} (hδ : 0 ≤ δ) (s t : ℝ≥0) (hst : s < t) :
    (∫ ω, tent δ (|process s ω| - |process t ω|) ∂gaussianProduct) ≤
      16 * δ ^ 2 * peak (nndist (t : ℝ) (s : ℝ)) := by
  have hind : IndepFun (process s) (fun ω => process t ω - process s ω) gaussianProduct := by
    apply (process_disjoint_increments_independent 0 s s t (by positivity) le_rfl hst.le).congr
      ?_ (Filter.EventuallyEq.rfl)
    filter_upwards [process_zero_ae] with ω hω
    simp [hω]
  have hp := hind.hasLaw_prod (process_hasLaw s) (process_increment_hasLaw s t)
  let v : ℝ≥0 := nndist (t : ℝ) (s : ℝ)
  have hv : v ≠ 0 := by simpa [v] using (ne_of_gt hst)
  let F : ℝ × ℝ → ℝ := fun p => tent δ (|p.1| - |p.1 + p.2|)
  have hF : Continuous F := (tent_continuous δ).comp
    (continuous_fst.abs.sub (continuous_fst.add continuous_snd).abs)
  have hi : Integrable F ((gaussianReal 0 s).prod (gaussianReal 0 v)) :=
    Integrable.of_bound hF.aestronglyMeasurable (2 * δ) (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _ _)]
      exact tent_le hδ _)
  have he : (∫ ω, tent δ (|process s ω| - |process t ω|) ∂gaussianProduct) =
      ∫ p, F p ∂(gaussianReal 0 s).prod (gaussianReal 0 v) := by
    convert hp.integral_comp hF.aestronglyMeasurable using 1
    congr 1
    funext ω
    simp [F]
  rw [he, integral_prod _ hi]
  calc
    _ ≤ ∫ _a : ℝ, 16 * δ ^ 2 * peak v ∂gaussianReal 0 s := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun a => integral_nonneg fun b => tent_nonneg δ _)
        (integrable_const _)
      exact ae_of_all _ fun a => by
        have hl := gaussianReal_const_add (HasLaw.id (μ := gaussianReal 0 v)) a
        have hc : Continuous (fun y : ℝ => tent δ (|a| - |y|)) :=
          (tent_continuous δ).comp (continuous_const.sub continuous_abs)
        have heq := hl.integral_comp hc.aestronglyMeasurable
        simp only [zero_add, Function.comp_def, id_eq] at heq
        change (∫ b, tent δ (|a| - |a+b|) ∂gaussianReal 0 v) ≤ _
        rw [heq]
        exact folded_tent_average_le hδ |a| a hv
    _ = _ := by simp [v]

theorem actual_clock_tent_le {δ : ℝ} (hδ : 0 ≤ δ) (s t : ℝ≥0) (hst : s < t) :
    (∫ ω, tent δ (|IBMConstructedSources.clockPath ω s| -
      |IBMConstructedSources.clockPath ω t|) ∂gaussianProduct) ≤
      16 * δ ^ 2 * peak (nndist (t : ℝ) (s : ℝ)) := by
  have he : (fun ω => tent δ (|IBMConstructedSources.clockPath ω s| -
      |IBMConstructedSources.clockPath ω t|)) =ᵐ[gaussianProduct]
      (fun ω => tent δ (|process s ω| - |process t ω|)) := by
    filter_upwards [IBMConstructedSources.clockPath_coordinate_ae s,
      IBMConstructedSources.clockPath_coordinate_ae t] with ω hs ht
    rw [hs, ht]
  rw [integral_congr_ae he]
  exact clock_tent_le hδ s t hst

def pairBound (δ : ℝ) (s t : ℝ≥0) : ℝ :=
  if s = t then 2 * δ else 16 * δ ^ 2 * peak (nndist (t : ℝ) (s : ℝ))

theorem actual_clock_tent_integrable {δ : ℝ} (hδ : 0 ≤ δ) (s t : ℝ≥0) :
    Integrable (fun ω => tent δ (|IBMConstructedSources.clockPath ω s| -
      |IBMConstructedSources.clockPath ω t|)) gaussianProduct := by
  apply (clock_tent_integrable hδ s t).congr
  filter_upwards [IBMConstructedSources.clockPath_coordinate_ae s,
    IBMConstructedSources.clockPath_coordinate_ae t] with ω hs ht
  rw [hs, ht]

/-- The diagonal is handled at its genuine finite value; zero variance is
never passed through a Gaussian density formula. -/
theorem actual_clock_pair_bound {δ : ℝ} (hδ : 0 ≤ δ) (s t : ℝ≥0) :
    (∫ ω, tent δ (|IBMConstructedSources.clockPath ω s| -
      |IBMConstructedSources.clockPath ω t|) ∂gaussianProduct) ≤ pairBound δ s t := by
  rcases lt_trichotomy s t with h | h | h
  · simpa [pairBound, ne_of_lt h] using actual_clock_tent_le hδ s t h
  · subst t
    simp [pairBound, tent, max_eq_left (by positivity : 0 ≤ 2 * δ)]
  · have he : (fun ω => tent δ (|IBMConstructedSources.clockPath ω s| -
        |IBMConstructedSources.clockPath ω t|)) =
        (fun ω => tent δ (|IBMConstructedSources.clockPath ω t| -
        |IBMConstructedSources.clockPath ω s|)) := by
      funext ω
      simp only [tent, abs_sub_comm]
    rw [he]
    simpa [pairBound, ne_of_gt h, nndist_comm] using actual_clock_tent_le hδ t s h

def energy {ι : Type*} (I : Finset ι) (τ : ι → ℝ≥0) (δ : ℝ) (ω : SampleSpace) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ I, tent δ (|IBMConstructedSources.clockPath ω (τ i)| -
    |IBMConstructedSources.clockPath ω (τ j)|)

theorem energy_integrable {ι : Type*} (I : Finset ι) (τ : ι → ℝ≥0)
    {δ : ℝ} (hδ : 0 ≤ δ) : Integrable (energy I τ δ) gaussianProduct :=
  integrable_finsetSum I fun i _ => integrable_finsetSum I fun j _ =>
    actual_clock_tent_integrable hδ (τ i) (τ j)

/-- Finite endpoint energy under the actual Brownian clock measure. Duplicate
times are allowed and are accounted for by their exact diagonal bound. -/
theorem energy_mean_le {ι : Type*} (I : Finset ι) (τ : ι → ℝ≥0)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ ω, energy I τ δ ω ∂gaussianProduct) ≤ ∑ i ∈ I, ∑ j ∈ I, pairBound δ (τ i) (τ j) := by
  unfold energy
  rw [integral_finsetSum]
  · apply Finset.sum_le_sum
    intro i hi
    rw [integral_finsetSum]
    · exact Finset.sum_le_sum fun j _ => actual_clock_pair_bound hδ (τ i) (τ j)
    · exact fun j _ => actual_clock_tent_integrable hδ (τ i) (τ j)
  · exact fun i _ => integrable_finsetSum I fun j _ => actual_clock_tent_integrable hδ (τ i) (τ j)

/-- On a bounded-increment clock sample, true traversal occupation energy is
dominated by the finite endpoint envelope whose mean has just been bounded. -/
theorem occupation_le_energy (I : Finset (ℝ≥0 × ℝ≥0)) (ω : SampleSpace)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmesh : ∀ p ∈ I, abs (|IBMConstructedSources.clockPath ω p.2| -
      |IBMConstructedSources.clockPath ω p.1|) ≤ δ) :
    (∫ x, count I (fun p => |IBMConstructedSources.clockPath ω p.1|)
      (fun p => |IBMConstructedSources.clockPath ω p.2|) x ^ 2) ≤
        energy I Prod.fst δ ω := by
  rw [count_square_mass]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  exact overlap_le_tent hδ (hmesh p hp) (hmesh q hq)

end OperatorDerivativeRewrite.Foundation.IBMClockTraversalEnvelope
