import Foundation.IBMFiniteQuarticSecondMoment
import Foundation.IBMConstructedSources
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! A spatial occupation-energy estimate for actual conditional IBM quartic sums.
Repeated visits to the same scenery interval are counted, not discarded as
temporally independent. The Brownian-clock limit of this energy is not assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace OperatorDerivativeRewrite.Foundation.IBMQuarticOccupationEnergy
open IBMSpatialOverlap

def interval (a b : ℝ) : Set ℝ := Ioc (min a b) (max a b)

def hit (a b x : ℝ) : ℝ := (interval a b).indicator (fun _ => 1) x

def count {ι : Type*} (I : Finset ι) (a b : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ I, hit (a i) (b i) x

theorem hit_nonneg (a b x : ℝ) : 0 ≤ hit a b x := by
  by_cases h : x ∈ interval a b <;> simp [hit, h]

theorem hit_integrable (a b : ℝ) : Integrable (hit a b) := by
  unfold hit interval
  exact (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne)).integrable_indicator
    measurableSet_Ioc

theorem hit_mass (a b : ℝ) : (∫ x, hit a b x) = |b-a| := by
  simp only [hit, interval, integral_indicator_const (1 : ℝ) measurableSet_Ioc,
    smul_eq_mul, mul_one, Real.volume_real_Ioc]
  rcases le_total a b with h | h
  · simp [h, abs_of_nonneg (sub_nonneg.mpr h)]
  · simp [h, abs_of_nonpos (sub_nonpos.mpr h)]

theorem abs_overlap (a b c d : ℝ) :
    |signedOverlap a b c d| =
      max (min (max a b) (max c d) - max (min a b) (min c d)) 0 := by
  have hn : 0 ≤ max (min (max a b) (max c d) - max (min a b) (min c d)) 0 :=
    le_max_right _ _
  simp only [signedOverlap, abs_mul]
  split_ifs <;> simp [abs_of_nonneg hn]

theorem overlap_le_left (a b c d : ℝ) : |signedOverlap a b c d| ≤ |b-a| := by
  have he : |b-a| = max a b - min a b := by
    rcases le_total a b with h | h
    · simp [h, abs_of_nonneg (sub_nonneg.mpr h)]
    · simp [h, abs_of_nonpos (sub_nonpos.mpr h)]
  rw [abs_overlap, he]
  apply max_le
  · linarith [min_le_left (max a b) (max c d), le_max_left (min a b) (min c d)]
  · exact sub_nonneg.mpr min_le_max

theorem overlap_le_right (a b c d : ℝ) : |signedOverlap a b c d| ≤ |d-c| := by
  have he : |d-c| = max c d - min c d := by
    rcases le_total c d with h | h
    · simp [h, abs_of_nonneg (sub_nonneg.mpr h)]
    · simp [h, abs_of_nonpos (sub_nonpos.mpr h)]
  rw [abs_overlap, he]
  apply max_le
  · linarith [min_le_right (max a b) (max c d), le_max_right (min a b) (min c d)]
  · exact sub_nonneg.mpr min_le_max

theorem hit_product (a b c d x : ℝ) :
    hit a b x * hit c d x =
      (interval a b ∩ interval c d).indicator (fun _ => (1 : ℝ)) x := by
  by_cases h : x ∈ interval a b <;> by_cases k : x ∈ interval c d <;>
    simp [hit, h, k]

theorem hit_product_integrable (a b c d : ℝ) :
    Integrable (fun x => hit a b x * hit c d x) := by
  simp_rw [hit_product, interval, Ioc_inter_Ioc]
  exact (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne)).integrable_indicator
    measurableSet_Ioc

theorem hit_product_mass (a b c d : ℝ) :
    (∫ x, hit a b x * hit c d x) = |signedOverlap a b c d| := by
  simp_rw [hit_product, interval, Ioc_inter_Ioc]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ioc, abs_overlap]
  simp [Real.volume_real_Ioc]

theorem count_integrable {ι : Type*} (I : Finset ι) (a b : ι → ℝ) :
    Integrable (count I a b) :=
  integrable_finsetSum I fun i _ => hit_integrable (a i) (b i)

theorem count_square_integrable {ι : Type*} (I : Finset ι) (a b : ι → ℝ) :
    Integrable (fun x => count I a b x ^ 2) := by
  have h (x : ℝ) : count I a b x ^ 2 =
      ∑ i ∈ I, ∑ j ∈ I, hit (a i) (b i) x * hit (a j) (b j) x := by
    simp only [count, pow_two, Finset.sum_mul_sum]
  simp_rw [h]
  exact integrable_finsetSum I fun i _ => integrable_finsetSum I fun j _ =>
    hit_product_integrable _ _ _ _

/-- Exact return-count energy: every pair of overlapping spatial traversals
contributes its unsigned overlap length, regardless of orientation. -/
theorem count_square_mass {ι : Type*} (I : Finset ι) (a b : ι → ℝ) :
    (∫ x, count I a b x ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I, |signedOverlap (a i) (b i) (a j) (b j)| := by
  have h (x : ℝ) : count I a b x ^ 2 =
      ∑ i ∈ I, ∑ j ∈ I, hit (a i) (b i) x * hit (a j) (b j) x := by
    simp only [count, pow_two, Finset.sum_mul_sum]
  simp_rw [h]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · simp_rw [hit_product_mass]
    · exact fun j _ => hit_product_integrable _ _ _ _
  · exact fun i _ => integrable_finsetSum I fun j _ => hit_product_integrable _ _ _ _

/-- Repeated traversals contribute quadratically in their number. In
particular their contribution cannot be replaced by the sum of diagonal terms. -/
theorem repeated_return_energy (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (∫ x, count (Finset.range n) (fun _ => 0) (fun _ => r) x ^ 2) =
      (n : ℝ) ^ 2 * r := by
  rw [count_square_mass]
  simp only [abs_overlap, max_eq_right hr, min_eq_left hr, min_self, max_self,
    sub_zero, max_eq_left hr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Maximum spatial increment tending to zero is insufficient by itself:
`n²` repeated traversals of `[0,1/n]` have nonvanishing weighted energy.
This is a finite spatial-family test, not an assertion about Brownian clocks. -/
theorem shrinking_repeated_return_energy (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) ^ 3 *
      (∫ x, count (Finset.range (n ^ 2)) (fun _ => 0) (fun _ => 1 / (n : ℝ)) x ^ 2) = 1 := by
  rw [repeated_return_energy _ _ (by positivity)]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  push_cast
  field_simp [hne]

/-- A quantitative overlap bound for the exact eighth-moment covariance. -/
theorem quartic_covariance_le (a b c d δ : ℝ) (hδ : 0 ≤ δ)
    (hab : |b - a| ≤ δ) (hcd : |d - c| ≤ δ) :
    72 * |b-a| * |d-c| * signedOverlap a b c d ^ 2 +
      24 * signedOverlap a b c d ^ 4 ≤ 96 * δ ^ 3 * |signedOverlap a b c d| := by
  let o := |signedOverlap a b c d|
  have ho : 0 ≤ o := abs_nonneg _
  have hod : o ≤ δ := (overlap_le_left a b c d).trans hab
  have hprod : |b-a| * |d-c| ≤ δ ^ 2 := by
    simpa [pow_two] using mul_le_mul hab hcd (abs_nonneg _) hδ
  have ho2 : o ^ 2 ≤ δ * o := by nlinarith
  have ho4 : o ^ 4 ≤ δ ^ 3 * o := by
    calc
      o ^ 4 = o ^ 2 * o ^ 2 := by ring
      _ ≤ (δ * o) * (δ * o) := mul_self_le_mul_self (sq_nonneg o) ho2
      _ = δ ^ 2 * o ^ 2 := by ring
      _ ≤ δ ^ 2 * (δ * o) := mul_le_mul_of_nonneg_left ho2 (sq_nonneg δ)
      _ = _ := by ring
  have hfirst := mul_le_mul_of_nonneg_right hprod (sq_nonneg o)
  have hsecond := mul_le_mul_of_nonneg_left ho2 (sq_nonneg δ)
  have he2 : signedOverlap a b c d ^ 2 = o ^ 2 := by simp [o, sq_abs]
  have he4 : signedOverlap a b c d ^ 4 = o ^ 4 := by
    calc
      _ = (signedOverlap a b c d ^ 2) ^ 2 := by ring
      _ = (o ^ 2) ^ 2 := congrArg (fun x : ℝ => x ^ 2) he2
      _ = _ := by ring
  rw [he2, he4]
  nlinarith

theorem count_mass {ι : Type*} (I : Finset ι) (a b : ι → ℝ) :
    (∫ x, count I a b x) = ∑ i ∈ I, |b i-a i| := by
  unfold count
  rw [integral_finsetSum I (fun i _ => hit_integrable (a i) (b i))]
  simp_rw [hit_mass]

/-- A bound on spatial traversal multiplicity controls the whole occupation
energy. Temporal intervals may overlap or revisit the same spatial region. -/
theorem count_square_le {ι : Type*} (I : Finset ι) (a b : ι → ℝ) (M : ℝ)
    (hM : ∀ x, count I a b x ≤ M) :
    (∫ x, count I a b x ^ 2) ≤ M * ∑ i ∈ I, |b i-a i| := by
  calc
    _ ≤ ∫ x, M * count I a b x := by
      apply integral_mono (count_square_integrable I a b) ((count_integrable I a b).const_mul M)
      intro x
      have hn : 0 ≤ count I a b x := Finset.sum_nonneg fun i _ => hit_nonneg _ _ _
      nlinarith [hM x]
    _ = _ := by rw [integral_const_mul, count_mass]

open InfiniteGaussian IBMFiniteQuartic IBMFiniteQuarticSecondMoment

/-- The actual scenery-conditional variance is bounded by maximum spatial
increment cubed times occupation energy. This is a reduction, not an assertion
that the Brownian-clock energy converges. -/
theorem conditional_variance_le_occupation
    (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] IBMSourceLaws.sceneryBase r)
    (I : Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmesh : ∀ p ∈ I, abs (|C p.2 ωY| - |C p.1 ωY|) ≤ δ) :
    (∫ ωX, quarticSum S C hS hC I ωX ωY ^ 2 ∂gaussianProduct) -
      (∫ ωX, quarticSum S C hS hC I ωX ωY ∂gaussianProduct) ^ 2 ≤
      96 * δ ^ 3 * ∫ x, count I (fun p => |C p.1 ωY|) (fun p => |C p.2 ωY|) x ^ 2 := by
  rw [conditional_quarticSum_centered_second_moment S C hS hC hmodS,
    count_square_mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  exact quartic_covariance_le _ _ _ _ δ hδ (hmesh p hp) (hmesh q hq)

theorem conditional_quartic_memLp_two
    (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] IBMSourceLaws.sceneryBase r)
    (I : Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) :
    MemLp (fun ωX => quarticSum S C hS hC I ωX ωY) 2 gaussianProduct := by
  exact memLp_finsetSum I fun p _ =>
    conditional_fourth_memLp_two S C hS hC hmodS p.1 p.2 ωY

/-- The estimate controls an actual nonnegative mean-square error, not merely
a formal difference of two moments. -/
theorem conditional_centered_square_le_occupation
    (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] IBMSourceLaws.sceneryBase r)
    (I : Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmesh : ∀ p ∈ I, abs (|C p.2 ωY| - |C p.1 ωY|) ≤ δ) :
    (∫ ωX, (quarticSum S C hS hC I ωX ωY -
        ∫ η, quarticSum S C hS hC I η ωY ∂gaussianProduct) ^ 2 ∂gaussianProduct) ≤
      96 * δ ^ 3 * ∫ x, count I (fun p => |C p.1 ωY|) (fun p => |C p.2 ωY|) x ^ 2 := by
  have hm := conditional_quartic_memLp_two S C hS hC hmodS I ωY
  rw [← ProbabilityTheory.variance_eq_integral hm.aemeasurable,
    ProbabilityTheory.variance_eq_sub hm]
  exact conditional_variance_le_occupation S C hS hC hmodS I ωY δ hδ hmesh

/-- Spatial return multiplicity is sufficient; no temporal independence
assumption is made. Establishing a Brownian-clock rate is a separate obligation. -/
theorem conditional_centered_square_le_multiplicity
    (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] IBMSourceLaws.sceneryBase r)
    (I : Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) (δ M : ℝ) (hδ : 0 ≤ δ)
    (hmesh : ∀ p ∈ I, abs (|C p.2 ωY| - |C p.1 ωY|) ≤ δ)
    (hM : ∀ x, count I (fun p => |C p.1 ωY|) (fun p => |C p.2 ωY|) x ≤ M) :
    (∫ ωX, (quarticSum S C hS hC I ωX ωY -
        ∫ η, quarticSum S C hS hC I η ωY ∂gaussianProduct) ^ 2 ∂gaussianProduct) ≤
      96 * δ ^ 3 * M * ∑ p ∈ I, abs (|C p.2 ωY| - |C p.1 ωY|) := by
  exact (conditional_centered_square_le_occupation S C hS hC hmodS I ωY δ hδ hmesh).trans
    ((mul_le_mul_of_nonneg_left (count_square_le I _ _ M hM) (by positivity)).trans_eq
      (by ring))

/-- Precise conditional mean-square convergence criterion. It assumes decay
of the weighted occupation energy, not just decay of maximum increment. -/
theorem conditional_centered_square_tendsto
    (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] IBMSourceLaws.sceneryBase r)
    (I : ℕ → Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 ≤ δ n)
    (hmesh : ∀ n p, p ∈ I n → abs (|C p.2 ωY| - |C p.1 ωY|) ≤ δ n)
    (henergy : Filter.Tendsto
      (fun n => δ n ^ 3 * ∫ x, count (I n) (fun p => |C p.1 ωY|)
        (fun p => |C p.2 ωY|) x ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ ωX, (quarticSum S C hS hC (I n) ωX ωY -
      ∫ η, quarticSum S C hS hC (I n) η ωY ∂gaussianProduct) ^ 2 ∂gaussianProduct)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _)
    (fun n => conditional_centered_square_le_occupation S C hS hC hmodS
      (I n) ωY (δ n) (hδ n) (hmesh n))
  simpa only [mul_assoc, mul_zero] using henergy.const_mul 96

/-- Instantiation on the existing genuine constructed Brownian scenery and
clock: no supplied process-existence or modification hypothesis remains. -/
theorem actual_conditional_centered_square_le
    (I : Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmesh : ∀ p ∈ I, abs (|IBMConstructedSources.clockPath ωY p.2| -
      |IBMConstructedSources.clockPath ωY p.1|) ≤ δ) :
    (∫ ωX, (quarticSum (fun r ω => IBMConstructedSources.sceneryPath ω r)
      (fun t ω => IBMConstructedSources.clockPath ω t)
      (fun ω => (IBMConstructedSources.sceneryPath ω).continuous)
      (fun ω => (IBMConstructedSources.clockPath ω).continuous) I ωX ωY -
      ∫ η, quarticSum (fun r ω => IBMConstructedSources.sceneryPath ω r)
        (fun t ω => IBMConstructedSources.clockPath ω t)
        (fun ω => (IBMConstructedSources.sceneryPath ω).continuous)
        (fun ω => (IBMConstructedSources.clockPath ω).continuous) I η ωY ∂gaussianProduct) ^ 2
      ∂gaussianProduct) ≤ 96 * δ ^ 3 * ∫ x,
        count I (fun p => |IBMConstructedSources.clockPath ωY p.1|)
          (fun p => |IBMConstructedSources.clockPath ωY p.2|) x ^ 2 :=
  conditional_centered_square_le_occupation _ _ _ _
    IBMConstructedSources.sceneryPath_coordinate_ae I ωY δ hδ hmesh

end OperatorDerivativeRewrite.Foundation.IBMQuarticOccupationEnergy
