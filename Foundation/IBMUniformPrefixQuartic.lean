import Foundation.IBMUniformSubfamilyQuartic
import Foundation.IBMUniformPrefixClock

/-! Actual common-grid quartic prefixes approach three times their own physical
endpoint, even when the deterministic prefix changes with every grid size. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformPrefixQuartic
open InfiniteGaussian IBMSourceLaws IBMConstructedSources
open IBMUniformClockGridEnergy IBMUniformSubfamilyQuartic IBMUniformPrefixClock
open IBMReflectedClockCorrection
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

def penalty (T : ℝ≥0) (n m : ℕ) (ω : SampleSpace) : ℝ :=
  ∑ i ∈ Finset.range m, crossingPenalty (clockPath ω (grid (T/(n + 1)) i))
    (clockPath ω (grid (T/(n + 1)) (i + 1)))

theorem penalty_nonneg (T : ℝ≥0) (n m : ℕ) (ω : SampleSpace) :
    0 ≤ penalty T n m ω :=
  Finset.sum_nonneg fun _ _ => (crossingPenalty_bounds _ _).1

theorem penalty_le (T : ℝ≥0) (n m : ℕ) (hm : m ≤ n + 1) (ω : SampleSpace) :
    penalty T n m ω ≤ IBMUniformCrossingPenalty.penalty T (n + 1) ω := by
  unfold penalty IBMUniformCrossingPenalty.penalty
  simp only [Nat.cast_add, Nat.cast_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
    (fun _ _ _ => (crossingPenalty_bounds _ _).1)

def meanError (T : ℝ≥0) (n m : ℕ) (ω : SampleSpace) : ℝ :=
  mean (prefixIntervals T (n + 1) m) ω - 3 * ((T : ℝ)/(n + 1)*m)

theorem meanError_identity {T : ℝ≥0} (hT : 0 < T) (n m : ℕ) (ω : SampleSpace) :
    meanError T n m ω = 3 * actualError T n m ω - 3 * penalty T n m ω := by
  unfold meanError mean
  rw [sum_prefix hT n m]
  simp only [IBMUniformQuarticFamily.segment, Nat.cast_add, Nat.cast_one,
    reflected_increment_sq, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold actualError penalty
  ring

theorem meanError_bound {T : ℝ≥0} (hT : 0 < T) (n m : ℕ) (hm : m ≤ n + 1)
    (ω : SampleSpace) :
    |meanError T n m ω| ≤ 3 * |actualError T n m ω| +
      3 * IBMUniformCrossingPenalty.penalty T (n + 1) ω := by
  rw [meanError_identity hT]
  have h := abs_sub_le (3 * actualError T n m ω) 0 (3 * penalty T n m ω)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul,
    abs_of_nonneg (penalty_nonneg T n m ω)] at h
  norm_num at h
  linarith [penalty_le T n m hm ω]

theorem meanError_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T)
    (m : ℕ → ℕ) (hm : ∀ n, m n ≤ n + 1) :
    TendstoInMeasure gaussianProduct (fun n => meanError T n (m n))
      atTop (fun _ => (0 : ℝ)) := by
  have hc := tendstoInMeasure_iff_measureReal_norm.mp (actualError_tendstoInMeasure T m hm)
  have hp := tendstoInMeasure_iff_measureReal_norm.mp
    (IBMUniformCrossingPenalty.penalty_tendstoInMeasure hT)
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have he : 0 < ε/6 := by positivity
  have hb (n : ℕ) :
      gaussianProduct.real {ω | ε ≤ |meanError T n (m n) ω|} ≤
      gaussianProduct.real {ω | ε/6 ≤ |actualError T n (m n) ω|} +
      gaussianProduct.real {ω | ε/6 ≤ |IBMUniformCrossingPenalty.penalty T (n + 1) ω|} := by
    apply le_trans (measureReal_mono (μ := gaussianProduct) (s₂ :=
      {ω | ε/6 ≤ |actualError T n (m n) ω|} ∪
      {ω | ε/6 ≤ |IBMUniformCrossingPenalty.penalty T (n + 1) ω|}) ?_ (by finiteness))
      (measureReal_union_le _ _)
    intro ω hω
    by_contra hn
    have h1 : |actualError T n (m n) ω| < ε/6 :=
      lt_of_not_ge fun h => hn (Or.inl h)
    have h2 : IBMUniformCrossingPenalty.penalty T (n + 1) ω < ε/6 := by
      have hh : |IBMUniformCrossingPenalty.penalty T (n + 1) ω| < ε/6 :=
        lt_of_not_ge fun h => hn (Or.inr h)
      simpa only [abs_of_nonneg (IBMUniformCrossingPenalty.penalty_nonneg _ _ _)] using hh
    have := meanError_bound hT n (m n) (hm n) ω
    change ε ≤ |meanError T n (m n) ω| at hω
    linarith
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [sub_zero, Real.norm_eq_abs, add_zero] using (hc _ he).add (hp _ he)

def error (T : ℝ≥0) (n m : ℕ) (ω : JointSample) : ℝ :=
  quartic (prefixIntervals T (n + 1) m) ω - 3 * ((T : ℝ)/(n + 1)*m)

/-- Centering by the actual prefix endpoint is proved, not supplied as a
random conditional-mean hypothesis. Prefix selection is deterministic. -/
theorem error_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T)
    (m : ℕ → ℕ) (hm : ∀ n, m n ≤ n + 1) :
    TendstoInMeasure jointMeasure (fun n => error T n (m n))
      atTop (fun _ => (0 : ℝ)) := by
  have hr := tendstoInMeasure_iff_measureReal_norm.mp
    (prefix_residual_tendstoInMeasure hT m hm)
  have hc := tendstoInMeasure_iff_measureReal_norm.mp (meanError_tendstoInMeasure hT m hm)
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have he : 0 < ε/2 := by positivity
  have hb (n : ℕ) :
      jointMeasure.real {ω | ε ≤ |error T n (m n) ω|} ≤
      jointMeasure.real {ω | ε/2 ≤ |residual (prefixIntervals T (n + 1) (m n)) ω|} +
      gaussianProduct.real {y | ε/2 ≤ |meanError T n (m n) y|} := by
    have hs : {ω : JointSample | ε ≤ |error T n (m n) ω|} ⊆
        {ω | ε/2 ≤ |residual (prefixIntervals T (n + 1) (m n)) ω|} ∪
        {ω | ε/2 ≤ |meanError T n (m n) ω.2|} := by
      intro ω hω
      by_contra hn
      have h1 : |residual (prefixIntervals T (n + 1) (m n)) ω| < ε/2 :=
        lt_of_not_ge fun h => hn (Or.inl h)
      have h2 : |meanError T n (m n) ω.2| < ε/2 :=
        lt_of_not_ge fun h => hn (Or.inr h)
      have ha := abs_add_le (residual (prefixIntervals T (n + 1) (m n)) ω)
        (meanError T n (m n) ω.2)
      have hid : residual (prefixIntervals T (n + 1) (m n)) ω +
          meanError T n (m n) ω.2 = error T n (m n) ω := by
        unfold IBMUniformSubfamilyQuartic.residual meanError error
        ring
      rw [hid] at ha
      change ε ≤ |error T n (m n) ω| at hω
      linarith
    have h := (measureReal_mono (μ := jointMeasure) hs (by finiteness)).trans
      (measureReal_union_le _ _)
    have hmarg : jointMeasure.real {ω : JointSample | ε/2 ≤ |meanError T n (m n) ω.2|} =
        gaussianProduct.real {y | ε/2 ≤ |meanError T n (m n) y|} :=
      IBMUniformQuarticVariation.clock_event_measure {y | ε/2 ≤ |meanError T n (m n) y|}
    rw [hmarg] at h
    exact h
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [sub_zero, Real.norm_eq_abs, add_zero] using (hr _ he).add (hc _ he)

end OperatorDerivativeRewrite.Foundation.IBMUniformPrefixQuartic
