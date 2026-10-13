import Foundation.IBMFiniteQuarticSecondMoment
import Foundation.IBMConditionalMoments

/-! Brownian-clock second moments and bounds for conditional quartic sums. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace OperatorDerivativeRewrite.Foundation.IBMClockQuarticBound
open InfiniteGaussian IBMSourceLaws GaussianTimeProcess IBMConditionalMoments
open IBMFiniteQuartic IBMModificationBridge IBMContinuousComposition

/-- The verified pre-Brownian clock has the exact second increment moment. -/
theorem clockBase_increment_second (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, (process t ω - process s ω)^2 ∂gaussianProduct) = (t : ℝ) - s := by
  have hl := process_increment_hasLaw s t
  have he := hl.integral_comp (f := fun z : ℝ => z^2) (by fun_prop)
  simp only [Function.comp_def, Pi.sub_apply] at he
  rw [gaussian_zero_second] at he
  rw [he, Real.nndist_eq]
  have h : 0 ≤ (t : ℝ) - s := sub_nonneg.mpr (by exact hst)
  simp [Real.nnabs_of_nonneg h, hst]


/-- A continuous Brownian-clock modification retains its exact second
increment moment at deterministic ordered times. -/
theorem clockModified_increment_second
    (C : ℝ≥0 → SampleSpace → ℝ)
    (hmodC : ∀ r, C r =ᵐ[gaussianProduct] process r)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, (C t ω - C s ω)^2 ∂gaussianProduct) = (t : ℝ) - s := by
  have he : (fun ω => (C t ω - C s ω)^2) =ᵐ[gaussianProduct]
      (fun ω => (process t ω - process s ω)^2) := by
    filter_upwards [hmodC t, hmodC s] with ω ht hs
    rw [ht, hs]
  rw [integral_congr_ae he, clockBase_increment_second s t hst]

/-- The reflected-clock squared displacement is integrable. -/
theorem clock_reflected_increment_integrable
    (C : ℝ≥0 → SampleSpace → ℝ)
    (hmodC : ∀ r, C r =ᵐ[gaussianProduct] process r)
    (s t : ℝ≥0) :
    Integrable (fun ω => (|C t ω| - |C s ω|)^2) gaussianProduct := by
  have ht : MemLp (C t) 2 gaussianProduct :=
    (memLp_congr_ae (hmodC t)).2 (process_memLp t 2 (by simp))
  have hs : MemLp (C s) 2 gaussianProduct :=
    (memLp_congr_ae (hmodC s)).2 (process_memLp s 2 (by simp))
  have hdiff : MemLp (fun ω => |C t ω| - |C s ω|) 2 gaussianProduct :=
    ht.abs.sub hs.abs
  have hi := hdiff.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  convert hi using 1
  ext ω
  simp [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity :
    0 ≤ (|C t ω| - |C s ω|)^2)]

/-- Clock reflection can only decrease the expected squared increment. -/
theorem clock_reflected_increment_second_le
    (C : ℝ≥0 → SampleSpace → ℝ)
    (hmodC : ∀ r, C r =ᵐ[gaussianProduct] process r)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, (|C t ω| - |C s ω|)^2 ∂gaussianProduct) ≤ (t : ℝ) - s := by
  have hf := clock_reflected_increment_integrable C hmodC s t
  have ht : MemLp (C t) 2 gaussianProduct :=
    (memLp_congr_ae (hmodC t)).2 (process_memLp t 2 (by simp))
  have hs : MemLp (C s) 2 gaussianProduct :=
    (memLp_congr_ae (hmodC s)).2 (process_memLp s 2 (by simp))
  have hdiff : MemLp (fun ω => C t ω - C s ω) 2 gaussianProduct := ht.sub hs
  have hi := hdiff.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hg : Integrable (fun ω => (C t ω - C s ω)^2) gaussianProduct := by
    convert hi using 1
    ext ω
    simp [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity :
      0 ≤ (C t ω - C s ω)^2)]
  calc
    (∫ ω, (|C t ω| - |C s ω|)^2 ∂gaussianProduct) ≤
      ∫ ω, (C t ω - C s ω)^2 ∂gaussianProduct := by
        apply integral_mono_ae hf hg
        exact Filter.Eventually.of_forall (fun ω => by
          have h := (IBMReflectedClockCorrection.crossingPenalty_bounds
            (C s ω) (C t ω)).1
          dsimp only
          rw [IBMReflectedClockCorrection.reflected_increment_sq]
          linarith)
    _ = (t : ℝ) - s := clockModified_increment_second C hmodC s t hst

/-- The clock-averaged *conditional* quartic expectation over any finite
ordered interval family is bounded by three times its total physical length.
No assertion about convergence as the mesh shrinks is made. -/
theorem averaged_conditional_quarticSum_le
    (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (hmodC : ∀ r, C r =ᵐ[gaussianProduct] process r)
    (I : Finset (ℝ≥0 × ℝ≥0))
    (hI : ∀ p ∈ I, p.1 ≤ p.2) :
    (∫ ωY, ∫ ωX, quarticSum S C hS hC I ωX ωY
      ∂gaussianProduct ∂gaussianProduct) ≤
      3 * ∑ p ∈ I, ((p.2 : ℝ) - p.1) := by
  classical
  have hpoint (ωY : SampleSpace) :
      (∫ ωX, quarticSum S C hS hC I ωX ωY ∂gaussianProduct) =
        ∑ p ∈ I, 3 * (|C p.2 ωY| - |C p.1 ωY|)^2 := by
    exact conditional_quarticSum_expectation S C hS hC hmodS I ωY
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · calc
      (∑ p ∈ I, ∫ ωY, 3 * (|C p.2 ωY| - |C p.1 ωY|)^2
        ∂gaussianProduct) ≤
          ∑ p ∈ I, 3 * ((p.2 : ℝ) - p.1) := by
            apply Finset.sum_le_sum
            intro p hp
            rw [integral_const_mul]
            have h := clock_reflected_increment_second_le C hmodC p.1 p.2 (hI p hp)
            linarith
      _ = 3 * ∑ p ∈ I, ((p.2 : ℝ) - p.1) := by
        rw [Finset.mul_sum]
  · intro p hp
    exact (clock_reflected_increment_integrable C hmodC p.1 p.2).const_mul 3
end OperatorDerivativeRewrite.Foundation.IBMClockQuarticBound
