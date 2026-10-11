import Foundation.GaussianSobolevSmoothApprox
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! Smooth Lebesgue L² approximation with a fixed enlarged support. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianSobolevFixedSupport

/-- A compactly supported L² function can be approximated smoothly without
allowing the approximants' supports to escape a fixed interval. -/
theorem exists_fixed_support_smooth_approx {h : ℝ → ℝ} (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support h ⊆ Icc (-R) R)
    (hh : MemLp h 2 (volume : Measure ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      Function.support v ⊆ Icc (-(R + 2)) (R + 2) ∧
      eLpNorm (h - v) 2 (volume : Measure ℝ) ≤ ENNReal.ofReal ε := by
  let B : ContDiffBump (0 : ℝ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  obtain ⟨g, hgcomp, hgsmooth, hgerror⟩ := hh.exist_eLpNorm_sub_le
    (by norm_num : (2 : ENNReal) ≠ ⊤) (by norm_num : (1 : ENNReal) ≤ 2) hε
  let v : ℝ → ℝ := fun x => B x * g x
  refine ⟨v, ?_, ?_, ?_⟩
  · exact B.contDiff.mul hgsmooth
  · intro x hx
    have hBx : B x ≠ 0 := by
      have hv : v x ≠ 0 := hx
      exact (mul_ne_zero_iff.mp hv).1
    have hball : x ∈ Metric.ball (0 : ℝ) (R + 2) := by
      rw [← B.support_eq]
      exact hBx
    have habs : |x| < R + 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hball
    exact abs_le.mp habs.le
  · have hBh (x : ℝ) : h x = B x * h x := by
      by_cases hx : x ∈ Function.support h
      · have hI := hs hx
        have habs : |x| ≤ R := abs_le.mpr hI
        have hball : x ∈ Metric.closedBall (0 : ℝ) (R + 1) := by
          simpa [Metric.mem_closedBall, Real.dist_eq] using (show |x| ≤ R + 1 by linarith)
        rw [B.one_of_mem_closedBall hball]
        ring
      · have hz : h x = 0 := by simpa [Function.support] using hx
        simp [hz]
    have hrewrite : (h - v) = fun x => B x * (h x - g x) := by
      funext x
      simp only [Pi.sub_apply, v]
      conv_lhs => rw [hBh x]
      ring
    rw [hrewrite]
    have hmeas : AEStronglyMeasurable (fun x => B x * (h x - g x))
        (volume : Measure ℝ) := by
      exact (B.continuous.measurable.aestronglyMeasurable.mul
        (hh.aestronglyMeasurable.sub hgsmooth.continuous.measurable.aestronglyMeasurable))
    have hle : eLpNorm (fun x => B x * (h x - g x)) 2 (volume : Measure ℝ) ≤
        eLpNorm (h - g) 2 (volume : Measure ℝ) := by
      apply eLpNorm_mono_ae hmeas
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      have hB0 := B.nonneg' x
      have hB1 : B x ≤ 1 := B.le_one
      rw [abs_of_nonneg hB0]
      exact mul_le_of_le_one_left (abs_nonneg _) hB1
    exact hle.trans hgerror



/-- A smooth unit-integral correction bump supported in the same fixed interval. -/
theorem exists_unit_integral_bump (R : ℝ) (hR : 0 ≤ R) :
    ∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧
      Function.support q ⊆ Icc (-(R + 2)) (R + 2) ∧
      (∫ x, q x ∂(volume : Measure ℝ)) = 1 := by
  let B : ContDiffBump (0 : ℝ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  refine ⟨B.normed (volume : Measure ℝ), B.contDiff_normed, ?_, B.integral_normed⟩
  intro x hx
  have hball : x ∈ Metric.ball (0 : ℝ) (R + 2) := by
    rw [← (B.support_normed_eq (μ := (volume : Measure ℝ)))]
    exact hx
  have habs : |x| < R + 2 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hball
  exact abs_le.mp habs.le



def corrected (v q : ℝ → ℝ) (x : ℝ) : ℝ :=
  v x - (∫ y, v y ∂(volume : Measure ℝ)) * q x

/-- Subtracting the unit-integral bump imposes zero mean while retaining
smoothness and the same fixed compact support. -/
theorem corrected_properties (R : ℝ) {v q : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q)
    (hvs : Function.support v ⊆ Icc (-(R + 2)) (R + 2))
    (hqs : Function.support q ⊆ Icc (-(R + 2)) (R + 2))
    (hqint : (∫ x, q x ∂(volume : Measure ℝ)) = 1) :
    ContDiff ℝ ∞ (corrected v q) ∧
    Function.support (corrected v q) ⊆ Icc (-(R + 2)) (R + 2) ∧
    (∫ x, corrected v q x ∂(volume : Measure ℝ)) = 0 := by
  have hvc : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hvs
  have hqc : HasCompactSupport q :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hqs
  have hvi : Integrable v (volume : Measure ℝ) :=
    hv.continuous.integrable_of_hasCompactSupport hvc
  have hqi : Integrable q (volume : Measure ℝ) :=
    hq.continuous.integrable_of_hasCompactSupport hqc
  refine ⟨?_, ?_, ?_⟩
  · exact hv.sub (contDiff_const.mul hq)
  · intro x hx
    by_contra hxK
    have hv0 : v x = 0 := by
      by_contra hn
      exact hxK (hvs hn)
    have hq0 : q x = 0 := by
      by_contra hn
      exact hxK (hqs hn)
    have hw0 : corrected v q x = 0 := by simp [corrected, hv0, hq0]
    exact hx hw0
  · change (∫ x, v x - (∫ y, v y ∂(volume : Measure ℝ)) * q x ∂volume) = 0
    rw [integral_sub hvi (hqi.const_mul _), integral_const_mul, hqint]
    ring

end OperatorDerivativeRewrite.Foundation.GaussianSobolevFixedSupport
