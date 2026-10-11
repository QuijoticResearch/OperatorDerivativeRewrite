import Foundation.GaussianSobolevFixedSupport
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Smooth compactly supported primitives of zero-mean Lebesgue functions. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianSobolevFixedSupport

theorem integrable_of_memLp_two_support {h : ℝ → ℝ} {A B : ℝ}
    (hs : Function.support h ⊆ Icc A B)
    (hh : MemLp h 2 (volume : Measure ℝ)) :
    Integrable h (volume : Measure ℝ) := by
  have hzero : ∀ x, x ∉ Icc A B → h x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hs hn)
  have hfin : (volume : Measure ℝ) (Icc A B) ≠ (⊤ : ENNReal) := by simp
  exact memLp_one_iff_integrable.mp
    (hh.mono_exponent_of_measure_support_ne_top hzero hfin
      (by norm_num : (1 : ENNReal) ≤ 2))

theorem correction_integrable {h v q : ℝ → ℝ} {A B : ℝ}
    (hh : MemLp h 2 (volume : Measure ℝ))
    (hhs : Function.support h ⊆ Icc A B)
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q)
    (hvs : Function.support v ⊆ Icc A B)
    (hqs : Function.support q ⊆ Icc A B) :
    Integrable h (volume : Measure ℝ) ∧
    Integrable v (volume : Measure ℝ) ∧
    Integrable (v - h) (volume : Measure ℝ) ∧
    Integrable (corrected v q) (volume : Measure ℝ) := by
  have hhi := integrable_of_memLp_two_support hhs hh
  have hvi : Integrable v (volume : Measure ℝ) :=
    hv.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hvs)
  have hqi : Integrable q (volume : Measure ℝ) :=
    hq.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hqs)
  exact ⟨hhi, hvi, hvi.sub hhi, hvi.sub (hqi.const_mul _)⟩

def primitive (a : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in a..x, w y

theorem primitive_hasDerivAt {w : ℝ → ℝ} (hw : Continuous w) (a x : ℝ) :
    HasDerivAt (primitive a w) (w x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (hw.intervalIntegrable a x)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt

theorem deriv_primitive {w : ℝ → ℝ} (hw : Continuous w) (a x : ℝ) :
    deriv (primitive a w) x = w x := (primitive_hasDerivAt hw a x).deriv

theorem primitive_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (a : ℝ) :
    ContDiff ℝ ∞ (primitive a w) := by
  rw [← contDiffOn_univ, contDiffOn_infty_iff_deriv_of_isOpen isOpen_univ]
  constructor
  · exact fun x _ =>
      (primitive_hasDerivAt hw.continuous a x).differentiableAt.differentiableWithinAt
  · have heq : deriv (primitive a w) = w := funext (deriv_primitive hw.continuous a)
    simpa only [heq, contDiffOn_univ] using hw

theorem primitive_zero_left {w : ℝ → ℝ} {A B a x : ℝ}
    (ha : a < A) (hx : x ≤ A)
    (hs : Function.support w ⊆ Icc A B) : primitive a w x = 0 := by
  unfold primitive
  rw [← intervalIntegral.integral_zero]
  apply intervalIntegral.integral_congr_uIoo
  intro y hy
  have hyA : y < A := by
    rcases le_total a x with hax | hxa
    · have hy' : y ∈ Ioo a x := by simpa [uIoo, min_eq_left hax, max_eq_right hax] using hy
      exact lt_of_lt_of_le hy'.2 hx
    · have hy' : y ∈ Ioo x a := by simpa [uIoo, min_eq_right hxa, max_eq_left hxa] using hy
      exact lt_trans hy'.2 ha
  have hw0 : w y = 0 := by
    by_contra hn
    exact (not_lt.mpr (hs hn).1) hyA
  exact hw0

theorem primitive_zero_right {w : ℝ → ℝ} {A B a x : ℝ}
    (ha : a < A) (hx : B ≤ x) (hs : Function.support w ⊆ Icc A B)
    (hzero : (∫ y, w y ∂(volume : Measure ℝ)) = 0) : primitive a w x = 0 := by
  unfold primitive
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · exact hzero
  · intro y hy
    have hyK := hs hy
    exact ⟨lt_of_lt_of_le ha hyK.1, le_trans hyK.2 hx⟩

theorem primitive_hasCompactSupport {w : ℝ → ℝ} {A B a : ℝ}
    (ha : a < A) (hs : Function.support w ⊆ Icc A B)
    (hzero : (∫ y, w y ∂(volume : Measure ℝ)) = 0) :
    HasCompactSupport (primitive a w) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Icc A B) isCompact_Icc ?_
  intro x hx
  constructor
  · by_contra h
    exact hx (primitive_zero_left ha (le_of_lt (lt_of_not_ge h)) hs)
  · by_contra h
    exact hx (primitive_zero_right ha (le_of_lt (lt_of_not_ge h)) hs hzero)

/-- The zero-mean correction has a genuine smooth, compactly supported primitive. -/
theorem corrected_primitive_properties (R : ℝ) {v q : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q)
    (hvs : Function.support v ⊆ Icc (-(R + 2)) (R + 2))
    (hqs : Function.support q ⊆ Icc (-(R + 2)) (R + 2))
    (hqint : (∫ x, q x ∂(volume : Measure ℝ)) = 1) :
    let w := corrected v q
    let F := primitive (-(R + 3)) w
    ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      (∀ x, deriv F x = w x) ∧
      (∀ x, x ≤ -(R + 2) → F x = 0) ∧
      (∀ x, R + 2 ≤ x → F x = 0) := by
  dsimp
  obtain ⟨hwsmooth, hwsupport, hwzero⟩ := corrected_properties R hv hq hvs hqs hqint
  refine ⟨primitive_contDiff hwsmooth _, ?_, ?_, ?_, ?_⟩
  · exact primitive_hasCompactSupport (a := -(R + 3)) (by linarith) hwsupport hwzero
  · intro x
    exact deriv_primitive hwsmooth.continuous _ x
  · intro x hx
    exact primitive_zero_left (a := -(R + 3)) (by linarith) hx hwsupport
  · intro x hx
    exact primitive_zero_right (a := -(R + 3)) (by linarith) hx hwsupport hwzero

end OperatorDerivativeRewrite.Foundation.GaussianSobolevFixedSupport
