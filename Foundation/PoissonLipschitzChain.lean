import Foundation.PoissonMultiplierAlgebra

/-! Genuine finite-difference chain rule for Lipschitz scalar maps on the
maximal one-site Poisson domain. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.PoissonLipschitzChain
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonWeightedDomains PoissonCoordinateEvaluation

/-- A globally Lipschitz map fixing zero sends a scalar Poisson L² class to L². -/
theorem composition_memLp (rate : ℝ≥0) (f : ScalarL2 rate)
    (φ : ℝ → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ) (hzero : φ 0 = 0) :
    MemLp (fun n => φ (f n)) 2 (poissonLaw rate) := by
  exact hφ.comp_memLp hzero (Lp.memLp f)

/-- The actual scalar L² class represented by a Lipschitz composition. -/
def composition (rate : ℝ≥0) (f : ScalarL2 rate)
    (φ : ℝ → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ) (hzero : φ 0 = 0) :
    ScalarL2 rate :=
  (composition_memLp rate f φ K hφ hzero).toLp (fun n => φ (f n))

theorem composition_apply (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (φ : ℝ → ℝ) (K : ℝ≥0)
    (hφ : LipschitzWith K φ) (hzero : φ 0 = 0) (n : ℕ) :
    (composition rate f φ K hφ hzero) n = φ (f n) :=
  ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp (composition_memLp rate f φ K hφ hzero)) n

/-- The jump difference of the composition is genuinely in the weighted field L². -/
theorem composition_difference_memLp (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (φ : ℝ → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ) (hzero : φ 0 = 0) :
    MemLp (fun n => (composition rate f φ K hφ hzero) (n + 1) -
      (composition rate f φ K hφ hzero) n) 2
      ((rate : ℝ≥0∞) • poissonLaw rate) := by
  have hdf := (maximalDifference rate hr).mem_graph ⟨f, hf⟩
  rw [maximalDifference_graph] at hdf
  apply (Lp.memLp ((maximalDifference rate hr) ⟨f, hf⟩)).of_le_mul (c := (K : ℝ))
    (by fun_prop)
  filter_upwards [] with n
  rw [composition_apply rate hr, composition_apply rate hr]
  simpa only [Real.norm_eq_abs, hdf n] using
    hφ.norm_sub_le (f (n + 1)) (f n)

/-- A Lipschitz map fixing zero preserves the maximal Poisson difference domain. -/
theorem composition_mem_domain (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (φ : ℝ → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ) (hzero : φ 0 = 0) :
    composition rate f φ K hφ hzero ∈ (maximalDifference rate hr).domain :=
  (mem_maximalDifference_domain_iff_memLp_difference rate hr _).mpr
    (composition_difference_memLp rate hr f hf φ K hφ hzero)

/-- The actual maximal derivative obeys the exact jump chain formula. -/
theorem composition_difference_apply (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (φ : ℝ → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ) (hzero : φ 0 = 0)
    (n : ℕ) :
    ((maximalDifference rate hr)
      ⟨composition rate f φ K hφ hzero,
        composition_mem_domain rate hr f hf φ K hφ hzero⟩) n =
      φ (f n + ((maximalDifference rate hr) ⟨f, hf⟩) n) - φ (f n) := by
  have hcomp := (maximalDifference rate hr).mem_graph
    ⟨composition rate f φ K hφ hzero,
      composition_mem_domain rate hr f hf φ K hφ hzero⟩
  have hdf := (maximalDifference rate hr).mem_graph ⟨f, hf⟩
  rw [maximalDifference_graph] at hcomp hdf
  rw [hcomp n, composition_apply rate hr, composition_apply rate hr, hdf n]
  congr 1
  abel

/-- The Lipschitz constant controls the actual weighted L² derivative. -/
theorem composition_difference_norm_le (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (φ : ℝ → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ) (hzero : φ 0 = 0) :
    ‖(maximalDifference rate hr)
      ⟨composition rate f φ K hφ hzero,
        composition_mem_domain rate hr f hf φ K hφ hzero⟩‖ ≤
      (K : ℝ) * ‖(maximalDifference rate hr) ⟨f, hf⟩‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [] with n
  rw [composition_difference_apply rate hr f hf φ K hφ hzero n]
  have hdf := (maximalDifference rate hr).mem_graph ⟨f, hf⟩
  rw [maximalDifference_graph] at hdf
  rw [hdf n]
  have hs : f n + (f (n + 1) - f n) = f (n + 1) := by ring
  rw [hs]
  simpa only [Real.norm_eq_abs] using hφ.norm_sub_le (f (n + 1)) (f n)
end OperatorDerivativeRewrite.Foundation.PoissonLipschitzChain







