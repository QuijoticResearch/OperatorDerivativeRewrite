import Foundation.HigherHeatFourierSeries
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! A genuine compactly supported Schwartz square has negative higher-heat expectation. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal SchwartzMap ContDiff BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzSquare
open HigherHeatSignedLaws HigherHeatKernelMoments

theorem negative_schwartz_square (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) :
    ∃ f : 𝓢(ℝ,ℝ), HasCompactSupport (f : ℝ → ℝ) ∧
      (∫ x : ℝ, realKernel m (by omega) T hT x*(f x)^2) < 0 := by
  let K := realKernel m (by omega : 0 < m) T hT
  obtain ⟨x,hx⟩ := exists_negative m hm T hT
  have hn : {y : ℝ | K y < 0} ∈ 𝓝 x :=
    (isOpen_lt K.continuous continuous_const).mem_nhds hx
  obtain ⟨f,hsub,hcomp,hsmooth,hrange,hfx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hn
  let g : ℝ → ℝ := fun y => -K y*(f y*f y)
  have hgcont : Continuous g := K.continuous.neg.mul (hsmooth.continuous.mul hsmooth.continuous)
  have hgcomp : HasCompactSupport g := (hcomp.mul_right (f' := f)).mul_left
  have hgnonneg : 0 ≤ g := by
    intro y
    change 0 ≤ -K y*(f y*f y)
    by_cases hy : f y=0
    · simp [hy]
    · have hk : K y < 0 := hsub (subset_tsupport f (Function.mem_support.mpr hy))
      exact mul_nonneg (neg_nonneg.mpr hk.le) (mul_self_nonneg _)
  have hgx : g x ≠ 0 := by
    dsimp only [g]
    rw [hfx,one_mul,mul_one]
    exact ne_of_gt (neg_pos.mpr hx)
  have hp : 0 < ∫ y, g y :=
    hgcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hgcomp hgnonneg hgx
  refine ⟨hcomp.toSchwartzMap hsmooth,hcomp,?_⟩
  change (∫ y, K y*(f y)^2) < 0
  have he : g=(fun y => -(K y*(f y)^2)) := by
    funext y
    dsimp [g]
    ring
  rw [he,integral_neg] at hp
  linarith

open HigherHeatNegativeProbe HigherHeatCylindricalExpectation HigherHeatContinuousCylinders
open HigherHeatPathCylinderAlgebra

theorem actual_negative_square (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) :
    ∃ G : cylinderAlgebra, algebraExpectation m (by omega) T hT (G*G) < 0 := by
  obtain ⟨f,hcomp,hf⟩ := negative_schwartz_square m hm T hT
  let G := representCylinder (cylinderOf 0 (terminalTest f.toBoundedContinuousFunction))
  refine ⟨G,?_⟩
  have he : G*G=representCylinder (cylinderOf 0 (terminalTest
      (f.toBoundedContinuousFunction*f.toBoundedContinuousFunction))) := by
    ext w
    rfl
  rw [he,algebraExpectation_represent,cylindricalExpectation_apply,terminal_expectation]
  simpa only [BoundedContinuousFunction.mul_apply,SchwartzMap.toBoundedContinuousFunction_apply,
    pow_two] using hf

end OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzSquare
