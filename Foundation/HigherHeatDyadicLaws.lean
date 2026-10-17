import Foundation.HigherHeatGridDoubling
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.VectorMeasure.Integral

/-! Actual consistent signed laws and bounded-observable expectations on dyadic grids. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatDyadicLaws
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatObservationRefinement
open HigherHeatGridDoubling

def gridSize : ℕ → ℕ | 0 => 1 | n+1 => 2*gridSize n

theorem gridSize_pos (n : ℕ) : 0 < gridSize n := by
  induction n with
  | zero => norm_num [gridSize]
  | succ n ih => simpa only [gridSize] using mul_pos (by norm_num : 0 < (2 : ℕ)) ih

theorem gridSize_pow (n : ℕ) : gridSize n=2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gridSize,ih,pow_succ,mul_comm]

abbrev Grid (n : ℕ) := Fin (gridSize n) → ℝ
abbrev Test (n : ℕ) := Grid n →ᵇ ℝ

def duration (T : ℝ≥0) (n : ℕ) : ℝ≥0 := T/(gridSize n : ℝ≥0)

theorem duration_pos (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : 0 < duration T n := by
  apply div_pos hT
  exact_mod_cast gridSize_pos n

theorem duration_halves (T : ℝ≥0) (n : ℕ) : duration T (n+1)+duration T (n+1)=duration T n := by
  unfold duration
  simp only [gridSize,Nat.cast_mul,Nat.cast_ofNat]
  field_simp <;> ring

def law (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : SignedMeasure (Grid n) :=
  positionLaw (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n)

instance law_variation_finite (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    IsFiniteMeasure (law m hm T hT n).variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]
  infer_instance

theorem law_mass (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    law m hm T hT n Set.univ=1 := positionLaw_mass _ _ _ _ _

def restriction (n : ℕ) : Grid (n+1) → Grid n := oldPositions

theorem restriction_continuous (n : ℕ) : Continuous (restriction n) := by
  apply continuous_pi
  intro i
  exact continuous_apply (oddIndex i)

set_option backward.isDefEq.respectTransparency false in
theorem law_consistent (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (law m hm T hT (n+1)).map (restriction n)=law m hm T hT n := by
  have h := position_doubling (gridSize n) m hm (duration T (n+1)) (duration_pos T hT (n+1))
  simpa only [law,Grid,gridSize,restriction,duration_halves] using h

def pullback (n : ℕ) : Test n →L[ℝ] Test (n+1) :=
  BoundedContinuousFunction.compContinuousCLM ℝ ℝ ⟨restriction n,restriction_continuous n⟩

theorem pullback_apply (n : ℕ) (f : Test n) (x : Grid (n+1)) :
    pullback n f x=f (restriction n x) := rfl

theorem test_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (f : Test n) :
    (law m hm T hT n).Integrable f :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)

def expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : Test n →ₗ[ℝ] ℝ where
  toFun f := ∫ᵛ x, f x ∂•law m hm T hT n
  map_add' f g := by
    change (∫ᵛ x, f x+g x ∂•law m hm T hT n) = _
    exact VectorMeasure.integral_fun_add (test_integrable m hm T hT n f) (test_integrable m hm T hT n g)
  map_smul' c f := by
    change (∫ᵛ x, c • f x ∂•law m hm T hT n) = _
    exact VectorMeasure.integral_fun_smul _ _ _ _

theorem expectation_one (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    expectation m hm T hT n (1 : Test n)=1 := by
  change (∫ᵛ _ : Grid n, (1 : ℝ) ∂•law m hm T hT n)=1
  rw [VectorMeasure.integral_const,law_mass]
  simp

theorem expectation_compatible (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (f : Test n) :
    expectation m hm T hT (n+1) (pullback n f)=expectation m hm T hT n f := by
  have hi := test_integrable m hm T hT (n+1) (pullback n f)
  change (∫ᵛ x, f (restriction n x) ∂•law m hm T hT (n+1)) =
    ∫ᵛ x, f x ∂•law m hm T hT n
  conv_rhs => rw [← law_consistent m hm T hT n]
  exact (VectorMeasure.integral_map (restriction_continuous n).measurable
    f.continuous.aestronglyMeasurable hi).symm

def time (T : ℝ≥0) (n : ℕ) (i : Fin (gridSize n)) : ℝ≥0 := (i.val+1 : ℕ)*duration T n

theorem time_positive (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (i : Fin (gridSize n)) : 0 < time T n i := by
  apply mul_pos _ (duration_pos T hT n)
  exact_mod_cast Nat.succ_pos i.val

theorem time_in_horizon (T : ℝ≥0) (n : ℕ) (i : Fin (gridSize n)) : time T n i ≤ T := by
  have hN : (gridSize n : ℝ≥0) ≠ 0 := by exact_mod_cast (gridSize_pos n).ne'
  calc
    time T n i ≤ (gridSize n : ℝ≥0)*duration T n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    _ = T := by unfold duration; field_simp

theorem time_restriction (T : ℝ≥0) (n : ℕ) (i : Fin (gridSize n)) :
    time T (n+1) (oddIndex i)=time T n i := by
  simp only [time,oddIndex,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  rw [← duration_halves T n]
  ring

theorem restriction_surjective (n : ℕ) : Function.Surjective (restriction n) := by
  intro x
  refine ⟨fun j => x (@pairBlock (gridSize n) j),?_⟩
  funext i
  change x (pairBlock (oddIndex i))=x i
  congr 1
  apply Fin.ext
  dsimp [pairBlock,oddIndex]
  omega

theorem pullback_injective (n : ℕ) : Function.Injective (pullback n) := by
  intro f g h
  ext x
  obtain ⟨y,hy⟩ := restriction_surjective n x
  have hv := congrArg (fun F : Test (n+1) => F y) h
  change f (restriction n y)=g (restriction n y) at hv
  rwa [hy] at hv

end OperatorDerivativeRewrite.Foundation.HigherHeatDyadicLaws
