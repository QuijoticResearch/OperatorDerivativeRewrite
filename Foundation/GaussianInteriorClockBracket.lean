import Foundation.GaussianFutureTerminalBracket
import Foundation.IBMHigherScalarProjection
import Mathlib.Algebra.Order.Floor.Semifield

/-! Centered clock increments after an observed time have zero conditional
projection. A finite cut identifies the unique possible crossing cell. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianInteriorClockBracket
open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence GaussianTimeFieldNorm
open GaussianTimeSpaceHermite GaussianTimeHilbert SeparableHilbertEmbedding
open GaussianTerminalBracketPrediction GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianBrownianQuadraticVariation
attribute [local instance] timeHilbert_secondCountable

theorem past_conditional_square (s t R : ℝ≥0) (hst : s ≤ t) (hRs : R ≤ s) :
    conditionalProjection (observation s R) (wick (incrementDirection s t) 2) = 0 := by
  have hc (i : Option (Iic s)) : inner ℝ (incrementDirection s t) (observation s R i) =
      inner ℝ (0:CoefficientSpace) (observation s R i) := by
    rw [inner_zero_left]
    cases i with
    | none =>
      exact (real_inner_comm _ _).trans (pastDirection_inner_increment R s t hRs hst)
    | some r =>
      exact (real_inner_comm _ _).trans (pastDirection_inner_increment r.val s t r.property hst)
  rw [conditional_wick_eq_of_covariances (observation s R) _ 0 hc 2,
    IBMHigherScalarProjection.wick_zero_positive 2 (by norm_num),map_zero]

theorem past_generated_pairing_zero (s t R : ℝ≥0) (hst : s ≤ t) (hRs : R ≤ s)
    (a : GaussianL2) (ha : a ∈ generated (observation s R)) :
    inner ℝ (wick (incrementDirection s t) 2 : GaussianL2) a = 0 := by
  have hp := (generated (observation s R)).starProjection_inner_eq_zero
    (wick (incrementDirection s t) 2 : GaussianL2) a ha
  rw [inner_sub_left] at hp
  change inner ℝ (wick (incrementDirection s t) 2 : GaussianL2) a-
    inner ℝ (conditionalProjection (observation s R) (wick (incrementDirection s t) 2)) a=0 at hp
  simpa only [past_conditional_square s t R hst hRs,inner_zero_left,sub_zero] using hp

def cut (H R : ℝ≥0) (N : ℕ) : ℕ := min (N+1) ⌊(R:ℝ)*(N+1)/H⌋₊

theorem cut_le (H R : ℝ≥0) (N : ℕ) : cut H R N ≤ N+1 := Nat.min_le_left _ _

theorem cut_position (H R : ℝ≥0) (hH : 0 < H) (N : ℕ) :
    (H:ℝ)*(cut H R N)/(N+1) ≤ R ∧
      (cut H R N < N+1 → (R:ℝ) < (H:ℝ)*((cut H R N)+1)/(N+1)) := by
  have hp : (0:ℝ) < H := hH
  have hn : (0:ℝ) < N+1 := by positivity
  have hc : (cut H R N:ℝ) ≤ (R:ℝ)*(N+1)/H :=
    (show (cut H R N:ℝ) ≤ (⌊(R:ℝ)*(N+1)/H⌋₊:ℝ) by
      exact_mod_cast (show cut H R N ≤ ⌊(R:ℝ)*(N+1)/H⌋₊ from Nat.min_le_right _ _)).trans
        (Nat.floor_le (by positivity))
  have he : (H:ℝ)*((R:ℝ)*(N+1)/H) = (R:ℝ)*(N+1) := by
    field_simp
    <;> ring
  constructor
  · rw [div_le_iff₀ hn]
    calc
      _ ≤ (H:ℝ)*((R:ℝ)*(N+1)/H) := mul_le_mul_of_nonneg_left hc hp.le
      _ = _ := he
  · intro hcut
    have hf : cut H R N = ⌊(R:ℝ)*(N+1)/H⌋₊ := by
      unfold cut at hcut ⊢
      exact min_eq_right (by omega)
    have hf' := Nat.lt_floor_add_one ((R:ℝ)*(N+1)/H)
    rw [← hf] at hf'
    have hm := mul_lt_mul_of_pos_left hf' hp
    rw [he] at hm
    rw [lt_div_iff₀ hn]
    exact hm

theorem early_right_le (H R : ℝ≥0) (hH : 0 < H) (N : ℕ) (i : Fin (N+1))
    (hi : i.val < cut H R N) : uniformTime H N i.succ ≤ R := by
  apply NNReal.coe_le_coe.mp
  have hp := (cut_position H R hH N).1
  simp only [uniformTime,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,Fin.val_succ,
    Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one]
  apply le_trans _ hp
  gcongr
  exact_mod_cast Nat.succ_le_of_lt hi

theorem early_gap (H R : ℝ≥0) (hH : 0 < H) (N : ℕ) (i : Fin (N+1))
    (hi : i.val < cut H R N) :
    ((H:ℝ)/(N+1))*((cut H R N-i.val:ℕ):ℝ) ≤ (R:ℝ)-uniformTime H N i.castSucc := by
  have hp := (cut_position H R hH N).1
  simp only [uniformTime,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,Fin.val_castSucc,
    Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one,Nat.cast_sub (Nat.le_of_lt hi)]
  have he : ((H:ℝ)/(N+1))*((cut H R N:ℝ)-i.val) =
      (H:ℝ)*(cut H R N)/(N+1)-(H:ℝ)*i.val/(N+1) := by ring
  rw [he]
  linarith

theorem late_left_ge (H R : ℝ≥0) (hH : 0 < H) (N : ℕ) (i : Fin (N+1))
    (hi : cut H R N < i.val) : R ≤ uniformTime H N i.castSucc := by
  apply NNReal.coe_le_coe.mp
  have hp := (cut_position H R hH N).2 (hi.trans i.isLt)
  simp only [uniformTime,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,Fin.val_castSucc,
    Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one]
  apply hp.le.trans
  gcongr
  exact_mod_cast Nat.succ_le_of_lt hi

end OperatorDerivativeRewrite.Foundation.GaussianInteriorClockBracket
