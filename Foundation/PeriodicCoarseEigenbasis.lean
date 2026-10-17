import Foundation.PeriodicCoarseGramAction

/-! A complete eigenbasis of the actual periodic coarse curl Gram operator. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseEigenbasis
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarseClosedReconstruction PeriodicCoarseGramAction
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def eigenvalue (a : Label) : ℕ :=
  if a.1 = ∅ ∨ (a.2 ∈ a.1 ∧ a.2 = pivot a.1) then 0 else 4*a.1.card

def eigenMode (a : Label) : Field :=
  if a.1 = ∅ ∨ a.2 ∉ a.1 then mode a
  else if a.2 = pivot a.1 then ∑ j ∈ a.1, mode (a.1,j)
  else mode a - mode (a.1,pivot a.1)

def intEigenMode (a : Label) (e : CoarseEdge) : ℤ :=
  if a.1 = ∅ ∨ a.2 ∉ a.1 then modeZ a e
  else if a.2 = pivot a.1 then ∑ j ∈ a.1, modeZ (a.1,j) e
  else modeZ a e - modeZ (a.1,pivot a.1) e

def intDual (a : Label) (e : CoarseEdge) : ℤ :=
  if a.1 = ∅ ∨ a.2 ∉ a.1 then modeZ a e
  else if a.2 = pivot a.1 then ∑ j ∈ a.1, modeZ (a.1,j) e
  else (a.1.card : ℤ)*modeZ a e - ∑ j ∈ a.1, modeZ (a.1,j) e

def dual (a : Label) (e : CoarseEdge) : ℝ := (intDual a e : ℝ)
def normalization (a : Label) : ℕ := if a.1 = ∅ ∨ a.2 ∉ a.1 then 16 else 16*a.1.card

theorem normalization_pos (a : Label) : 0 < normalization a := by
  by_cases h : a.1 = ∅ ∨ a.2 ∉ a.1
  · simp [normalization, h]
  · have hi : a.2 ∈ a.1 := not_not.mp (not_or.mp h).2
    have hc := Finset.card_pos.mpr ⟨a.2,hi⟩
    simp only [normalization, if_neg h]
    omega

theorem eigenMode_int (a : Label) (e : CoarseEdge) : eigenMode a e = (intEigenMode a e : ℝ) := by
  by_cases h : a.1 = ∅ ∨ a.2 ∉ a.1
  · rw [eigenMode, if_pos h, intEigenMode, if_pos h]
    rfl
  · rw [eigenMode, if_neg h, intEigenMode, if_neg h]
    by_cases hp : a.2 = pivot a.1
    · rw [if_pos hp, if_pos hp]
      simp only [Finset.sum_apply, mode, Int.cast_sum]
    · rw [if_neg hp, if_neg hp]
      simp only [Pi.sub_apply, mode, Int.cast_sub]

set_option maxHeartbeats 768000000 in
-- Integer dual pairings certify all64 transformed edge fields without external arithmetic.
theorem int_dual_pair : ∀ a b : Label,
    (∑ e : CoarseEdge, intEigenMode a e * intDual b e) =
      if a = b then (normalization a : ℤ) else 0 := by decide

theorem eigenMode_dual_pair (a b : Label) :
    dotProduct (eigenMode a) (dual b) = if a = b then (normalization a : ℝ) else 0 := by
  unfold dotProduct dual
  simp_rw [eigenMode_int]
  exact_mod_cast int_dual_pair a b

theorem eigenMode_linearIndependent : LinearIndependent ℝ eigenMode := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc a
  have h := congrArg (fun f => dotProduct f (dual a)) hc
  rw [sum_dotProduct] at h
  simp only [smul_dotProduct, eigenMode_dual_pair, smul_eq_mul, zero_dotProduct,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  have hp : 0 < (normalization a : ℝ) := by exact_mod_cast normalization_pos a
  exact (mul_eq_zero.mp h).resolve_right hp.ne'

def eigenBasis : Module.Basis Label ℝ Field :=
  basisOfLinearIndependentOfCardEqFinrank' _ eigenMode_linearIndependent (by
    rw [label_card, Module.finrank_fintype_fun_eq_card, edge_card])

theorem eigenBasis_apply (a : Label) : eigenBasis a = eigenMode a := by
  rw [eigenBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

theorem mode_eigen (a : Label) : H (eigenMode a) = (eigenvalue a : ℝ) • eigenMode a := by
  by_cases hT : a.1 = ∅
  · simp [eigenMode, eigenvalue, hT, H_mode]
  · by_cases hi : a.2 ∈ a.1
    · by_cases hp : a.2 = pivot a.1
      · have hn : ¬ (a.1 = ∅ ∨ a.2 ∉ a.1) := by simp only [hT, hi, not_true_eq_false, or_self, not_false_eq_true]
        have hz : a.1 = ∅ ∨ (a.2 ∈ a.1 ∧ a.2 = pivot a.1) := Or.inr ⟨hi,hp⟩
        simp only [eigenMode, if_neg hn, if_pos hp, eigenvalue,
          if_pos hz, Nat.cast_zero, zero_smul, H_sector_sum]
      · have hn : a.1.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
        have hm := pivot_mem a.1 hn
        simp only [eigenMode, eigenvalue, hT, hi, hp, not_true_eq_false,
          or_self, ite_false, and_false, or_false]
        rw [map_sub, H_mode, H_mode, if_pos hi, if_pos hm]
        funext e
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
        ring
    · simp [eigenMode, eigenvalue, hT, hi, H_mode]

theorem eigenvalue_counts :
    Fintype.card {a : Label // eigenvalue a = 0} = 19 ∧
    Fintype.card {a : Label // eigenvalue a = 4} = 12 ∧
    Fintype.card {a : Label // eigenvalue a = 8} = 18 ∧
    Fintype.card {a : Label // eigenvalue a = 12} = 12 ∧
    Fintype.card {a : Label // eigenvalue a = 16} = 3 := by decide

theorem eigenvalue_mem : ∀ a : Label,
    eigenvalue a = 0 ∨ eigenvalue a = 4 ∨ eigenvalue a = 8 ∨
      eigenvalue a = 12 ∨ eigenvalue a = 16 := by decide

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseEigenbasis
