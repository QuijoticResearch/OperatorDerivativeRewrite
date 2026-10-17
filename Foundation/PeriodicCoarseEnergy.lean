import Foundation.PeriodicCoarseCurl

/-! Exact energy normalization for the actual periodic boundary averaging adjoint. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseEnergy
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def faceEquiv : Face ≃ CoarseFace × Bits where
  toFun p := (⟨(coarseBlock p.val.1, p.val.2), p.property⟩, fineBits p.val.1)
  invFun p := ⟨(fineVertex p.1.val.1 p.2, p.1.val.2), p.1.property⟩
  left_inv p := by
    apply Subtype.ext
    change (fineVertex (coarseBlock p.val.1) (fineBits p.val.1), p.val.2) = p.val
    rw [fineVertex_reconstruct]
  right_inv p := by
    rcases p with ⟨⟨⟨q, i, j⟩, hij⟩, b⟩
    simp [coarseBlock_fineVertex, fineBits_fineVertex]

theorem corner_bit_count : ∀ i j : Direction, i ≠ j →
    ((Finset.univ : Finset Bits).filter (fun b => b i = 1 ∧ b j = 1)).card = 4 := by
  decide

def coarseEnergy (c : CoarseEdge → ℝ) : ℝ := ∑ p : CoarseFace, (coarseIncidence c p)^2

theorem coarseEnergy_nonneg (c : CoarseEdge → ℝ) : 0 ≤ coarseEnergy c :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem normalized_lift_energy (c : CoarseEdge → ℝ) :
    fineEnergy (normalizedLift c) = (1/16 : ℝ) * coarseEnergy c := by
  unfold fineEnergy
  rw [← faceEquiv.symm.sum_comp (fun p => (incidence (normalizedLift c) p)^2)]
  rw [Fintype.sum_prod_type]
  unfold coarseEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hij : q.val.2.1 ≠ q.val.2.2 := ne_of_lt q.property
  have hp (b : Bits) : (incidence (normalizedLift c) (faceEquiv.symm (q,b)))^2 =
      if b q.val.2.1 = 1 ∧ b q.val.2.2 = 1 then
        (1/64 : ℝ) * (coarseIncidence c q)^2 else 0 := by
    change (curl (normalizedLift c) (fineVertex q.val.1 b) q.val.2.1 q.val.2.2)^2 = _
    rw [normalizedLift_curl c _ _ _ hij]
    simp only [oddEdge, fineBits_fineVertex, coarseBlock_fineVertex]
    by_cases h : b q.val.2.1 = 1 ∧ b q.val.2.2 = 1
    · simp only [h, and_self, if_true]
      change ((1/8 : ℝ) * coarseIncidence c q)^2 = _
      ring
    · simp [h]
  simp_rw [hp]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_const_zero, add_zero]
  rw [corner_bit_count _ _ hij]
  ring

theorem minimum_lower (y : Interior → ℝ) (c : CoarseEdge → ℝ) :
    (1/16 : ℝ) * coarseEnergy c ≤ fineEnergy (extend y + normalizedLift c) := by
  rw [← normalized_lift_energy]
  exact interior_minimum_lower y c

theorem minimum_attained (c : CoarseEdge → ℝ) :
    fineEnergy (extend 0 + normalizedLift c) = (1/16 : ℝ) * coarseEnergy c := by
  rw [interior_minimum_attained, normalized_lift_energy]

theorem minimum_not_unique (c : CoarseEdge → ℝ) :
    ∃ y : Interior → ℝ, y ≠ 0 ∧
      fineEnergy (extend y + normalizedLift c) = (1/16 : ℝ) * coarseEnergy c := by
  obtain ⟨y, hy, he⟩ := interior_minimum_not_unique c
  exact ⟨y, hy, he.trans (normalized_lift_energy c)⟩

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseEnergy
