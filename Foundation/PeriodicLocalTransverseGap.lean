import Foundation.PeriodicLocalHodgeExact

/-! Sharp candidate lower bounds on the explicitly defined local gradient-orthogonal sector. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalTransverseGap
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity PeriodicSingleBlockDecomposition
  PeriodicLocalGradientModes PeriodicLocalWalshAction PeriodicLocalSpectralSet PeriodicLocalHodgeExact
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def transverse (f : Field) : Prop := ∀ φ : Vertex → ℝ, dotProduct f (localGradient φ) = 0

def coeff (f : Field) (a : Label) : ℝ := walshBasis.repr f a

theorem walshBasis_dot (a b : Label) : dotProduct (walshBasis a) (walshBasis b) =
    if a=b then (8 : ℝ) else 0 := by
  simp only [walshBasis_apply]
  exact walsh_orthogonality a b

theorem dot_coefficient (f : Field) (a : Label) :
    dotProduct f (walshBasis a) = 8*coeff f a := by
  have h := congrArg (fun v => dotProduct v (walshBasis a)) (walshBasis.sum_repr f)
  rw [sum_dotProduct] at h
  simp only [smul_dotProduct, walshBasis_dot, smul_eq_mul] at h
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  calc
    _ = walshBasis.repr f a * 8 := h.symm
    _ = _ := mul_comm _ _

theorem dot_parseval (f : Field) : dotProduct f f = 8*∑ a : Label, coeff f a ^ 2 := by
  have h := congrArg (fun v => dotProduct f v) (walshBasis.sum_repr f)
  rw [dotProduct_sum] at h
  simp only [dotProduct_smul, smul_eq_mul, dot_coefficient] at h
  calc
    _ = ∑ a : Label, coeff f a * (8*coeff f a) := h.symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem squaredSize_parseval (f : Field) : squaredSize f = 8*∑ a : Label, coeff f a ^ 2 := by
  have hd : dotProduct f f = squaredSize f := by simp [dotProduct, PeriodicSingleBlockCoercivity.squaredSize, pow_two]
  rw [← hd]
  exact dot_parseval f

theorem transverse_sum {f : Field} (hf : transverse f) (T : Finset Direction) :
    dotProduct f (walshSum T) = 0 := by
  obtain ⟨φ, hφ⟩ := walshSum_in_gradient_range T
  have h := hf φ
  rw [hφ] at h
  exact h

theorem singleton_coeff_zero {f : Field} (hf : transverse f) (a : Label)
    (ha : a.val.1.card = 1) : coeff f a = 0 := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp ha
  have hij : a.val.2 = j := by simpa [hj] using a.property
  have hs : walshBasis a = walshSum a.val.1 := by
    simp [walshBasis_apply, walshSum, hj, hij]
  have h := transverse_sum hf a.val.1
  rw [← hs, dot_coefficient] at h
  linarith

theorem H_walshBasis (a : Label) : H (walshBasis a) =
    (3+2*(a.val.1.card : ℝ)) • walshBasis a - (2 : ℝ) • walshSum a.val.1 := by
  rw [walshBasis_apply]
  exact walsh_H a.val.1 a.val.2 a.property

theorem transverse_energy_expansion {f : Field} (hf : transverse f) :
    energy f = 8*∑ a : Label, (3+2*(a.val.1.card : ℝ))*coeff f a ^ 2 := by
  have hv : f = ∑ a : Label, coeff f a • walshBasis a := (walshBasis.sum_repr f).symm
  calc
    energy f = dotProduct f (H f) := (hessian_energy f).symm
    _ = dotProduct f (H (∑ a : Label, coeff f a • walshBasis a)) :=
      congrArg (fun v : Field => dotProduct f (H v)) hv
    _ = ∑ a : Label, coeff f a * ((3+2*(a.val.1.card : ℝ))*(8*coeff f a)) := by
      rw [map_sum, dotProduct_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [map_smul, dotProduct_smul, H_walshBasis, dotProduct_sub,
        dotProduct_smul, dotProduct_smul, transverse_sum hf, dot_coefficient]
      simp [smul_eq_mul]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem transverse_coercive {f : Field} (hf : transverse f) : 7*squaredSize f ≤ energy f := by
  rw [squaredSize_parseval, transverse_energy_expansion hf]
  have hs : (∑ a : Label, 7*coeff f a ^ 2) ≤
      ∑ a : Label, (3+2*(a.val.1.card : ℝ))*coeff f a ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : a.val.1.card = 1
    · rw [singleton_coeff_zero hf a ha]
      norm_num
    · have hp : 0 < a.val.1.card := Finset.card_pos.mpr ⟨a.val.2, a.property⟩
      have h2 : 2 ≤ a.val.1.card := by omega
      have h2' : (2 : ℝ) ≤ (a.val.1.card : ℝ) := by exact_mod_cast h2
      nlinarith [sq_nonneg (coeff f a)]
  rw [← Finset.mul_sum] at hs
  nlinarith

theorem transverse_core_coercive {f : Field} (hf : transverse f) :
    4*squaredSize f ≤ coreEnergy f := by
  have h := transverse_coercive hf
  rw [exact_energy_decomposition] at h
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicLocalTransverseGap
