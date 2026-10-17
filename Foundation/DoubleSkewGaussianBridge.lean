import Foundation.SparseBlockPartialHessian
import Foundation.GaussianRecoveryCompactnessObstruction

/-! Two skew factors make a symmetric combined coefficient with a nonzero Gaussian target. -/
noncomputable section
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.DoubleSkewGaussianBridge
set_option backward.isDefEq.respectTransparency false
open ChristoffelSkewCancellation InfiniteGaussian GaussianDivergenceRecovery
open GaussianQuadraticSourceHodge GaussianSourceHodge
open GaussianNumberSectors

variable {L C : Type*} [Fintype L] [Fintype C]

def tensor (A : Matrix L L ℝ) (B : Matrix C C ℝ) : Matrix (L×C) (L×C) ℝ :=
  fun i j => A i.1 j.1*B i.2 j.2

omit [Fintype L] [Fintype C] in
theorem double_skew_symmetric (A : Matrix L L ℝ) (B : Matrix C C ℝ)
    (hA : ∀ i j, A j i= -A i j) (hB : ∀ a b, B b a= -B a b) (i j : L×C) :
    tensor A B j i=tensor A B i j := by
  unfold tensor
  rw [hA i.1 j.1, hB i.2 j.2]
  ring

omit [Fintype L] [Fintype C] in
theorem symmetric_skew_full_skew (A : Matrix L L ℝ) (B : Matrix C C ℝ)
    (hA : ∀ i j, A j i=A i j) (hB : ∀ a b, B b a= -B a b) (i j : L×C) :
    tensor A B j i= -tensor A B i j := by
  unfold tensor
  rw [hA i.1 j.1, hB i.2 j.2]
  ring

theorem symmetric_skew_contraction_zero (A : Matrix L L ℝ) (B : Matrix C C ℝ)
    (hA : ∀ i j, A j i=A i j) (hB : ∀ a b, B b a= -B a b) (v : L×C → ℝ) :
    contraction (tensor A B) v v=0 :=
  contraction_diagonal_zero _ (symmetric_skew_full_skew A B hA hB) v

theorem tensor_square_sum (A : Matrix L L ℝ) (B : Matrix C C ℝ) :
    (∑ i, ∑ j, (tensor A B i j)^2)=(∑ i, ∑ j, (A i j)^2)*(∑ a, ∑ b, (B a b)^2) := by
  simp only [tensor, Fintype.sum_prod_type, mul_pow]
  calc
    _ = ∑ i, ∑ j, ∑ a, ∑ b, (A i j)^2*(B a b)^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

omit [Fintype L] [Fintype C] in
theorem double_skew_symmetrize (A : Matrix L L ℝ) (B : Matrix C C ℝ)
    (hA : ∀ i j, A j i= -A i j) (hB : ∀ a b, B b a= -B a b) :
    symmetrize (tensor A B)=tensor A B := by
  ext i j
  unfold symmetrize
  rw [double_skew_symmetric A B hA hB]
  ring

theorem double_skew_gaussian_energy (A : Matrix L L ℝ) (B : Matrix C C ℝ)
    (hA : ∀ i j, A j i= -A i j) (hB : ∀ a b, B b a= -B a b)
    (h : L×C → CoefficientSpace) (hh : Orthonormal ℝ h) :
    ‖quadraticTarget h (tensor A B)‖^2=
      2*(∑ i, ∑ j, (A i j)^2)*(∑ a, ∑ b, (B a b)^2) := by
  rw [quadraticTarget_variance, double_skew_symmetrize A B hA hB,
    linearField_energy h hh, tensor_square_sum]
  ring

def J : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;-1,0]
def T : Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℝ := tensor J J
def sameCorner (p : Fin 2×Fin 2) : ℝ := if p.1=p.2 then 1 else 0
def oppositeCorner (p : Fin 2×Fin 2) : ℝ := if p=(0,0) then 1 else if p=(1,1) then -1 else 0

theorem J_skew (i j : Fin 2) : J j i= -J i j := by
  fin_cases i <;> fin_cases j <;> norm_num [J]

theorem T_symmetric (i j : Fin 2×Fin 2) : T j i=T i j :=
  double_skew_symmetric J J J_skew J_skew i j

theorem sameCorner_contraction : contraction T sameCorner sameCorner=2 := by
  norm_num [contraction, T, tensor, J, sameCorner, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem oppositeCorner_contraction : contraction T oppositeCorner oppositeCorner= -2 := by
  norm_num [contraction, T, tensor, J, oppositeCorner, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem determinant_contraction (v : Fin 2×Fin 2 → ℝ) :
    contraction T v v=2*(v (0,0)*v (1,1)-v (0,1)*v (1,0)) := by
  norm_num [contraction, T, tensor, J, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem T_square : T*T=1 := by
  ext i j
  rcases i with ⟨a,b⟩
  rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [T, tensor, J, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem T_trace : Matrix.trace T=0 := by
  norm_num [Matrix.trace, T, tensor, J, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem T_square_sum : (∑ i, ∑ j, (T i j)^2)=4 := by
  rw [T, tensor_square_sum]
  norm_num [J, Fin.sum_univ_two]

theorem T_symmetrize : symmetrize T=T := double_skew_symmetrize J J J_skew J_skew

theorem T_not_full_skew : ¬ ∀ i j, T j i= -T i j := by
  intro hh
  have hz := contraction_diagonal_zero T hh sameCorner
  rw [sameCorner_contraction] at hz
  norm_num at hz

theorem one_factor_gaussian_zero (h : Fin 2 → CoefficientSpace) : quadraticTarget h J=0 :=
  skew_gaussian_target_zero J J_skew h

theorem one_factor_divergence_kernel (h : Fin 2 → CoefficientSpace) :
    (linearField h J,0)∈hilbertDivergence.graph := by
  have hg := linearField_divergence_graph h J
  rw [one_factor_gaussian_zero] at hg
  exact hg

theorem T_transpose : T.transpose=T := by ext i j; exact T_symmetric i j

theorem gaussian_variance (h : Fin 2×Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    ‖quadraticTarget h T‖^2=8 := by
  rw [quadraticTarget_variance, T_symmetrize, linearField_energy h hh, T_square_sum]
  norm_num

theorem gaussian_target_nonzero (h : Fin 2×Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    quadraticTarget h T ≠ 0 := by
  intro hz
  have he := gaussian_variance h hh
  rw [hz] at he
  norm_num at he

theorem gaussian_gradient_projection (h : Fin 2×Fin 2 → CoefficientSpace) :
    gradientProjection (linearField h T)=linearField h T := by
  rw [linearField_gradientProjection, T_symmetrize]

theorem gaussian_gradient_mem (h : Fin 2×Fin 2 → CoefficientSpace) :
    linearField h T∈gradientRange := by
  simpa only [quadraticTarget_recovery, T_symmetrize] using
    recovery_mem_gradientRange (quadraticTarget h T)

theorem gaussian_recovery (h : Fin 2×Fin 2 → CoefficientSpace) :
    recovery (quadraticTarget h T)=linearField h T := by
  rw [quadraticTarget_recovery, T_symmetrize]

theorem gaussian_divergence_graph (h : Fin 2×Fin 2 → CoefficientSpace) :
    (linearField h T, quadraticTarget h T)∈hilbertDivergence.graph :=
  linearField_divergence_graph h T

theorem gaussian_derivative_graph (h : Fin 2×Fin 2 → CoefficientSpace) :
    (quadraticTarget h T, (2:ℝ) • linearField h T)∈closedCylindricalDerivative.graph := by
  have hg := quadraticTarget_derivative_graph h T
  rw [T_transpose, ← two_smul ℝ] at hg
  exact hg

theorem mixedTarget_symmetric (u v : CoefficientSpace) : mixedTarget u v=mixedTarget v u := by
  apply MeasureTheory.Lp.ext
  filter_upwards [mixedTarget_coeFn u v, mixedTarget_coeFn v u] with ω h1 h2
  rw [h1, h2, real_inner_comm u v]
  ring

theorem gaussian_target_expansion (h : Fin 2×Fin 2 → CoefficientSpace) :
    quadraticTarget h T=(2:ℝ) • (mixedTarget (h (0,0)) (h (1,1))-
      mixedTarget (h (0,1)) (h (1,0))) := by
  norm_num [quadraticTarget, T, tensor, J, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [mixedTarget_symmetric (h (1,0)) (h (0,1)), mixedTarget_symmetric (h (1,1)) (h (0,0))]
  module

theorem gaussian_determinant_ae (h : Fin 2×Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    quadraticTarget h T =ᵐ[gaussianProduct] fun ω => 2*
      (firstChaosEmbedding (h (0,0)) ω*firstChaosEmbedding (h (1,1)) ω-
        firstChaosEmbedding (h (0,1)) ω*firstChaosEmbedding (h (1,0)) ω) := by
  have hi := orthonormal_iff_ite.mp hh
  have hab : inner ℝ (h (0,0)) (h (1,1))=0 := by rw [hi]; norm_num
  have hcd : inner ℝ (h (0,1)) (h (1,0))=0 := by rw [hi]; norm_num
  rw [gaussian_target_expansion]
  filter_upwards [MeasureTheory.Lp.coeFn_smul (2:ℝ)
      (mixedTarget (h (0,0)) (h (1,1))-mixedTarget (h (0,1)) (h (1,0))),
    MeasureTheory.Lp.coeFn_sub (mixedTarget (h (0,0)) (h (1,1)))
      (mixedTarget (h (0,1)) (h (1,0))),
    mixedTarget_coeFn (h (0,0)) (h (1,1)), mixedTarget_coeFn (h (0,1)) (h (1,0))]
      with ω hs hd ha hb
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hs hd
  rw [hs, hd, ha, hb, hab, hcd]
  simp

theorem gaussian_field_energy (h : Fin 2×Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    ‖linearField h T‖^2=4 := by
  rw [linearField_energy h hh, T_square_sum]

theorem gaussian_recovery_energy (h : Fin 2×Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    ‖recovery (quadraticTarget h T)‖^2=4 := by
  rw [gaussian_recovery, gaussian_field_energy h hh]

theorem gaussian_not_kernel (h : Fin 2×Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    ¬ (linearField h T,0)∈hilbertDivergence.graph := by
  intro hg
  have hs := (linearField_divergence_kernel_iff h hh T).mp hg
  have hz := contraction_diagonal_zero T (fun i j => hs j i) sameCorner
  rw [sameCorner_contraction] at hz
  norm_num at hz

theorem gaussian_zero_mode (h : Fin 2×Fin 2 → CoefficientSpace) : projection 0 (quadraticTarget h T)=0 := by
  have hi := GaussianNumberSectors.graph_duality (closedDerivative_constant_graph 1)
    (gaussian_divergence_graph h)
  have hc : inner ℝ gaussianOne (quadraticTarget h T)=0 := by
    simpa only [one_smul, inner_zero_left] using hi.symm
  rw [projection_zero, hc, zero_smul]

def coordinateIndex (p : Fin 2×Fin 2) : ℕ := 2*p.1.val+p.2.val
def directions (p : Fin 2×Fin 2) : CoefficientSpace := lp.single 2 (coordinateIndex p) (1:ℝ)

theorem coordinateIndex_injective : Function.Injective coordinateIndex := by
  intro p q h
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all [coordinateIndex]

theorem directions_orthonormal : Orthonormal ℝ directions :=
  GaussianRecoveryCompactnessObstruction.coefficient_single_orthonormal.comp
    coordinateIndex coordinateIndex_injective

theorem actual_gaussian_variance : ‖quadraticTarget directions T‖^2=8 :=
  gaussian_variance directions directions_orthonormal

theorem actual_gaussian_nonzero : quadraticTarget directions T ≠ 0 :=
  gaussian_target_nonzero directions directions_orthonormal

theorem actual_gaussian_determinant :
    quadraticTarget directions T =ᵐ[gaussianProduct] fun ω => 2*
      (firstChaosEmbedding (directions (0,0)) ω*firstChaosEmbedding (directions (1,1)) ω-
        firstChaosEmbedding (directions (0,1)) ω*firstChaosEmbedding (directions (1,0)) ω) :=
  gaussian_determinant_ae directions directions_orthonormal

end OperatorDerivativeRewrite.Foundation.DoubleSkewGaussianBridge
