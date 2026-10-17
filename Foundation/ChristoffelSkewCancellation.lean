import Foundation.GaussianQuadraticSourceHodge
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic

/-! Finite antisymmetric contractions and the explicit hypotheses of a frame Hessian. -/
noncomputable section
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.ChristoffelSkewCancellation
set_option backward.isDefEq.respectTransparency false

variable {I : Type*} [Fintype I]

def contraction (A : Matrix I I ℝ) (v w : I → ℝ) : ℝ := ∑ i, ∑ j, A i j*v i*w j

theorem contraction_flip (A : Matrix I I ℝ) (hA : ∀ i j, A j i= -A i j) (v w : I → ℝ) :
    contraction A w v= -contraction A v w := by
  unfold contraction
  calc
    _ = ∑ i, ∑ j, A j i*w j*v i := Finset.sum_comm
    _ = ∑ i, ∑ j, -(A i j*v i*w j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hA i j]
      ring
    _ = _ := by simp only [Finset.sum_neg_distrib]

theorem contraction_diagonal_zero (A : Matrix I I ℝ) (hA : ∀ i j, A j i= -A i j) (v : I → ℝ) :
    contraction A v v=0 := by
  have hh := contraction_flip A hA v v
  linarith

variable {L C P : Type*} [Fintype L] [Fintype C] [Fintype P]

def correction (Γ : C → C → C → ℝ) (s : P → L → ℝ) (g : P → C → ℝ) (φ : P → ℝ) :
    Matrix (L × C) (L × C) ℝ := fun i j =>
  -(∑ p, ∑ c, s p i.1*s p j.1*Γ i.2 j.2 c*g p c*φ p)

theorem correction_skew (Γ : C → C → C → ℝ) (hΓ : ∀ a b c, Γ b a c= -Γ a b c)
    (s : P → L → ℝ) (g : P → C → ℝ) (φ : P → ℝ) (i j : L × C) :
    correction Γ s g φ j i= -correction Γ s g φ i j := by
  have he : (∑ p, ∑ c, s p j.1*s p i.1*Γ j.2 i.2 c*g p c*φ p) =
      -(∑ p, ∑ c, s p i.1*s p j.1*Γ i.2 j.2 c*g p c*φ p) := by
    calc
      _ = ∑ p, ∑ c, -(s p i.1*s p j.1*Γ i.2 j.2 c*g p c*φ p) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro c hc
        rw [hΓ i.2 j.2 c]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  unfold correction
  rw [he]

theorem correction_quadratic_zero (Γ : C → C → C → ℝ) (hΓ : ∀ a b c, Γ b a c= -Γ a b c)
    (s : P → L → ℝ) (g : P → C → ℝ) (φ : P → ℝ) (v : L × C → ℝ) :
    contraction (correction Γ s g φ) v v=0 :=
  contraction_diagonal_zero _ (correction_skew Γ hΓ s g φ) v

def halfCoefficients (f : C → C → C → ℝ) (a b c : C) : ℝ := f a b c/2

theorem half_coefficients_torsion (f : C → C → C → ℝ) (hf : ∀ a b c, f b a c= -f a b c)
    (a b c : C) : halfCoefficients f a b c-halfCoefficients f b a c=f a b c := by
  unfold halfCoefficients
  rw [hf a b c]
  ring

theorem half_coefficients_skew (f : C → C → C → ℝ) (hf : ∀ a b c, f b a c= -f a b c)
    (a b c : C) : halfCoefficients f b a c= -halfCoefficients f a b c := by
  unfold halfCoefficients
  rw [hf a b c]
  ring

theorem half_correction_quadratic_zero (f : C → C → C → ℝ)
    (hf : ∀ a b c, f b a c= -f a b c) (s : P → L → ℝ) (g : P → C → ℝ) (φ : P → ℝ)
    (v : L × C → ℝ) : contraction (correction (halfCoefficients f) s g φ) v v=0 :=
  correction_quadratic_zero _ (half_coefficients_skew f hf) s g φ v

theorem coordinate_torsionfree_symmetric (Γ : C → C → C → ℝ)
    (hT : ∀ a b c, Γ a b c-Γ b a c=0) (a b c : C) : Γ a b c=Γ b a c :=
  sub_eq_zero.mp (hT a b c)

theorem coordinate_and_skew_zero (Γ : C → C → C → ℝ)
    (hT : ∀ a b c, Γ a b c-Γ b a c=0) (hΓ : ∀ a b c, Γ b a c= -Γ a b c)
    (a b c : C) : Γ a b c=0 := by
  have hh := coordinate_torsionfree_symmetric Γ hT a b c
  rw [hΓ a b c] at hh
  linarith

theorem half_coefficients_coordinate_iff (f : C → C → C → ℝ)
    (hf : ∀ a b c, f b a c= -f a b c) :
    (∀ a b c, halfCoefficients f a b c-halfCoefficients f b a c=0) ↔
      ∀ a b c, f a b c=0 := by
  simp only [half_coefficients_torsion f hf]

def frameHessian (D : Matrix C C ℝ) (Γ : C → C → C → ℝ) (g : C → ℝ) : Matrix C C ℝ :=
  fun a b => D a b-∑ c, Γ a b c*g c

theorem frameHessian_symmetric (f : C → C → C → ℝ) (hf : ∀ a b c, f b a c= -f a b c)
    (D : Matrix C C ℝ) (g : C → ℝ)
    (hD : ∀ a b, D a b-D b a=∑ c, f a b c*g c) (a b : C) :
    frameHessian D (halfCoefficients f) g a b=frameHessian D (halfCoefficients f) g b a := by
  have hs : (∑ c, halfCoefficients f a b c*g c) -
      (∑ c, halfCoefficients f b a c*g c)=∑ c, f a b c*g c := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← sub_mul, half_coefficients_torsion f hf]
  unfold frameHessian
  linarith [hD a b]

open InfiniteGaussian GaussianDivergenceRecovery GaussianQuadraticSourceHodge

theorem skew_gaussian_target_zero (A : Matrix I I ℝ) (hA : ∀ i j, A j i= -A i j)
    (h : I → CoefficientSpace) : quadraticTarget h A=0 := by
  have hs : symmetrize A=0 := by
    ext i j
    change (A i j+A j i)/2=0
    rw [hA i j]
    ring
  have hz : linearField h (0 : Matrix I I ℝ)=0 := by simp [linearField]
  have he := quadraticTarget_variance h A
  rw [hs, hz] at he
  norm_num at he
  exact he

theorem correction_gaussian_divergence_graph (Γ : C → C → C → ℝ)
    (hΓ : ∀ a b c, Γ b a c= -Γ a b c)
    (s : P → L → ℝ) (g : P → C → ℝ) (φ : P → ℝ) (h : L × C → CoefficientSpace) :
    (linearField h (correction Γ s g φ),0)∈hilbertDivergence.graph := by
  have he := linearField_divergence_graph h (correction Γ s g φ)
  rwa [skew_gaussian_target_zero _ (correction_skew Γ hΓ s g φ) h] at he

section Operators
variable {R : Type*} [Ring R] [Algebra ℝ R]

def operatorContraction (A : Matrix I I ℝ) (X : I → R) : R :=
  ∑ i, ∑ j, A i j • (X i*X j)

theorem reversed_operator_contraction (A : Matrix I I ℝ) (hA : ∀ i j, A j i= -A i j) (X : I → R) :
    (∑ i, ∑ j, A i j • (X j*X i))= -operatorContraction A X := by
  calc
    _ = ∑ i, ∑ j, A j i • (X i*X j) := Finset.sum_comm
    _ = ∑ i, ∑ j, -(A i j • (X i*X j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hA i j, neg_smul]
    _ = _ := by simp only [operatorContraction, Finset.sum_neg_distrib]

theorem weighted_commutator (A : Matrix I I ℝ) (hA : ∀ i j, A j i= -A i j) (X : I → R) :
    (∑ i, ∑ j, A i j • (X i*X j-X j*X i))=(2:ℝ) • operatorContraction A X := by
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [reversed_operator_contraction A hA X]
  change operatorContraction A X- -operatorContraction A X=(2:ℝ) • operatorContraction A X
  module

theorem operator_half_commutator (A : Matrix I I ℝ) (hA : ∀ i j, A j i= -A i j) (X : I → R) :
    operatorContraction A X=(1/2:ℝ) • (∑ i, ∑ j, A i j • (X i*X j-X j*X i)) := by
  rw [weighted_commutator A hA X, smul_smul]
  norm_num
end Operators

def generatorX : Matrix (Fin 2) (Fin 2) ℂ := !![0,1; -1,0]
def generatorY : Matrix (Fin 2) (Fin 2) ℂ := !![0,Complex.I; Complex.I,0]
def generatorZ : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I,0; 0,-Complex.I]

theorem generators_skewHermitian : generatorXᴴ= -generatorX ∧ generatorYᴴ= -generatorY ∧
    generatorZᴴ= -generatorZ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [generatorX, generatorY, generatorZ, Matrix.conjTranspose_apply]

theorem generators_trace_zero : Matrix.trace generatorX=0 ∧ Matrix.trace generatorY=0 ∧
    Matrix.trace generatorZ=0 := by
  norm_num [Matrix.trace, Fin.sum_univ_two, generatorX, generatorY, generatorZ]

theorem generatorX_mulY : generatorX*generatorY=generatorZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, generatorX, generatorY, generatorZ]

theorem generatorY_mulX : generatorY*generatorX= -generatorZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, generatorX, generatorY, generatorZ]

theorem generatorZ_ne_zero : generatorZ≠0 := by
  intro hz
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hz
  exact Complex.I_ne_zero (by simpa [generatorZ] using hh)

def operatorCoefficients : Matrix (Fin 2) (Fin 2) ℝ := !![0,1; -1,0]
def operatorFamily (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := if i=0 then generatorX else generatorY

theorem operatorCoefficients_skew (i j : Fin 2) :
    operatorCoefficients j i= -operatorCoefficients i j := by
  fin_cases i <;> fin_cases j <;> norm_num [operatorCoefficients]

theorem explicit_operator_contraction :
    operatorContraction operatorCoefficients operatorFamily=(2:ℝ) • generatorZ := by
  unfold operatorContraction
  norm_num [Fin.sum_univ_two, operatorCoefficients, operatorFamily]
  rw [generatorX_mulY, generatorY_mulX]
  module

theorem explicit_operator_nonzero : operatorContraction operatorCoefficients operatorFamily≠0 := by
  rw [explicit_operator_contraction]
  exact smul_ne_zero (by norm_num : (2:ℝ)≠0) generatorZ_ne_zero

theorem same_coefficients_scalar_zero (v : Fin 2 → ℝ) :
    contraction operatorCoefficients v v=0 :=
  contraction_diagonal_zero _ operatorCoefficients_skew v

end OperatorDerivativeRewrite.Foundation.ChristoffelSkewCancellation
