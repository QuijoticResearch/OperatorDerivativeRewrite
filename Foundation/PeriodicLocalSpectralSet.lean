import Foundation.PeriodicLocalWalshAction
import Mathlib.Tactic.Module

/-! The real eigenvalue set of the actual conditional single-block Hessian.
The proof uses its verified Walsh basis and a polynomial annihilator. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalSpectralSet
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity
  PeriodicSingleBlockDecomposition PeriodicLocalWalshAction
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

abbrev Field := Local → ℝ
def H : Field →ₗ[ℝ] Field := Matrix.toLin' localHessian
def shifted (r : ℝ) : Field →ₗ[ℝ] Field := H-r • LinearMap.id
def annihilator : Field →ₗ[ℝ] Field :=
  (shifted 3).comp ((shifted 7).comp ((shifted 9).comp (shifted 11)))

theorem H_apply (f : Field) : H f=localHessian.mulVec f := rfl

theorem shifted_apply (r : ℝ) (f : Field) : shifted r f=H f-r • f := rfl

theorem annihilator_eigen (f : Field) (ell : ℝ) (hf : H f=ell • f) :
    annihilator f=((ell-3)*(ell-7)*(ell-9)*(ell-11)) • f := by
  simp only [annihilator,LinearMap.comp_apply,shifted_apply,map_sub,map_smul,hf]
  module

theorem annihilator_two_modes (w g : Field) (ell : ℝ)
    (hw : H w=ell • w-(2 : ℝ) • g) (hg : H g=(3 : ℝ) • g)
    (hell : ell=7 ∨ ell=9 ∨ ell=11) : annihilator w=0 := by
  simp only [annihilator,LinearMap.comp_apply,shifted_apply,map_sub,map_smul,hw,hg]
  rcases hell with rfl | rfl | rfl <;> module

theorem walsh_H (T : Finset Direction) (i : Direction) (hi : i ∈ T) :
    H (walsh T i)=(3+2*(T.card : ℝ)) • walsh T i-(2 : ℝ) • walshSum T := by
  rw [H_apply,localHessian_decomposition,Matrix.add_mulVec,Matrix.ofNat_mulVec,
    coreGram_walsh T i hi]
  module

theorem label_card_cases : ∀ a : Label,
    a.val.1.card=1 ∨ a.val.1.card=2 ∨ a.val.1.card=3 ∨ a.val.1.card=4 := by decide

theorem annihilator_walsh (a : Label) : annihilator (walsh a.val.1 a.val.2)=0 := by
  have hg : H (walshSum a.val.1)=(3 : ℝ) • walshSum a.val.1 :=
    walshSum_eigenvalue_three a.val.1
  rcases label_card_cases a with h₁ | h₂ | h₃ | h₄
  · obtain ⟨j,hj⟩ := Finset.card_eq_one.mp h₁
    have hij : a.val.2=j := by simpa [hj] using a.property
    have hs : walshSum a.val.1=walsh a.val.1 a.val.2 := by
      simp [walshSum,hj,hij]
    rw [hs] at hg
    rw [annihilator_eigen _ 3 hg]
    norm_num
  · apply annihilator_two_modes _ (walshSum a.val.1) 7
    · convert walsh_H a.val.1 a.val.2 a.property using 1; norm_num [h₂]
    · exact hg
    · exact Or.inl rfl
  · apply annihilator_two_modes _ (walshSum a.val.1) 9
    · convert walsh_H a.val.1 a.val.2 a.property using 1; norm_num [h₃]
    · exact hg
    · exact Or.inr (Or.inl rfl)
  · apply annihilator_two_modes _ (walshSum a.val.1) 11
    · convert walsh_H a.val.1 a.val.2 a.property using 1; norm_num [h₄]
    · exact hg
    · exact Or.inr (Or.inr rfl)

theorem annihilator_eq_zero : annihilator=0 := by
  apply walshBasis.ext
  intro a
  change annihilator (walshBasis a)=0
  rw [walshBasis_apply]
  exact annihilator_walsh a

theorem eigenvalue_mem (ell : ℝ) (f : Field) (hf : f ≠ 0)
    (he : localHessian.mulVec f=ell • f) : ell=3 ∨ ell=7 ∨ ell=9 ∨ ell=11 := by
  have hp := annihilator_eigen f ell he
  rw [annihilator_eq_zero,LinearMap.zero_apply] at hp
  have hz : (ell-3)*(ell-7)*(ell-9)*(ell-11)=0 :=
    (smul_eq_zero.mp hp.symm).resolve_right hf
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h)))

theorem origin_local : ∀ i : Direction, localEdge (origin,i) := by decide
def originEdge (i : Direction) : Local := ⟨(origin,i),origin_local i⟩

theorem walsh_origin (T : Finset Direction) (i j : Direction) :
    walsh T i (originEdge j)=if j=i then 1 else 0 := by
  simp [walsh,intWalsh,originEdge,origin]

theorem walsh_difference_nonzero (T : Finset Direction) (i j : Direction)
    (hij : i ≠ j) : walsh T i-walsh T j ≠ 0 := by
  intro h
  have he := congrFun h (originEdge i)
  simp [walsh_origin,hij] at he

theorem eigenvalue_of_subset (T : Finset Direction) (i j : Direction)
    (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j) :
    ∃ f : Field, f ≠ 0 ∧ localHessian.mulVec f=(3+2*(T.card : ℝ)) • f :=
  ⟨walsh T i-walsh T j,walsh_difference_nonzero T i j hij,
    walsh_difference_eigenvalue T i j hi hj⟩

theorem eigenvalue_seven_exists :
    ∃ f : Field, f ≠ 0 ∧ localHessian.mulVec f=(7 : ℝ) • f := by
  convert eigenvalue_of_subset ({0,1} : Finset Direction) 0 1
    (by decide) (by decide) (by decide) using 1; norm_num

theorem eigenvalue_nine_exists :
    ∃ f : Field, f ≠ 0 ∧ localHessian.mulVec f=(9 : ℝ) • f := by
  convert eigenvalue_of_subset ({0,1,2} : Finset Direction) 0 1
    (by decide) (by decide) (by decide) using 1; norm_num

theorem eigenvalue_eleven_exists :
    ∃ f : Field, f ≠ 0 ∧ localHessian.mulVec f=(11 : ℝ) • f := by
  convert eigenvalue_of_subset (Finset.univ : Finset Direction) 0 1
    (by decide) (by decide) (by decide) using 1; norm_num

theorem eigenvalue_iff (ell : ℝ) :
    (∃ f : Field, f ≠ 0 ∧ localHessian.mulVec f=ell • f) ↔
      ell=3 ∨ ell=7 ∨ ell=9 ∨ ell=11 := by
  constructor
  · rintro ⟨f,hf,he⟩
    exact eigenvalue_mem ell f hf he
  · rintro (rfl | rfl | rfl | rfl)
    · exact eigenvalue_three_exists
    · exact eigenvalue_seven_exists
    · exact eigenvalue_nine_exists
    · exact eigenvalue_eleven_exists

end OperatorDerivativeRewrite.Foundation.PeriodicLocalSpectralSet
