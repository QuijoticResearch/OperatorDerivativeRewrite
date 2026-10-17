import Foundation.PeriodicLocalGradientModes
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Exact Walsh action of the internal curl Gram matrix of the actual
periodic single block. Integer certificates are checked by kernel reduction. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalWalshAction
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity
  PeriodicSingleBlockDecomposition PeriodicLocalGradientModes
set_option maxRecDepth 65536
set_option maxHeartbeats 128000000
set_option backward.isDefEq.respectTransparency false

abbrev Label := {a : Finset Direction × Direction // a.2 ∈ a.1}

theorem label_card : Fintype.card Label=32 := by decide

def intWalsh (T : Finset Direction) (i : Direction) (e : Edge) : ℤ :=
  if e.2=i then (-1)^(∑ j ∈ T.erase i, (e.1 j).val) else 0

def walsh (T : Finset Direction) (i : Direction) (e : Local) : ℝ :=
  (intWalsh T i e.val : ℝ)

def walshSum (T : Finset Direction) : Local → ℝ := ∑ i ∈ T, walsh T i

theorem int_core_action : ∀ a : Label, ∀ e : Local,
    (∑ p : Core, coefficient p.val e.val *
      intCurl (intWalsh a.val.1 a.val.2) p.val.val.1 p.val.val.2.1 p.val.val.2.2)=
    (2*(a.val.1.card : ℤ))*intWalsh a.val.1 a.val.2 e.val-
      2*∑ j ∈ a.val.1, intWalsh a.val.1 j e.val := by decide

theorem coreMatrix_entry (p : Core) (e : Local) :
    coreMatrix p e=(coefficient p.val e.val : ℝ) := by
  rw [coreMatrix,LinearMap.toMatrix'_apply]
  exact localIncidence_single p.val e

theorem coreIncidence_walsh (T : Finset Direction) (i : Direction) (p : Core) :
    coreIncidence (walsh T i) p=
      (intCurl (intWalsh T i) p.val.val.1 p.val.val.2.1 p.val.val.2.2 : ℝ) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := core_links_local p
  change curl (localExtend (walsh T i)) p.val.val.1
    p.val.val.2.1 p.val.val.2.2=_
  have he (e : Edge) (h : localEdge e) :
      localExtend (walsh T i) e=(intWalsh T i e : ℝ) := by
    change (if he : localEdge e then walsh T i ⟨e,he⟩ else 0)=_
    simp [h,walsh]
  unfold curl
  rw [he _ h₁,he _ h₂,he _ h₃,he _ h₄]
  simp only [intCurl,Int.cast_add,Int.cast_sub]

theorem coreGram_walsh (T : Finset Direction) (i : Direction) (hi : i ∈ T) :
    coreGram.mulVec (walsh T i)=
      (2*(T.card : ℝ)) • walsh T i-(2 : ℝ) • walshSum T := by
  rw [coreGram,← Matrix.mulVec_mulVec,coreMatrix_mulVec]
  ext e
  change (∑ p : Core, coreMatrix p e*coreIncidence (walsh T i) p)=_
  simp only [coreMatrix_entry,coreIncidence_walsh]
  have h := int_core_action ⟨(T,i),hi⟩ e
  change (∑ p : Core, coefficient p.val e.val *
      intCurl (intWalsh T i) p.val.val.1 p.val.val.2.1 p.val.val.2.2)=
    (2*(T.card : ℤ))*intWalsh T i e.val-2*∑ j ∈ T, intWalsh T j e.val at h
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,walshSum,Finset.sum_apply,walsh]
  exact_mod_cast h

theorem coreGram_walshSum (T : Finset Direction) :
    coreGram.mulVec (walshSum T)=0 := by
  unfold walshSum
  rw [Matrix.mulVec_sum]
  have hs : (∑ i ∈ T, coreGram.mulVec (walsh T i))=
      ∑ i ∈ T, ((2*(T.card : ℝ)) • walsh T i-(2 : ℝ) • walshSum T) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact coreGram_walsh T i hi
  rw [hs]
  ext e
  simp only [Finset.sum_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const]
  simp only [nsmul_eq_mul]
  simp only [walshSum,Finset.sum_apply]
  ring

theorem walshSum_eigenvalue_three (T : Finset Direction) :
    localHessian.mulVec (walshSum T)=(3 : ℝ) • walshSum T := by
  rw [localHessian_decomposition,Matrix.add_mulVec,Matrix.ofNat_mulVec,
    coreGram_walshSum,add_zero]

theorem coreGram_walsh_difference (T : Finset Direction) (i j : Direction)
    (hi : i ∈ T) (hj : j ∈ T) :
    coreGram.mulVec (walsh T i-walsh T j)=
      (2*(T.card : ℝ)) • (walsh T i-walsh T j) := by
  rw [Matrix.mulVec_sub,coreGram_walsh T i hi,coreGram_walsh T j hj]
  rw [smul_sub]
  abel

theorem walsh_difference_eigenvalue (T : Finset Direction) (i j : Direction)
    (hi : i ∈ T) (hj : j ∈ T) :
    localHessian.mulVec (walsh T i-walsh T j)=
      (3+2*(T.card : ℝ)) • (walsh T i-walsh T j) := by
  rw [localHessian_decomposition,Matrix.add_mulVec,Matrix.ofNat_mulVec,
    coreGram_walsh_difference T i j hi hj,add_smul]

theorem int_walsh_orthogonality : ∀ a b : Label,
    (∑ e : Local, intWalsh a.val.1 a.val.2 e.val*intWalsh b.val.1 b.val.2 e.val)=
      if a=b then 8 else 0 := by decide

theorem walsh_orthogonality (a b : Label) :
    dotProduct (walsh a.val.1 a.val.2) (walsh b.val.1 b.val.2)=
      if a=b then (8 : ℝ) else 0 := by
  have h := int_walsh_orthogonality a b
  unfold dotProduct walsh
  exact_mod_cast h

theorem walsh_linearIndependent :
    LinearIndependent ℝ (fun a : Label => walsh a.val.1 a.val.2) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc a
  have h := congrArg (fun f => dotProduct f (walsh a.val.1 a.val.2)) hc
  rw [sum_dotProduct] at h
  simp only [smul_dotProduct,walsh_orthogonality,smul_eq_mul,zero_dotProduct] at h
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
  linarith

def walshBasis : Module.Basis Label ℝ (Local → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ walsh_linearIndependent (by
    rw [label_card,Module.finrank_fintype_fun_eq_card,local_card])

theorem walshBasis_apply (a : Label) : walshBasis a=walsh a.val.1 a.val.2 := by
  rw [walshBasis,coe_basisOfLinearIndependentOfCardEqFinrank']

end OperatorDerivativeRewrite.Foundation.PeriodicLocalWalshAction
