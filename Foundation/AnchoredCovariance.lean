import Foundation.FiniteStableGamma
import Mathlib.Tactic
open scoped BigOperators
/-! Finite anchored covariance and conditional negative energy.
The exact real matrix equivalence is classical Schoenberg algebra.
The Fourier bridge reuses the actual Hermitian Gamma kernel and explicitly
requires an included zero-frequency anchor. No process or curvature claim. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.AnchoredCovariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def energy (d : ι → ι → ℝ) (c : ι → ℝ) : ℝ := ∑ i, ∑ j, c i*c j*d i j
def anchored (d : ι → ι → ℝ) (o : ι) (i j : ι) : ℝ := (d i o+d o j-d i j)/2
def centered (o : ι) (c : ι → ℝ) (i : ι) : ℝ := c i - if i=o then ∑ j,c j else 0
theorem centered_sum (o : ι) (c : ι → ℝ) : ∑ i,centered o c i = 0 := by
  simp [centered,Finset.sum_sub_distrib]
theorem anchored_energy (d : ι → ι → ℝ) (o : ι) (c : ι → ℝ) :
    2*energy (anchored d o) c =
      (∑ i,c i*d i o)*(∑ j,c j)+(∑ i,c i)*(∑ j,c j*d o j)-energy d c := by
  calc
    _ = ∑ i, ∑ j, (c i*d i o*c j+c i*(c j*d o j)-c i*c j*d i j) := by
      unfold energy anchored
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,energy]
theorem centered_energy (d : ι → ι → ℝ) (o : ι) (h0 : d o o=0) (c : ι → ℝ) :
    energy d (centered o c) = energy d c -
      (∑ i,c i*d i o)*(∑ j,c j)-(∑ i,c i)*(∑ j,c j*d o j) := by
  unfold energy centered
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib]
  simp only [ite_mul,mul_ite,zero_mul,mul_zero,Finset.sum_ite_irrel,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,h0]
  simp only [Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp_rw [mul_assoc]
  simp only [← Finset.mul_sum,← Finset.sum_mul,mul_zero,sub_zero]
  have he : (∑ x, c x*((∑ j,c j)*d x o)) = (∑ j,c j)*(∑ x,c x*d x o) := by
    simp only [Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]
  rw [he]
  ring
theorem covariance_identity (d : ι → ι → ℝ) (o : ι) (h0 : d o o=0) (c : ι → ℝ) :
    2*energy (anchored d o) c = -energy d (centered o c) := by
  rw [anchored_energy,centered_energy d o h0]
  ring
def CondNegative (d : ι → ι → ℝ) : Prop := ∀ c : ι → ℝ, (∑ i,c i)=0 → energy d c ≤ 0
theorem anchored_positive_iff (d : ι → ι → ℝ) (o : ι) (h0 : d o o=0) :
    (∀ c : ι → ℝ, 0 ≤ energy (anchored d o) c) ↔ CondNegative d := by
  constructor
  · intro h c hc
    have he := anchored_energy d o c
    rw [hc,mul_zero,zero_mul,zero_add,zero_sub] at he
    linarith [h c]
  · intro h c
    have hn := h (centered o c) (centered_sum o c)
    have he := covariance_identity d o h0 c
    linarith
theorem anchored_symm (d : ι → ι → ℝ) (hd : ∀ i j,d i j=d j i) (o i j : ι) :
    anchored d o i j = anchored d o j i := by
  unfold anchored
  rw [hd i o,hd o j,hd i j]
  ring
theorem anchored_posSemidef_iff (d : ι → ι → ℝ) (hd : ∀ i j,d i j=d j i)
    (o : ι) (h0 : d o o=0) : Matrix.PosSemidef (anchored d o) ↔ CondNegative d := by
  rw [← anchored_positive_iff d o h0]
  constructor
  · intro h c
    simpa only [energy,dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
      Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using h.dotProduct_mulVec_nonneg c
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      change anchored d o j i = anchored d o i j
      exact anchored_symm d hd o j i
    · intro c
      simpa only [energy,dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
        Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using h c
theorem quadratic_plus_diagonal : (((1:ℝ)^2+1^2-(1+1)^2)/2) = -1 := by norm_num
open FiniteFourierDifferentialTrace
theorem fourier_anchor (ψ : Wave → ℝ) (he : ∀ k,ψ (-k)=ψ k)
    (k : ι → Wave) (o : ι) (ho : k o=0) (i j : ι) :
    anchored (fun i j => ψ (k j-k i)) o i j = FiniteStableGamma.Core.kernel ψ (k i) (k j) := by
  simp [anchored,FiniteStableGamma.Core.kernel,ho,he]
theorem fourier_covariance_iff (ψ : Wave → ℝ) (h0 : ψ 0=0) (he : ∀ k,ψ (-k)=ψ k)
    (k : ι → Wave) (o : ι) (ho : k o=0) :
    Matrix.PosSemidef (fun i j => FiniteStableGamma.Core.kernel ψ (k i) (k j)) ↔
      CondNegative (fun i j => ψ (k j-k i)) := by
  have hd (i j : ι) : ψ (k j-k i)=ψ (k i-k j) := by
    rw [← he (k j-k i),neg_sub]
  have hz : ψ (k o-k o)=0 := by simpa using h0
  have hh := anchored_posSemidef_iff (fun i j => ψ (k j-k i)) hd o hz
  have hk : anchored (fun i j => ψ (k j-k i)) o = (fun i j => FiniteStableGamma.Core.kernel ψ (k i) (k j)) := funext fun i => funext fun j => fourier_anchor ψ he k o ho i j
  rw [hk] at hh
  exact hh

end OperatorDerivativeRewrite.Foundation.AnchoredCovariance
