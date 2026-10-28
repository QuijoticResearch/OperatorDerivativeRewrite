import Foundation.YMPositiveKernel
/-!
Ordered-tree and selected-forest gauge trivialization; four-cycle holonomy
reconstruction and genuine Haar pairing cancellation. The forest certificate
allows free vertex gauges. The boundary-fixed path obstruction and the missing
full-lattice product/spectral bridge are not removed by these identities.
-/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2ForestCycleReduction
variable {G : Type*} [Group G]

def recursiveGauge (parent : ℕ → ℕ) (hp : ∀ i, parent i ≤ i) (U : ℕ → G) : ℕ → G
  | 0 => 1
  | i+1 => recursiveGauge parent hp U (parent i)*U i
termination_by v => v
decreasing_by exact Nat.lt_succ_of_le (hp i)

def extendedParent {n : ℕ} (p : Fin n → Fin (n+1)) (i : ℕ) : ℕ :=
  if hi : i < n then (p ⟨i,hi⟩).val else 0

theorem extendedParent_le {n : ℕ} (p : Fin n → Fin (n+1))
    (hp : ∀ i, (p i).val ≤ i.val) (i : ℕ) : extendedParent p i ≤ i := by
  unfold extendedParent
  split_ifs with hi
  · exact hp ⟨i,hi⟩
  · omega

def extendedField {n : ℕ} (U : Fin n → G) (i : ℕ) : G :=
  if hi : i < n then U ⟨i,hi⟩ else 1

def treeGauge {n : ℕ} (p : Fin n → Fin (n+1)) (hp : ∀ i, (p i).val ≤ i.val)
    (U : Fin n → G) (v : Fin (n+1)) : G :=
  recursiveGauge (extendedParent p) (extendedParent_le p hp) (extendedField U) v.val

def treeAction {n : ℕ} (p : Fin n → Fin (n+1)) (g : Fin (n+1) → G)
    (U : Fin n → G) (i : Fin n) : G := g (p i)*U i*(g i.succ)⁻¹

theorem treeGauge_trivializes {n : ℕ} (p : Fin n → Fin (n+1))
    (hp : ∀ i, (p i).val ≤ i.val) (U : Fin n → G) :
    treeAction p (treeGauge p hp U) U = fun _ => 1 := by
  funext i
  have he : treeGauge p hp U i.succ = treeGauge p hp U (p i)*U i := by
    simp only [treeGauge,Fin.val_succ,recursiveGauge,extendedParent,extendedField,i.isLt,dif_pos]
  unfold treeAction
  rw [he,mul_inv_cancel]

theorem tree_invariant_constant {n : ℕ} (p : Fin n → Fin (n+1))
    (hp : ∀ i, (p i).val ≤ i.val) {E : Type*} (f : (Fin n → G) → E)
    (hf : ∀ g U, f (treeAction p g U)=f U) (U : Fin n → G) :
    f U = f (fun _ => 1) := by
  rw [← hf (treeGauge p hp U) U,treeGauge_trivializes p hp U]

/-- A loop has four independent vertex gauges, unlike the open ordered tree. -/
def CycleInvariant {E : Type*} (f : G → G → G → G → E) : Prop :=
  ∀ g₀ g₁ g₂ g₃ A B C D,
    f (g₀*A*g₁⁻¹) (g₁*B*g₂⁻¹) (g₂*C*g₃⁻¹) (g₃*D*g₀⁻¹)=f A B C D

theorem cycle_reconstruct {E : Type*} (f : G → G → G → G → E)
    (hf : CycleInvariant f) (A B C D : G) : f A B C D=f 1 1 1 (A*B*C*D) := by
  have hh := hf 1 A (A*B) (A*B*C) A B C D
  have h₁ : (1:G)*A*A⁻¹=1 := by group
  have h₂ : A*B*(A*B)⁻¹=1 := by group
  have h₃ : (A*B)*C*(A*B*C)⁻¹=1 := by group
  have h₄ : (A*B*C)*D*(1:G)⁻¹=A*B*C*D := by group
  rw [h₁,h₂,h₃,h₄] at hh
  exact hh.symm

theorem canonical_conjugate {E : Type*} (f : G → G → G → G → E)
    (hf : CycleInvariant f) (g W : G) : f 1 1 1 (g*W*g⁻¹)=f 1 1 1 W := by
  have hh := hf g g g g 1 1 1 W
  simpa using hh

theorem class_cyclic {E : Type*} (F : G → E)
    (hF : ∀ g W, F (g*W*g⁻¹)=F W) (A B : G) : F (A*B)=F (B*A) := by
  have hh := hF A⁻¹ (A*B)
  have he : A⁻¹*(A*B)*(A⁻¹)⁻¹=B*A := by group
  rw [he] at hh
  exact hh.symm
end OperatorDerivativeRewrite.Foundation.SU2ForestCycleReduction

namespace OperatorDerivativeRewrite.Foundation.SU2ForestCycleReduction
variable {G : Type*} [Group G]

def forestExtend {n : ℕ} (S : Finset (Fin n)) (U : S → G) (i : Fin n) : G :=
  if hi : i ∈ S then U ⟨i,hi⟩ else 1

def forestAction {n : ℕ} (p : Fin n → Fin (n+1)) (S : Finset (Fin n))
    (g : Fin (n+1) → G) (U : S → G) (i : S) : G :=
  g (p i.val)*U i*(g i.val.succ)⁻¹

theorem forestGauge_trivializes {n : ℕ} (p : Fin n → Fin (n+1))
    (hp : ∀ i, (p i).val ≤ i.val) (S : Finset (Fin n)) (U : S → G) :
    forestAction p S (treeGauge p hp (forestExtend S U)) U = fun _ => 1 := by
  funext i
  have hh := congrFun (treeGauge_trivializes p hp (forestExtend S U)) i.val
  simpa only [forestAction,treeAction,forestExtend,i.property,dif_pos] using hh

theorem forest_invariant_constant {n : ℕ} (p : Fin n → Fin (n+1))
    (hp : ∀ i, (p i).val ≤ i.val) (S : Finset (Fin n)) {E : Type*} (f : (S → G) → E)
    (hf : ∀ g U, f (forestAction p S g U)=f U) (U : S → G) :
    f U=f (fun _ => 1) := by
  rw [← hf (treeGauge p hp (forestExtend S U)) U,forestGauge_trivializes p hp S U]

open QuaternionSU2Representation

theorem class_sandwich_integral (F : SU2 → ℝ)
    (hF : ∀ g W, F (g*W*g⁻¹)=F W) (L R : SU2) :
    (∫ V, F (L*V*R) ∂law) = ∫ W, F W ∂law := by
  have he : (fun V => F (L*V*R)) = fun V => F ((R*L)*V) := by
    funext V
    rw [class_cyclic F hF (L*V) R]
    simp only [mul_assoc]
  rw [he]
  exact integral_mul_left_eq_self F (R*L)

theorem class_sandwich_integrable (F : SU2 → ℝ) (hF : Measurable F)
    (M : ℝ) (hb : ∀ W, |F W| ≤ M) (L R : SU2) :
    Integrable (fun V => F (L*V*R)) law := by
  apply Integrable.of_bound
    (hF.comp ((measurable_mul_const R).comp (measurable_const_mul L))).aestronglyMeasurable M
  filter_upwards with V
  simpa only [Real.norm_eq_abs,Function.comp_apply] using hb (L*V*R)

theorem cycle_one_edge_integrals (f : SU2 → SU2 → SU2 → SU2 → ℝ)
    (hf : CycleInvariant f) (A B C D : SU2) :
    (∫ V, f V B C D ∂law) = (∫ W, f 1 1 1 W ∂law) ∧
    (∫ V, f A V C D ∂law) = (∫ W, f 1 1 1 W ∂law) ∧
    (∫ V, f A B V D ∂law) = (∫ W, f 1 1 1 W ∂law) ∧
    (∫ V, f A B C V ∂law) = (∫ W, f 1 1 1 W ∂law) := by
  have hF := canonical_conjugate f hf
  have h₁ : (fun V => f V B C D) = fun V => f 1 1 1 (V*B*C*D) :=
    funext (fun V => cycle_reconstruct f hf V B C D)
  have h₂ : (fun V => f A V C D) = fun V => f 1 1 1 (A*V*C*D) :=
    funext (fun V => cycle_reconstruct f hf A V C D)
  have h₃ : (fun V => f A B V D) = fun V => f 1 1 1 (A*B*V*D) :=
    funext (fun V => cycle_reconstruct f hf A B V D)
  have h₄ : (fun V => f A B C V) = fun V => f 1 1 1 (A*B*C*V) :=
    funext (fun V => cycle_reconstruct f hf A B C V)
  rw [h₁,h₂,h₃,h₄]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [one_mul,mul_assoc] using class_sandwich_integral (f 1 1 1) hF 1 (B*C*D)
  · simpa only [mul_assoc] using class_sandwich_integral (f 1 1 1) hF A (C*D)
  · exact class_sandwich_integral (f 1 1 1) hF (A*B) D
  · simpa only [mul_one] using class_sandwich_integral (f 1 1 1) hF (A*B*C) 1

theorem centered_cycle_one_edge_zero (f : SU2 → SU2 → SU2 → SU2 → ℝ)
    (hf : CycleInvariant f) (hzero : (∫ W, f 1 1 1 W ∂law)=0) (A B C D : SU2) :
    (∫ V, f V B C D ∂law)=0 ∧ (∫ V, f A V C D ∂law)=0 ∧
    (∫ V, f A B V D ∂law)=0 ∧ (∫ V, f A B C V ∂law)=0 := by
  simpa only [hzero] using cycle_one_edge_integrals f hf A B C D

theorem cycle_one_edge_integrable (f : SU2 → SU2 → SU2 → SU2 → ℝ)
    (hf : CycleInvariant f) (hm : Measurable (f 1 1 1))
    (M : ℝ) (hb : ∀ A B C D, |f A B C D| ≤ M) (A B C D : SU2) :
    Integrable (fun V => f V B C D) law ∧ Integrable (fun V => f A V C D) law ∧
    Integrable (fun V => f A B V D) law ∧ Integrable (fun V => f A B C V) law := by
  have hb' (W : SU2) : |f 1 1 1 W| ≤ M := hb 1 1 1 W
  have h₁ : (fun V => f V B C D) = fun V => f 1 1 1 (V*B*C*D) :=
    funext (fun V => cycle_reconstruct f hf V B C D)
  have h₂ : (fun V => f A V C D) = fun V => f 1 1 1 (A*V*C*D) :=
    funext (fun V => cycle_reconstruct f hf A V C D)
  have h₃ : (fun V => f A B V D) = fun V => f 1 1 1 (A*B*V*D) :=
    funext (fun V => cycle_reconstruct f hf A B V D)
  have h₄ : (fun V => f A B C V) = fun V => f 1 1 1 (A*B*C*V) :=
    funext (fun V => cycle_reconstruct f hf A B C V)
  rw [h₁,h₂,h₃,h₄]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [one_mul,mul_assoc] using class_sandwich_integrable (f 1 1 1) hm M hb' 1 (B*C*D)
  · simpa only [mul_assoc] using class_sandwich_integrable (f 1 1 1) hm M hb' A (C*D)
  · exact class_sandwich_integrable (f 1 1 1) hm M hb' (A*B) D
  · simpa only [mul_one] using class_sandwich_integrable (f 1 1 1) hm M hb' (A*B*C) 1
end OperatorDerivativeRewrite.Foundation.SU2ForestCycleReduction

namespace OperatorDerivativeRewrite.Foundation.SU2ForestCycleReduction
open QuaternionSU2Representation
abbrev Triple := SU2 × SU2 × SU2
def tripleLaw : Measure Triple := law.prod (law.prod law)

private theorem joint_mul_measurable : Measurable (fun p : SU2 × SU2 => p.1*p.2) := by
  have hA : Measurable (fun p : SU2 × SU2 => (p.1 : SU2TraceHessianModel.M2)) :=
    measurable_subtype_coe.comp measurable_fst
  have hB : Measurable (fun p : SU2 × SU2 => (p.2 : SU2TraceHessianModel.M2)) :=
    measurable_subtype_coe.comp measurable_snd
  have ha (i j : Fin 2) : Measurable (fun p : SU2 × SU2 => (p.1 : SU2TraceHessianModel.M2) i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
  have hb (i j : Fin 2) : Measurable (fun p : SU2 × SU2 => (p.2 : SU2TraceHessianModel.M2) i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hB)
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  change Measurable (fun p : SU2 × SU2 => ∑ k : Fin 2,
    (p.1 : SU2TraceHessianModel.M2) i k*(p.2 : SU2TraceHessianModel.M2) k j)
  exact Finset.measurable_sum _ (fun k _ => (ha i k).mul (hb k j))

def cycleWord (p : Triple × SU2) : SU2 := p.1.1*p.1.2.1*p.1.2.2*p.2

private theorem cycleWord_measurable : Measurable cycleWord := by
  letI : MeasurableMul₂ SU2 := ⟨joint_mul_measurable⟩
  have hA : Measurable (fun p : Triple × SU2 => p.1.1) := measurable_fst.comp measurable_fst
  have hB : Measurable (fun p : Triple × SU2 => p.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hC : Measurable (fun p : Triple × SU2 => p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  exact ((hA.mul hB).mul hC).mul measurable_snd

private theorem cycle_pair_integrable (F : SU2 → ℝ) (hF : Measurable F)
    (M N : ℝ) (hM : 0 ≤ M) (hbF : ∀ W, |F W| ≤ M)
    (g : Triple → ℝ) (hg : Measurable g) (hbg : ∀ x, |g x| ≤ N) :
    Integrable (fun p : Triple × SU2 => F (cycleWord p)*g p.1) (tripleLaw.prod law) := by
  letI : IsProbabilityMeasure tripleLaw := by unfold tripleLaw; infer_instance
  apply Integrable.of_bound ((hF.comp cycleWord_measurable).mul
    (hg.comp measurable_fst)).aestronglyMeasurable (M*N)
  filter_upwards with p
  change ‖F (cycleWord p)*g p.1‖ ≤ M*N
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  exact mul_le_mul (hbF _) (hbg _) (abs_nonneg _) hM

theorem cycle_missing_edge_pairing_zero (F : SU2 → ℝ) (hF : Measurable F)
    (hclass : ∀ g W, F (g*W*g⁻¹)=F W) (hzero : (∫ W, F W ∂law)=0)
    (M N : ℝ) (hM : 0 ≤ M) (hbF : ∀ W, |F W| ≤ M)
    (g : Triple → ℝ) (hg : Measurable g) (hbg : ∀ x, |g x| ≤ N) :
    (∫ p : Triple × SU2, F (cycleWord p)*g p.1 ∂tripleLaw.prod law)=0 := by
  letI : IsProbabilityMeasure tripleLaw := by unfold tripleLaw; infer_instance
  rw [integral_prod _ (cycle_pair_integrable F hF M N hM hbF g hg hbg)]
  have hz (x : Triple) : (∫ D, F (cycleWord (x,D))*g x ∂law)=0 := by
    rw [integral_mul_const]
    have he := class_sandwich_integral F hclass (x.1*x.2.1*x.2.2) 1
    simp only [mul_one] at he
    change (∫ D, F (x.1*x.2.1*x.2.2*D) ∂law)*g x=0
    rw [he,hzero,zero_mul]
  simp only [hz,integral_zero]
end OperatorDerivativeRewrite.Foundation.SU2ForestCycleReduction

namespace OperatorDerivativeRewrite.Foundation.SU2ForestCycleReduction
open QuaternionSU2Representation SU2OpenLinkGaugeObstruction

theorem boundary_fixed_path_obstruction :
    ∃ f : SU2 → SU2 → ℝ,
      (∀ g A B, f (A*g⁻¹) (g*B)=f A B) ∧
      f SU2StapleExtremes.minusOne 1 ≠ f 1 1 := by
  refine ⟨closedPairTrace,?_,closedPairTrace_nonconstant⟩
  intro g A B
  simpa only [one_mul,inv_one,mul_one] using closedPairTrace_gauge 1 g A B
end OperatorDerivativeRewrite.Foundation.SU2ForestCycleReduction

