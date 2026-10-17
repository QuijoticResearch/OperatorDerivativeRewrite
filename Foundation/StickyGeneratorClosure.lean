import Foundation.StickyFlatTestDomain
import Foundation.StickyGeneratorLinearGraph
import Foundation.AdjointClosure

/-! A genuine densely defined closable C0 operator from the verified sticky
differential relation. No range condition or semigroup identification is assumed. -/
noncomputable section
open Set
open scoped NNReal Topology ZeroAtInfty
namespace OperatorDerivativeRewrite.Foundation.StickyGeneratorClosure
open StickyGeneratorRelation StickyGeneratorLinearGraph
set_option backward.isDefEq.respectTransparency false

theorem zero_pair (κ : ℝ≥0) : Admissible κ (0 : C₀(ℝ, ℝ)) 0 := by
  simpa only [zero_smul] using smul (concrete_pair κ) 0

def relation (κ : ℝ≥0) : Submodule ℝ (C₀(ℝ, ℝ) × C₀(ℝ, ℝ)) where
  carrier := {z | Admissible κ z.1 z.2}
  zero_mem' := zero_pair κ
  add_mem' := fun h h' => add h h'
  smul_mem' := fun c _ h => smul h c

theorem vertical_zero (κ : ℝ≥0) (z : C₀(ℝ, ℝ) × C₀(ℝ, ℝ))
    (hz : z ∈ relation κ) (h0 : z.1 = 0) : z.2 = 0 := by
  change Admissible κ z.1 z.2 at hz
  have h : Admissible κ 0 z.2 := by rw [h0] at hz; exact hz
  exact single_valued h (zero_pair κ)

def operator (κ : ℝ≥0) : C₀(ℝ, ℝ) →ₗ.[ℝ] C₀(ℝ, ℝ) := (relation κ).toLinearPMap

theorem operator_graph (κ : ℝ≥0) : (operator κ).graph = relation κ :=
  (relation κ).toLinearPMap_graph_eq (vertical_zero κ)

theorem closure_bound {κ : ℝ≥0} (hκ : 0 < κ) {q : ℝ} (hq : 0 < q)
    (z : C₀(ℝ, ℝ) × C₀(ℝ, ℝ)) (hz : z ∈ (relation κ).topologicalClosure) :
    q*‖z.1‖ ≤ ‖q • z.1-z.2‖ := by
  have h1 : Continuous (fun w : C₀(ℝ, ℝ) × C₀(ℝ, ℝ) => q*‖w.1‖) :=
    continuous_const.mul continuous_fst.norm
  have h2 : Continuous (fun w : C₀(ℝ, ℝ) × C₀(ℝ, ℝ) => ‖q • w.1-w.2‖) :=
    (((continuous_fst : Continuous (fun w : C₀(ℝ, ℝ) × C₀(ℝ, ℝ) => w.1)).const_smul q).sub
      continuous_snd).norm
  exact (closure_minimal (s := (relation κ : Set (C₀(ℝ, ℝ) × C₀(ℝ, ℝ))))
    (fun w hw => resolvent_norm_bound (κ := κ) hκ (F := w.1) (G := w.2) hw hq) (isClosed_le h1 h2)) hz

theorem closure_vertical_zero {κ : ℝ≥0} (hκ : 0 < κ)
    (y : C₀(ℝ, ℝ)) (hy : (0,y) ∈ (relation κ).topologicalClosure) : y = 0 := by
  have hb (f : C₀(ℝ, ℝ)) (hf : ∃ g, Admissible κ f g) : ‖f‖ ≤ ‖f-y‖ := by
    obtain ⟨g,hg⟩ := hf
    have hg' : (f,g) ∈ (relation κ).topologicalClosure :=
      (relation κ).le_topologicalClosure hg
    have hq (q : ℝ) (hq : 0 < q) : q*(‖f‖-‖f-y‖) ≤ ‖g‖ := by
      have hz := (relation κ).topologicalClosure.add_mem hg'
        ((relation κ).topologicalClosure.smul_mem q hy)
      have h := closure_bound hκ hq _ hz
      change q*‖f+q • (0 : C₀(ℝ, ℝ))‖ ≤ ‖q • (f+q • 0)-(g+q • y)‖ at h
      simp only [smul_zero,add_zero] at h
      have he : q • f-(g+q • y) = q • (f-y)-g := by
        simp only [smul_sub]
        abel
      rw [he] at h
      have ht := norm_sub_le (q • (f-y)) g
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hq] at ht
      nlinarith
    by_contra hn
    have hd : 0 < ‖f‖-‖f-y‖ := sub_pos.mpr (lt_of_not_ge hn)
    have hh := hq ((‖g‖+1)/(‖f‖-‖f-y‖)) (div_pos (by positivity) hd)
    rw [div_mul_cancel₀ _ (ne_of_gt hd)] at hh
    linarith
  have hd := StickyFlatTestDomain.domain_dense κ
  have hy' : ‖y‖ ≤ ‖y-y‖ :=
    (closure_minimal hb (isClosed_le continuous_norm
      (continuous_id.sub continuous_const).norm)) (hd y)
  simpa only [sub_self,norm_zero,norm_le_zero_iff] using hy'

theorem closable {κ : ℝ≥0} (hκ : 0 < κ) : (operator κ).IsClosable := by
  refine ⟨(relation κ).topologicalClosure.toLinearPMap,?_⟩
  rw [operator_graph]
  symm
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨f,g⟩ hz h0
  change f = 0 at h0
  subst f
  exact closure_vertical_zero hκ g hz

theorem domain_dense (κ : ℝ≥0) : Dense ((operator κ).domain : Set C₀(ℝ, ℝ)) := by
  apply (StickyFlatTestDomain.domain_dense κ).mono
  rintro f ⟨g,hg⟩
  change f ∈ (relation κ).map (LinearMap.fst ℝ C₀(ℝ, ℝ) C₀(ℝ, ℝ))
  exact ⟨(f,g),hg,rfl⟩

theorem closure_domain_dense (κ : ℝ≥0) : Dense ((operator κ).closure.domain : Set C₀(ℝ, ℝ)) :=
  (domain_dense κ).mono (operator κ).le_closure.1

theorem closed_closure {κ : ℝ≥0} (hκ : 0 < κ) : (operator κ).closure.IsClosed :=
  (closable hκ).closure_isClosed

end OperatorDerivativeRewrite.Foundation.StickyGeneratorClosure
