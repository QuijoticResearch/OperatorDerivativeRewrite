import Foundation.FourierPathDirectionalSeries
import Foundation.ContractionTangentDissipativity
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! A densely defined genuine path derivative in every continuous direction. -/
noncomputable section
open Filter
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathDirectionalOperator
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierTranslations HigherHeatFourierTranslationContinuity
open FourierPathDirectionalCharacters FourierPathDirectionalSeries

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def coefficientGraph (h : Path) : Submodule ℂ (Coeff × Coeff) where
  carrier := {z | ∀ i, z.2 i=z.1 i*eigenvalue (frequency levels ξ h i)}
  zero_mem' := by intro i; change 0=0*_; rw [zero_mul]
  add_mem' := by
    intro z w hz hw i
    change z.2 i+w.2 i=(z.1 i+w.1 i)*_
    rw [hz i, hw i, add_mul]
  smul_mem' := by
    intro c z hz i
    change c*z.2 i=(c*z.1 i)*_
    rw [hz i, mul_assoc]

def quotientPair : (Coeff × Coeff) →L[ℂ] (TestSpace levels ξ × TestSpace levels ξ) :=
  ((kernel levels ξ).mkQL.comp (ContinuousLinearMap.fst ℂ Coeff Coeff)).prod
    ((kernel levels ξ).mkQL.comp (ContinuousLinearMap.snd ℂ Coeff Coeff))

def graph (h : Path) : Submodule ℂ (TestSpace levels ξ × TestSpace levels ξ) :=
  (coefficientGraph levels ξ h).map (quotientPair levels ξ).toLinearMap

theorem graph_deriv (h : Path) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ h) :
    HasDerivAt (fun t => along levels ξ h t z.1) z.2 0 := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := hz
  exact along_hasDerivAt levels ξ h a b hab

theorem graph_vertical_zero (h : Path) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ h) (h0 : z.1=0) : z.2=0 := by
  have hd := graph_deriv levels ξ h z hz
  simp only [h0, map_zero] at hd
  exact hd.unique (hasDerivAt_const 0 0)

def operator (h : Path) : TestSpace levels ξ →ₗ.[ℂ] TestSpace levels ξ :=
  (graph levels ξ h).toLinearPMap

theorem operator_graph (h : Path) : (operator levels ξ h).graph=graph levels ξ h :=
  (graph levels ξ h).toLinearPMap_graph_eq (graph_vertical_zero levels ξ h)

theorem generator_mem_graph (h : Path) (i : ℕ) :
    (generator levels ξ i, eigenvalue (frequency levels ξ h i) • generator levels ξ i) ∈
      graph levels ξ h := by
  let a : Coeff := lp.single 1 i (1:ℂ)
  let c := eigenvalue (frequency levels ξ h i)
  refine ⟨(a,c • a), ?_, ?_⟩
  · intro j
    change c*a j=a j*eigenvalue (frequency levels ξ h j)
    classical
    by_cases hj : j=i
    · subst j
      change c*(lp.single 1 i (1:ℂ) : Coeff) i=_
      rw [lp.coeFn_single, Pi.single_eq_same]
      exact mul_comm _ _
    · change c*(lp.single 1 i (1:ℂ) : Coeff) j=
        (lp.single 1 i (1:ℂ) : Coeff) j*_
      rw [lp.coeFn_single, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · change ((kernel levels ξ).mkQL a,(kernel levels ξ).mkQL (c • a))=_
    rw [map_smul]
    rfl

theorem domain_dense (h : Path) :
    Dense ((operator levels ξ h).domain : Set (TestSpace levels ξ)) := by
  apply (finite_core_dense levels ξ).mono
  have hs : Submodule.span ℂ (Set.range (generator levels ξ)) ≤ (operator levels ξ h).domain := by
    apply Submodule.span_le.mpr
    rintro q ⟨i,rfl⟩
    apply LinearPMap.mem_domain_iff.mpr
    refine ⟨eigenvalue (frequency levels ξ h i) • generator levels ξ i, ?_⟩
    rw [operator_graph]
    exact generator_mem_graph levels ξ h i
  exact hs

theorem operator_deriv (h : Path) (q : (operator levels ξ h).domain) :
    HasDerivAt (fun t => along levels ξ h t (q:TestSpace levels ξ))
      (operator levels ξ h q) 0 := by
  have hg := (operator levels ξ h).mem_graph q
  rw [operator_graph] at hg
  exact graph_deriv levels ξ h _ hg

theorem graph_bound (h : Path) (c : ℝ) (hc : 0 < c)
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ h) :
    c*‖z.1‖ ≤ ‖c • z.1-z.2‖ := by
  have ht := (graph_deriv levels ξ h z hz).tendsto_slope_zero_right
  simp only [zero_add, along_zero] at ht
  exact ContractionTangentDissipativity.norm_resolvent_bound
    (fun t => along levels ξ h t z.1) z.1 z.2
    (fun t _ => (along_norm levels ξ h t z.1).le) ht c hc

end OperatorDerivativeRewrite.Foundation.FourierPathDirectionalOperator
