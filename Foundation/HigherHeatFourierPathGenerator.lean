import Foundation.HigherHeatFourierPathDerivative
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! A genuine densely defined path-space infinitesimal heat operator. -/
noncomputable section
open Filter
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathGenerator
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach HigherHeatFourierPathSemigroup HigherHeatFourierPathDerivative

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def derivativeCoeff (m : ℕ) (a : Coeff)
    (ha : Summable (fun i => ‖a i * ((-rate levels ξ m i : ℝ) : ℂ)‖)) : Coeff :=
  ⟨fun i => a i * ((-rate levels ξ m i : ℝ) : ℂ), memℓp_gen (by simpa using ha)⟩

def coefficientGraph (m : ℕ) : Submodule ℂ (Coeff × Coeff) where
  carrier := {z | ∀ i, z.2 i = z.1 i * ((-rate levels ξ m i : ℝ) : ℂ)}
  zero_mem' := by intro i; change 0 = 0 * _; rw [zero_mul]
  add_mem' := by
    intro z w hz hw i
    change z.2 i + w.2 i = (z.1 i + w.1 i) * _
    rw [hz i, hw i, add_mul]
  smul_mem' := by
    intro c z hz i
    change c * z.2 i = (c * z.1 i) * _
    rw [hz i, mul_assoc]

def quotientPair : (Coeff × Coeff) →L[ℂ] (TestSpace levels ξ × TestSpace levels ξ) :=
  ((kernel levels ξ).mkQL.comp (ContinuousLinearMap.fst ℂ Coeff Coeff)).prod
    ((kernel levels ξ).mkQL.comp (ContinuousLinearMap.snd ℂ Coeff Coeff))

def graph (m : ℕ) : Submodule ℂ (TestSpace levels ξ × TestSpace levels ξ) :=
  (coefficientGraph levels ξ m).map (quotientPair levels ξ).toLinearMap

theorem graph_limit (m : ℕ) (hm : 0 < m) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ m) :
    Tendsto (fun t : ℝ => t⁻¹ • (evolution levels ξ m hm t.toNNReal z.1-z.1))
      (𝓝[Set.Ioi 0] 0) (𝓝 z.2) := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := hz
  exact evolution_quotient_tendsto levels ξ m hm a b hab

theorem graph_vertical_zero (m : ℕ) (hm : 0 < m)
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ m)
    (h0 : z.1=0) : z.2=0 := by
  have ht := graph_limit levels ξ m hm z hz
  simp only [h0, map_zero, sub_self, smul_zero] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

def operator (m : ℕ) : TestSpace levels ξ →ₗ.[ℂ] TestSpace levels ξ :=
  (graph levels ξ m).toLinearPMap

theorem operator_graph (m : ℕ) (hm : 0 < m) :
    (operator levels ξ m).graph=graph levels ξ m :=
  (graph levels ξ m).toLinearPMap_graph_eq (graph_vertical_zero levels ξ m hm)

theorem weighted_mem_graph (m : ℕ) (a : Coeff)
    (ha : Summable (fun i => ‖a i * ((-rate levels ξ m i : ℝ) : ℂ)‖)) :
    ((kernel levels ξ).mkQ a, (kernel levels ξ).mkQ (derivativeCoeff levels ξ m a ha)) ∈
      graph levels ξ m := by
  exact ⟨(a, derivativeCoeff levels ξ m a ha), (fun _ => rfl), rfl⟩

theorem generator_mem_graph (m : ℕ) (i : ℕ) :
    (generator levels ξ i, ((-rate levels ξ m i : ℝ) : ℂ) • generator levels ξ i) ∈
      graph levels ξ m := by
  let a : Coeff := lp.single 1 i (1:ℂ)
  let c : ℂ := (-rate levels ξ m i : ℝ)
  refine ⟨(a,c • a), ?_, ?_⟩
  · intro j
    change c*a j = a j*((-rate levels ξ m j : ℝ) : ℂ)
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

theorem domain_dense (m : ℕ) (hm : 0 < m) :
    Dense ((operator levels ξ m).domain : Set (TestSpace levels ξ)) := by
  apply (finite_core_dense levels ξ).mono
  have hs : Submodule.span ℂ (Set.range (generator levels ξ)) ≤ (operator levels ξ m).domain := by
    apply Submodule.span_le.mpr
    rintro q ⟨i,rfl⟩
    apply LinearPMap.mem_domain_iff.mpr
    refine ⟨((-rate levels ξ m i : ℝ) : ℂ) • generator levels ξ i, ?_⟩
    rw [operator_graph levels ξ m hm]
    exact generator_mem_graph levels ξ m i
  exact hs

theorem operator_limit (m : ℕ) (hm : 0 < m) (q : (operator levels ξ m).domain) :
    Tendsto (fun t : ℝ => t⁻¹ • (evolution levels ξ m hm t.toNNReal (q:TestSpace levels ξ)-q))
      (𝓝[Set.Ioi 0] 0) (𝓝 (operator levels ξ m q)) := by
  have hg := (operator levels ξ m).mem_graph q
  rw [operator_graph levels ξ m hm] at hg
  exact graph_limit levels ξ m hm _ hg

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathGenerator
