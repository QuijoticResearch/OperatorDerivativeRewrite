import Foundation.FourierPathDirectionalFullGenerator
import Foundation.HigherHeatFourierPathSemigroup

/-! Domain-inclusive commutation of genuine path differentiation, translations and heat evolution. -/
noncomputable section
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.FourierPathDifferentialCommutation
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierTranslations HigherHeatFourierTranslationContinuity
open FourierPathDirectionalOperator FourierPathDirectionalFullGenerator

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem graph_map_of_commutes (h : Path)
    (S : TestSpace levels ξ →L[ℂ] TestSpace levels ξ)
    (hc : ∀ t q, along levels ξ h t (S q)=S (along levels ξ h t q))
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ h) :
    (S z.1,S z.2) ∈ graph levels ξ h := by
  have hd := (S.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (graph_deriv levels ξ h z hz)
  change HasDerivAt (fun t => S (along levels ξ h t z.1)) (S z.2) 0 at hd
  have he : (fun t => S (along levels ξ h t z.1))=(fun t => along levels ξ h t (S z.1)) := by
    funext t
    exact (hc t z.1).symm
  rw [he] at hd
  exact deriv_implies_graph levels ξ h _ _ hd

theorem translation_graph (h k : Path) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ h) :
    (translation levels ξ k z.1,translation levels ξ k z.2) ∈ graph levels ξ h := by
  apply graph_map_of_commutes levels ξ h (translation levels ξ k) ?_ z hz
  intro t q
  change translation levels ξ (scalePath t h) (translation levels ξ k q)=
    translation levels ξ k (translation levels ξ (scalePath t h) q)
  rw [translation_add, translation_add, addPath_comm (scalePath t h) k]

theorem heat_graph (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ h) :
    (HigherHeatFourierPathSemigroup.evolution levels ξ m hm T z.1,
      HigherHeatFourierPathSemigroup.evolution levels ξ m hm T z.2) ∈ graph levels ξ h := by
  apply graph_map_of_commutes levels ξ h
    (HigherHeatFourierPathSemigroup.evolution levels ξ m hm T) ?_ z hz
  intro t q
  exact (HigherHeatFourierPathSemigroup.evolution_translation levels ξ m hm T (scalePath t h) q).symm

theorem heat_domain (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (q : (operator levels ξ h).domain) :
    HigherHeatFourierPathSemigroup.evolution levels ξ m hm T (q:TestSpace levels ξ) ∈
      (operator levels ξ h).domain := by
  have hg := (operator levels ξ h).mem_graph q
  rw [operator_graph] at hg
  apply LinearPMap.mem_domain_iff.mpr
  refine ⟨HigherHeatFourierPathSemigroup.evolution levels ξ m hm T (operator levels ξ h q), ?_⟩
  rw [operator_graph]
  exact heat_graph levels ξ h m hm T _ hg

theorem heat_operator_apply (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (q : (operator levels ξ h).domain) :
    operator levels ξ h
      ⟨HigherHeatFourierPathSemigroup.evolution levels ξ m hm T (q:TestSpace levels ξ),
        heat_domain levels ξ h m hm T q⟩=
      HigherHeatFourierPathSemigroup.evolution levels ξ m hm T (operator levels ξ h q) := by
  have hg := (operator levels ξ h).mem_graph q
  rw [operator_graph] at hg
  have hs := heat_graph levels ξ h m hm T _ hg
  rw [← operator_graph] at hs
  exact (operator levels ξ h).mem_graph_snd_inj
    ((operator levels ξ h).mem_graph
      ⟨HigherHeatFourierPathSemigroup.evolution levels ξ m hm T (q:TestSpace levels ξ),
        heat_domain levels ξ h m hm T q⟩) hs rfl

end OperatorDerivativeRewrite.Foundation.FourierPathDifferentialCommutation
