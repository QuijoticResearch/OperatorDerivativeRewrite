import Foundation.HigherHeatFourierPathFullGenerator

/-! Finite Fourier eigenpairs form an actual graph core for the path heat generator. -/
noncomputable section
open Filter
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathGraphCore
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatFourierBanach
open HigherHeatFourierPathDerivative HigherHeatFourierPathGenerator
open HigherHeatFourierPathFullGenerator

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def eigenPair (m : ℕ) (i : ℕ) : TestSpace levels ξ × TestSpace levels ξ :=
  (generator levels ξ i, ((-rate levels ξ m i : ℝ) : ℂ) • generator levels ξ i)

def finiteGraph (m : ℕ) : Submodule ℂ (TestSpace levels ξ × TestSpace levels ξ) :=
  Submodule.span ℂ (Set.range (eigenPair levels ξ m))

theorem finiteGraph_le (m : ℕ) : finiteGraph levels ξ m ≤ graph levels ξ m := by
  apply Submodule.span_le.mpr
  rintro z ⟨i,rfl⟩
  exact generator_mem_graph levels ξ m i

theorem partial_pairs_tendsto (m : ℕ) (a b : Coeff)
    (hab : ∀ i, b i = a i * ((-rate levels ξ m i : ℝ) : ℂ)) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, a i • eigenPair levels ξ m i) atTop
      (𝓝 ((kernel levels ξ).mkQ a, (kernel levels ξ).mkQ b)) := by
  have ht := (partial_sums_tendsto levels ξ a).prodMk_nhds (partial_sums_tendsto levels ξ b)
  have he (n : ℕ) : (∑ i ∈ Finset.range n, a i • eigenPair levels ξ m i)=
      (∑ i ∈ Finset.range n, a i • generator levels ξ i,
        ∑ i ∈ Finset.range n, b i • generator levels ξ i) := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Prod.smul_fst, eigenPair]
    · simp only [Prod.snd_sum, Prod.smul_snd, eigenPair, ← smul_smul, hab]
  simpa only [← he] using ht

theorem graph_mem_closure_finite (m : ℕ) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ m) : z ∈ (finiteGraph levels ξ m).topologicalClosure := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := hz
  apply mem_closure_of_tendsto (partial_pairs_tendsto levels ξ m a b hab)
  exact Eventually.of_forall fun n => Submodule.sum_mem _ (fun i hi =>
    Submodule.smul_mem _ (a i) (Submodule.subset_span ⟨i,rfl⟩))

theorem graph_core (m : ℕ) (hm : 0 < m) :
    (finiteGraph levels ξ m).topologicalClosure=graph levels ξ m := by
  apply le_antisymm
  · exact (finiteGraph levels ξ m).topologicalClosure_minimal (finiteGraph_le levels ξ m)
      (graph_closed levels ξ m hm)
  · exact graph_mem_closure_finite levels ξ m

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathGraphCore
