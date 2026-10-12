import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! Closed partial operators acting in the fibers of Bochner L2.
The graph is specified almost everywhere by the ORIGINAL operator graph.
No density, core, or measurable selection of derivative values is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BochnerClosedOperator
variable {X E F : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def fiberGraph (T : E →ₗ.[ℝ] F) : Submodule ℝ (Lp E 2 μ × Lp F 2 μ) where
  carrier := {z | ∀ᵐ x ∂μ, (z.1 x, z.2 x) ∈ T.graph}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero E 2 μ, Lp.coeFn_zero F 2 μ] with x hx hy
    change ((0 : Lp E 2 μ) x, (0 : Lp F 2 μ) x) ∈ T.graph
    rw [hx, hy]
    exact T.graph.zero_mem
  add_mem' := by
    intro z w hz hw
    filter_upwards [hz, hw, Lp.coeFn_add z.1 w.1, Lp.coeFn_add z.2 w.2]
      with x hz hw hx hy
    change (((z.1 + w.1) x), ((z.2 + w.2) x)) ∈ T.graph
    simpa only [hx, hy, Pi.add_apply, Prod.mk_add_mk] using T.graph.add_mem hz hw
  smul_mem' := by
    intro c z hz
    filter_upwards [hz, Lp.coeFn_smul c z.1, Lp.coeFn_smul c z.2] with x hz hx hy
    change ((c • z.1) x, (c • z.2) x) ∈ T.graph
    simpa only [hx, hy, Pi.smul_apply, Prod.smul_mk] using T.graph.smul_mem c hz

theorem fiberGraph_singleValued (T : E →ₗ.[ℝ] F)
    (z : Lp E 2 μ × Lp F 2 μ) (hz : z ∈ fiberGraph μ T) (hzero : z.1 = 0) : z.2 = 0 := by
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero E 2 μ, Lp.coeFn_zero F 2 μ] with x hx he hf
  rw [hzero, he] at hx
  rw [hf]
  exact T.graph_fst_eq_zero_snd hx rfl

def lift (T : E →ₗ.[ℝ] F) : Lp E 2 μ →ₗ.[ℝ] Lp F 2 μ :=
  (fiberGraph μ T).toLinearPMap

theorem lift_graph (T : E →ₗ.[ℝ] F) : (lift μ T).graph = fiberGraph μ T :=
  Submodule.toLinearPMap_graph_eq _ (fiberGraph_singleValued μ T)

theorem mem_lift_graph_iff (T : E →ₗ.[ℝ] F) (u : Lp E 2 μ) (v : Lp F 2 μ) :
    (u, v) ∈ (lift μ T).graph ↔ ∀ᵐ x ∂μ, (u x, v x) ∈ T.graph := by
  rw [lift_graph]
  rfl

/-- The derivative values must form an actual Bochner L2 class, not just exist pointwise. -/
theorem mem_lift_domain_iff (T : E →ₗ.[ℝ] F) (u : Lp E 2 μ) :
    u ∈ (lift μ T).domain ↔ ∃ v : Lp F 2 μ, ∀ᵐ x ∂μ, (u x, v x) ∈ T.graph := by
  rw [LinearPMap.mem_domain_iff]
  simp only [mem_lift_graph_iff]

theorem fiberGraph_isClosed (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) :
    IsClosed (fiberGraph μ T : Set (Lp E 2 μ × Lp F 2 μ)) := by
  apply IsSeqClosed.isClosed
  intro z w hz hw
  obtain ⟨ns, hns, hn⟩ := (tendstoInMeasure_of_tendsto_Lp hw.fst_nhds).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hm⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hw.snd_nhds.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, ((z n).1 x, (z n).2 x) ∈ T.graph :=
    ae_all_iff.mpr hz
  filter_upwards [hn, hm, hall] with x hn hm hall
  exact hT.mem_of_tendsto ((hn.comp hms.tendsto_atTop).prodMk_nhds hm)
    (Eventually.of_forall fun n => hall (ns (ms n)))

/-- Closedness is proved by a common a.e. convergent subsequence of both graph coordinates. -/
theorem lift_isClosed (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) : (lift μ T).IsClosed := by
  change IsClosed ((lift μ T).graph : Set (Lp E 2 μ × Lp F 2 μ))
  rw [lift_graph]
  exact fiberGraph_isClosed μ T hT

theorem lift_value_ae (T : E →ₗ.[ℝ] F) (u : (lift μ T).domain) :
    ∀ᵐ x ∂μ, ((u : Lp E 2 μ) x, lift μ T u x) ∈ T.graph :=
  (mem_lift_graph_iff μ T _ _).mp ((lift μ T).mem_graph u)

/-- A genuine separated-variable L2 field, using Mathlib's continuous-map action. -/
def tensor (a : Lp ℝ 2 μ) (v : E) : Lp E 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).compLp a

theorem tensor_coeFn (a : Lp ℝ 2 μ) (v : E) :
    tensor μ a v =ᵐ[μ] fun x => a x • v :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).coeFn_compLp a

theorem tensor_graph (T : E →ₗ.[ℝ] F) (a : Lp ℝ 2 μ) (v : E) (w : F)
    (h : (v, w) ∈ T.graph) :
    (tensor μ a v, tensor μ a w) ∈ (lift μ T).graph := by
  rw [mem_lift_graph_iff]
  filter_upwards [tensor_coeFn μ a v, tensor_coeFn μ a w] with x hv hw
  rw [hv, hw]
  exact T.graph.smul_mem (a x) h

theorem tensor_continuous (a : Lp ℝ 2 μ) : Continuous (tensor μ a : E → Lp E 2 μ) := by
  let L : E →L[ℝ] Lp E 2 μ :=
    ((ContinuousLinearMap.lsmul ℝ ℝ).flip.compLpL₂ 2 μ).flip a
  have he : (tensor μ a : E → Lp E 2 μ) = L := by
    funext v
    apply Lp.ext
    filter_upwards [tensor_coeFn μ a v,
      ((ContinuousLinearMap.lsmul ℝ ℝ).flip v).coeFn_compLp a] with x hx hy
    exact hx.trans hy.symm
  rw [he]
  exact L.continuous

/-- This is ambient domain density, not a claim that any chosen core is graph dense. -/
theorem lift_dense_domain (T : E →ₗ.[ℝ] F) (hT : Dense (T.domain : Set E)) :
    Dense ((lift μ T).domain : Set (Lp E 2 μ)) := by
  let C := (lift μ T).domain.topologicalClosure
  have hC : ∀ u : Lp E 2 μ, u ∈ C := by
    apply Lp.induction (by simp) (fun u => u ∈ C)
    · intro v s hs hfin
      change indicatorConstLp 2 hs hfin.ne v ∈ C
      rw [indicatorConstLp_eq_toSpanSingleton_compLp]
      change tensor μ (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) v ∈ C
      refine hT.induction (fun x hx => ?_)
        ((lift μ T).domain.isClosed_topologicalClosure.preimage (tensor_continuous μ _)) v
      exact (lift μ T).domain.le_topologicalClosure
        (LinearPMap.mem_domain_iff.mpr ⟨tensor μ _ (T ⟨x, hx⟩),
          tensor_graph μ T _ _ _ (T.mem_graph ⟨x, hx⟩)⟩)
    · intro f g hf hg hd hfc hgc
      exact C.add_mem hfc hgc
    · exact (lift μ T).domain.isClosed_topologicalClosure
  exact fun u => hC u

end OperatorDerivativeRewrite.Foundation.BochnerClosedOperator
