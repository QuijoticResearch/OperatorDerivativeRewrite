import Foundation.CauchyPoissonOrbitRegularization
open Complex MeasureTheory Filter Set
open scoped Topology
/-! Exact graph-core identification from time-averaged finite Fourier inputs.
Closure is in the product supremum norm. The unsmoothed Fourier core and
resolvent range are not identified here. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonSmoothedCore
open CauchyPoissonFeller CauchyPoissonCoreGenerator CauchyPoissonGeneratorDomain
open CauchyPoissonDomainDensity CauchyPoissonOrbitRegularization

def fourierCore : Submodule ℂ C(Circle,ℂ) :=
  (Submodule.span ℂ (range (fourier (T := (1:ℝ))))).map transport.toLinearMap

theorem fourierCore_dense : Dense (fourierCore : Set C(Circle,ℂ)) := by
  intro f
  obtain ⟨u,hu⟩ := transport_surjective f
  have hd : closure ((Submodule.span ℂ (range (fourier (T := (1:ℝ))))) : Set C(AddCircle (1:ℝ),ℂ)) = univ := by
    rw [← Submodule.topologicalClosure_coe,span_fourier_closure_eq_top]
    rfl
  change f ∈ closure (transport '' ((Submodule.span ℂ (range (fourier (T := (1:ℝ))))) : Set C(AddCircle (1:ℝ),ℂ)))
  apply image_closure_subset_closure_image transport_continuous
  exact ⟨u,by rw [hd]; trivial,hu⟩

def regularizedPair (q : ℝ) (hq : |q| < 1) (T : ℝ) (f : C(Circle,ℂ)) :
    C(Circle,ℂ) × C(Circle,ℂ) :=
  (T⁻¹ • integralOperator q hq T f,T⁻¹ • (orbit q hq f T-f))

theorem regularizedPair_continuous (q : ℝ) (hq : |q| < 1) (T : ℝ) :
    Continuous (regularizedPair q hq T) := by
  apply Continuous.prodMk
  · exact (integralOperator q hq T).continuous.const_smul (T⁻¹)
  · change Continuous (fun f : C(Circle,ℂ) => T⁻¹ • (operator q (max T 0) hq (le_max_right _ _) f-f))
    exact (((operator q (max T 0) hq (le_max_right _ _)).continuous).sub continuous_id).const_smul (T⁻¹)

def smoothedPairs (q : ℝ) (hq : |q| < 1) : Set (C(Circle,ℂ) × C(Circle,ℂ)) :=
  {z | ∃ T : ℝ, 0 < T ∧ ∃ f ∈ fourierCore, z = regularizedPair q hq T f}

theorem smoothedPairs_subset_graph (q : ℝ) (hq : |q| < 1) :
    smoothedPairs q hq ⊆ (generator q hq).graph := by
  rintro z ⟨T,hT,f,hf,rfl⟩
  exact average_graph q hq f T hT.le

theorem regularizedPair_mem_closure (q : ℝ) (hq : |q| < 1) (T : ℝ) (hT : 0 < T)
    (f : C(Circle,ℂ)) : regularizedPair q hq T f ∈ closure (smoothedPairs q hq) := by
  have hi : regularizedPair q hq T f ∈ closure (regularizedPair q hq T '' (fourierCore : Set C(Circle,ℂ))) :=
    image_closure_subset_closure_image (regularizedPair_continuous q hq T) ⟨f,fourierCore_dense f,rfl⟩
  apply closure_mono (s := regularizedPair q hq T '' (fourierCore : Set C(Circle,ℂ))) _ hi
  rintro _ ⟨u,hu,rfl⟩
  exact ⟨T,hT,u,hu,rfl⟩

theorem smoothedPairs_closure (q : ℝ) (hq : |q| < 1) :
    closure (smoothedPairs q hq) = ((generator q hq).graph : Set (C(Circle,ℂ) × C(Circle,ℂ))) := by
  apply Set.Subset.antisymm
  · apply closure_minimal (smoothedPairs_subset_graph q hq)
    rw [generator_graph]
    exact graph_closed q hq
  · rintro ⟨f,g⟩ h
    apply isClosed_closure.mem_of_tendsto (graph_average_tendsto q hq f g h)
    filter_upwards [self_mem_nhdsWithin] with T hT
    exact regularizedPair_mem_closure q hq T hT f


def smoothedCoreGraph (q : ℝ) (hq : |q| < 1) : Submodule ℂ (C(Circle,ℂ) × C(Circle,ℂ)) :=
  Submodule.span ℂ (smoothedPairs q hq)

theorem smoothedCoreGraph_closure (q : ℝ) (hq : |q| < 1) :
    (smoothedCoreGraph q hq).topologicalClosure = (generator q hq).graph := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · exact Submodule.span_le.mpr (smoothedPairs_subset_graph q hq)
    · rw [generator_graph]
      exact graph_closed q hq
  · intro z hz
    change z ∈ closure (smoothedCoreGraph q hq : Set (C(Circle,ℂ) × C(Circle,ℂ)))
    apply closure_mono (s := smoothedPairs q hq) (fun _ h => Submodule.subset_span h)
    rwa [smoothedPairs_closure]

theorem graph_pair_approximation (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∃ u ∈ fourierCore, dist (f,g) (regularizedPair q hq T u) < ε := by
  have hc : (f,g) ∈ closure (smoothedPairs q hq) := by rwa [smoothedPairs_closure]
  obtain ⟨z,⟨T,hT,u,hu,rfl⟩,hz⟩ := Metric.mem_closure_iff.mp hc ε hε
  exact ⟨T,hT,u,hu,hz⟩

end OperatorDerivativeRewrite.Foundation.CauchyPoissonSmoothedCore
