import Foundation.CauchyPoissonCoreGenerator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.LinearPMap
/-! Actual closed circle generator: right norm tangents are equivalent to
integrated semigroup orbits. The graph is an intersection of bounded linear
kernels, with its exact partial-linear-operator domain. Density, finite graph-core
equality and resolvent surjectivity are not asserted. -/
noncomputable section
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonGeneratorDomain
open CauchyPoissonFeller CauchyPoissonConcentration CauchyPoissonCoreGenerator

theorem orbit_continuous (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) : Continuous (orbit q hq f) := by
  exact (operator_strong_continuity q hq f).comp
    (show Continuous (fun t : ℝ => (⟨max t 0,le_max_right _ _⟩ : {t : ℝ // 0 ≤ t})) by fun_prop)

theorem orbit_add (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    orbit q hq f (s+t) = operator q s hq hs (orbit q hq f t) := by
  simp only [orbit,max_eq_left hs,max_eq_left ht,max_eq_left (add_nonneg hs ht)]
  rw [operator_add q s t hq hs ht]
  rfl

def Tangent (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ)) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (orbit q hq f t-f)) (𝓝[Ioi 0] 0) (𝓝 g)

theorem tangent_propagates (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : Tangent q hq f g) (s : ℝ) (hs : 0 ≤ s) :
    HasDerivWithinAt (orbit q hq f) (orbit q hq g s) (Ioi s) s := by
  have hsub : Tendsto (fun u : ℝ => u-s) (𝓝[Ioi s] s) (𝓝[Ioi 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h0 : Tendsto (fun u : ℝ => u-s) (𝓝 s) (𝓝 0) := by
        simpa using (show Continuous (fun u : ℝ => u-s) by fun_prop).tendsto s
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change s < u at hu
      exact sub_pos.mpr hu
  have hc := ((operator q s hq hs).restrictScalars ℝ).continuous.tendsto g |>.comp (h.comp hsub)
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  have he : operator q s hq hs g = orbit q hq g s := by simp only [orbit,max_eq_left hs]
  change Tendsto (fun u => (operator q s hq hs).restrictScalars ℝ ((u-s)⁻¹ • (orbit q hq f (u-s)-f)))
    (𝓝[Ioi s] s) (𝓝 (operator q s hq hs g)) at hc
  rw [he] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  change (operator q s hq hs).restrictScalars ℝ ((u-s)⁻¹ • (orbit q hq f (u-s)-f)) =
    (u-s)⁻¹ • (orbit q hq f u-orbit q hq f s)
  rw [map_smul,map_sub]
  congr 1
  have ha := orbit_add q hq f s (u-s) hs (sub_nonneg.mpr hu.le)
  have hb : operator q s hq hs f = orbit q hq f s := by simp only [orbit,max_eq_left hs]
  change operator q s hq hs (orbit q hq f (u-s))-operator q s hq hs f = _
  rw [hb,← ha]
  congr 2
  ring

def Integrated (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ)) : Prop :=
  ∀ t : ℝ, 0 ≤ t → orbit q hq f t-f = ∫ s in (0:ℝ)..t, orbit q hq g s

theorem tangent_integrated (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : Tangent q hq f g) : Integrated q hq f g := by
  intro t ht
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (orbit_continuous q hq f).continuousOn
    (fun s hs => tangent_propagates q hq f g h s hs.1.le)
    ((orbit_continuous q hq g).intervalIntegrable 0 t)
  simpa only [orbit_zero] using hi.symm

theorem integrated_tangent (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : Integrated q hq f g) : Tangent q hq f g := by
  have hd : HasDerivAt (fun t => ∫ s in (0:ℝ)..t, orbit q hq g s) g 0 := by
    simpa only [orbit_zero] using intervalIntegral.integral_hasDerivAt_right
      ((orbit_continuous q hq g).intervalIntegrable 0 0)
      (orbit_continuous q hq g).stronglyMeasurable.stronglyMeasurableAtFilter
      (orbit_continuous q hq g).continuousAt
  have hl := hd.tendsto_slope_zero_right
  simp only [zero_add,intervalIntegral.integral_same,sub_zero] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [h t ht.le]

theorem tangent_iff_integrated (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ)) :
    Tangent q hq f g ↔ Integrated q hq f g :=
  ⟨tangent_integrated q hq f g,integrated_tangent q hq f g⟩

def integralOperator (q : ℝ) (hq : |q| < 1) (t : ℝ) : C(Circle,ℂ) →L[ℂ] C(Circle,ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ s in (0:ℝ)..t, orbit q hq g s
      map_add' := by
        intro f g
        simp only [orbit,map_add]
        exact intervalIntegral.integral_add ((orbit_continuous q hq f).intervalIntegrable 0 t)
          ((orbit_continuous q hq g).intervalIntegrable 0 t)
      map_smul' := by
        intro c g
        simp only [orbit,map_smul]
        exact intervalIntegral.integral_smul c _ }
    |t| (fun g => by
      change ‖∫ s in (0:ℝ)..t, orbit q hq g s‖ ≤ |t| * ‖g‖
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := t) (fun s _ => orbit_contraction q hq g s)
      simpa only [sub_zero,mul_comm] using h)

def defect (q : ℝ) (hq : |q| < 1) (t : ℝ) (ht : 0 ≤ t) :
    (C(Circle,ℂ) × C(Circle,ℂ)) →L[ℂ] C(Circle,ℂ) :=
  (operator q t hq ht).comp (ContinuousLinearMap.fst ℂ _ _) -
    ContinuousLinearMap.fst ℂ _ _ -
    (integralOperator q hq t).comp (ContinuousLinearMap.snd ℂ _ _)

def graph (q : ℝ) (hq : |q| < 1) : Submodule ℂ (C(Circle,ℂ) × C(Circle,ℂ)) :=
  ⨅ t : ℝ, ⨅ ht : 0 ≤ t, (defect q hq t ht).ker

theorem graph_iff (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ)) :
    (f,g) ∈ graph q hq ↔ Integrated q hq f g := by
  simp only [graph,Submodule.mem_iInf,LinearMap.mem_ker]
  change (∀ t ht, operator q t hq ht f-f-(∫ s in (0:ℝ)..t, orbit q hq g s) = 0) ↔ _
  simp only [sub_eq_zero]
  constructor
  · intro h t ht
    simpa only [orbit,max_eq_left ht] using h t ht
  · intro h t ht
    simpa only [orbit,max_eq_left ht] using h t ht

theorem graph_closed (q : ℝ) (hq : |q| < 1) :
    IsClosed (graph q hq : Set (C(Circle,ℂ) × C(Circle,ℂ))) := by
  simp only [graph,Submodule.coe_iInf]
  exact isClosed_iInter (fun t => isClosed_iInter (fun ht => (defect q hq t ht).isClosed_ker))

theorem graph_tangent_iff (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ)) :
    (f,g) ∈ graph q hq ↔ Tangent q hq f g := by
  rw [graph_iff,tangent_iff_integrated]

theorem vertical_zero (q : ℝ) (hq : |q| < 1) (z : C(Circle,ℂ) × C(Circle,ℂ))
    (hz : z ∈ graph q hq) (h0 : z.1 = 0) : z.2 = 0 := by
  have h := (graph_tangent_iff q hq z.1 z.2).mp hz
  rw [h0] at h
  simp only [Tangent,orbit,map_zero,sub_zero,smul_zero] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

def generator (q : ℝ) (hq : |q| < 1) : C(Circle,ℂ) →ₗ.[ℂ] C(Circle,ℂ) :=
  (graph q hq).toLinearPMap

theorem generator_graph (q : ℝ) (hq : |q| < 1) : (generator q hq).graph = graph q hq :=
  (graph q hq).toLinearPMap_graph_eq (vertical_zero q hq)

theorem generator_closed (q : ℝ) (hq : |q| < 1) : (generator q hq).IsClosed := by
  change IsClosed ((generator q hq).graph : Set (C(Circle,ℂ) × C(Circle,ℂ)))
  rw [generator_graph]
  exact graph_closed q hq

theorem domain_iff (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) :
    f ∈ (generator q hq).domain ↔ ∃ g, Tangent q hq f g := by
  rw [LinearPMap.mem_domain_iff,generator_graph]
  simp only [graph_tangent_iff]

theorem finite_core_graph (q : ℝ) (hq : |q| < 1) (N : ℕ) (a b : Fin N → ℂ) :
    (coreValue N a b,coreGenerator q N a b) ∈ (generator q hq).graph := by
  rw [generator_graph,graph_tangent_iff]
  exact core_tangent q hq N a b

theorem generator_graph_iff (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ)) :
    (f,g) ∈ (generator q hq).graph ↔ Tangent q hq f g := by
  rw [generator_graph,graph_tangent_iff]

theorem graph_resolvent_bound (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) (r : ℝ) (hr : 0 < r) :
    r*‖f‖ ≤ ‖r • f-g‖ :=
  ContractionTangentDissipativity.norm_resolvent_bound (orbit q hq f) f g
    (fun t _ => orbit_contraction q hq f t) ((generator_graph_iff q hq f g).mp h) r hr

theorem graph_value_unique (q : ℝ) (hq : |q| < 1) (f g h : C(Circle,ℂ))
    (hg : (f,g) ∈ (generator q hq).graph) (hh : (f,h) ∈ (generator q hq).graph) : g=h :=
  tendsto_nhds_unique ((generator_graph_iff q hq f g).mp hg) ((generator_graph_iff q hq f h).mp hh)

end OperatorDerivativeRewrite.Foundation.CauchyPoissonGeneratorDomain
