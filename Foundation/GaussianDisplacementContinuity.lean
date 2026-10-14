import Foundation.GaussianDisplacementGroup
import Foundation.PoissonExponentialTotal
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! Strong continuity of the actual reference-independent Gaussian displacement group. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianDisplacementContinuity
open GaussianCore GaussianCoherentIdentification GaussianDisplacementFromPoisson GaussianDisplacementGroup
open PoissonTiltSourceGauge PoissonTiltHellingerGeometry PoissonDifferenceOperators
open PoissonCoherentVectors PoissonCharlierHilbertBasis PoissonExponentialTotal

def coherentSpan : Submodule ℝ GaussianL2 := Submodule.span ℝ (Set.range gaussianRoot)

theorem scalar_root_relation (rate : ℝ≥0) (θ : ℝ) :
    scalar rate θ=Real.exp ((rate : ℝ)*(Real.exp (2*θ)-1)/2) • rootClass rate (2*θ) := by
  apply Lp.ext
  filter_upwards [(exponential_memLp rate θ).coeFn_toLp,rootClass_coeFn rate (2*θ),
    Lp.coeFn_smul (Real.exp ((rate : ℝ)*(Real.exp (2*θ)-1)/2)) (rootClass rate (2*θ))] with n hs hr hm
  change scalar rate θ n=exponential θ n at hs
  rw [hs,hm,Pi.smul_apply,hr,smul_eq_mul,rootDensity,exponential,← Real.exp_add]
  congr 1
  ring

theorem coherentSpan_closure : coherentSpan.topologicalClosure=⊤ := by
  let rate : ℝ≥0 := 1
  have hr : 0<rate := by norm_num [rate]
  let Q := gaussianTransfer rate hr
  have hs : exponentialSpan rate≤coherentSpan.topologicalClosure.comap Q.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro f ⟨θ,rfl⟩
    change Q (scalar rate θ)∈coherentSpan.topologicalClosure
    rw [scalar_root_relation,map_smul,transferred_root_identification]
    exact coherentSpan.topologicalClosure.smul_mem _
      (coherentSpan.le_topologicalClosure (Submodule.subset_span ⟨_,rfl⟩))
  have hc := (exponentialSpan rate).topologicalClosure_minimal hs
    (coherentSpan.isClosed_topologicalClosure.preimage Q.continuous)
  rw [exponentialSpan_closure rate hr] at hc
  apply eq_top_iff.mpr
  intro f hf
  have he := hc (show Q.symm f∈(⊤ : Submodule ℝ (ScalarL2 rate)) from trivial)
  change Q (Q.symm f)∈coherentSpan.topologicalClosure at he
  rwa [LinearIsometryEquiv.apply_symm_apply] at he

theorem displacement_coherent (rate : ℝ≥0) (hr : 0<rate) (θ e : ℝ) :
    gaussianDisplacement rate hr θ (gaussianRoot e)=gaussianRoot (displacement rate θ+e) := by
  obtain ⟨rate',hr',θ',he⟩ := exists_positive_reference_displacement e
  rw [← he,← displacement_vacuum_physical rate' hr' θ',composed_vacuum_physical]

theorem gaussianRoot_distance_sq (a b : ℝ) :
    ‖gaussianRoot a-gaussianRoot b‖^2=2*(1-Real.exp (-(a-b)^2/2)) := by
  rw [norm_sub_sq_real,gaussianRoot_norm,gaussianRoot_norm,gaussianRoot_inner]
  ring

theorem gaussianRoot_continuous : Continuous gaussianRoot := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun x : ℝ => 2*(1-Real.exp (-(x-a)^2/2))) := by fun_prop
  have ht : Tendsto (fun x => ‖gaussianRoot x-gaussianRoot a‖^2) (𝓝 a) (𝓝 (0 : ℝ)) := by
    simpa [gaussianRoot_distance_sq] using hc.tendsto a
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp ht

theorem strong_tendsto_zero {I : Type*} (l : Filter I) (rate : I → ℝ≥0) (hr : ∀ i,0<rate i)
    (θ : I → ℝ) (hd : Tendsto (fun i => displacement (rate i) (θ i)) l (𝓝 0)) (f : GaussianL2) :
    Tendsto (fun i => gaussianDisplacement (rate i) (hr i) (θ i) f) l (𝓝 f) := by
  let U (i : I) := gaussianDisplacement (rate i) (hr i) (θ i)
  let S : Submodule ℝ GaussianL2 := {
    carrier := {g | Tendsto (fun i => U i g) l (𝓝 g)}
    zero_mem' := by
      change Tendsto (fun i => U i 0) l (𝓝 0)
      simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : I => (0 : GaussianL2)) l (𝓝 0))
    add_mem' := by
      intro g h hg hh
      change Tendsto (fun i => U i (g+h)) l (𝓝 (g+h))
      simpa only [map_add] using hg.add hh
    smul_mem' := by
      intro c g hg
      change Tendsto (fun i => U i (c • g)) l (𝓝 (c • g))
      simpa only [map_smul] using hg.const_smul c }
  have hs : coherentSpan≤S := by
    apply Submodule.span_le.mpr
    rintro g ⟨e,rfl⟩
    change Tendsto (fun i => gaussianDisplacement (rate i) (hr i) (θ i) (gaussianRoot e)) l (𝓝 (gaussianRoot e))
    simp_rw [displacement_coherent]
    have ht := gaussianRoot_continuous.continuousAt.tendsto.comp (hd.add_const e)
    simpa only [zero_add,Function.comp_def] using ht
  have he : EquicontinuousAt (fun i : I => fun g : GaussianL2 => U i g) f := by
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    refine ⟨ε,hε,?_⟩
    intro g hg i
    rw [(U i).isometry.dist_eq,dist_comm]
    exact hg
  have hc : f∈closure (coherentSpan : Set GaussianL2) := by
    change f∈coherentSpan.topologicalClosure
    rw [coherentSpan_closure]
    trivial
  have ht : Tendsto (fun g : GaussianL2 => g) (𝓝[coherentSpan] f) (𝓝 f) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  exact he.tendsto_of_mem_closure ht (fun g hg => hs hg) hc

theorem strong_tendsto {I : Type*} (l : Filter I) (rate : I → ℝ≥0) (hr : ∀ i,0<rate i)
    (θ : I → ℝ) (rate' : ℝ≥0) (hr' : 0<rate') (θ' : ℝ)
    (hd : Tendsto (fun i => displacement (rate i) (θ i)) l (𝓝 (displacement rate' θ'))) (f : GaussianL2) :
    Tendsto (fun i => gaussianDisplacement (rate i) (hr i) (θ i) f) l
      (𝓝 (gaussianDisplacement rate' hr' θ' f)) := by
  choose r hR η hη using fun i : I => exists_positive_reference_displacement
    (displacement (rate i) (θ i)-displacement rate' θ')
  have ht : Tendsto (fun i => displacement (r i) (η i)) l (𝓝 0) := by
    simpa only [hη,sub_self] using hd.sub_const (displacement rate' θ')
  have hz := strong_tendsto_zero l r hR η ht f
  have hs := (gaussianDisplacement rate' hr' θ').continuous.continuousAt.tendsto.comp hz
  have he (i : I) : gaussianDisplacement rate' hr' θ' (gaussianDisplacement (r i) (hR i) (η i) f)=
      gaussianDisplacement (rate i) (hr i) (θ i) f := by
    have hg := displacement_group_law rate' hr' θ' (r i) (hR i) (η i) (rate i) (hr i) (θ i)
      (by rw [hη]; ring)
    exact congrArg (fun U : GaussianL2 ≃ₗᵢ[ℝ] GaussianL2 => U f) hg
  simpa only [Function.comp_def,he] using hs

theorem displacement_parameter_continuous (rate : ℝ≥0) (hr : 0<rate) (f : GaussianL2) :
    Continuous (fun θ : ℝ => gaussianDisplacement rate hr θ f) := by
  have hd : Continuous (fun θ : ℝ => displacement rate θ) := by
    simp_rw [displacement,← sqrtRate_eq_sqrt_tilted rate]
    unfold sqrtRate
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro θ
  exact strong_tendsto (𝓝 θ) (fun _ => rate) (fun _ => hr) id rate hr θ (hd.tendsto θ) f

end OperatorDerivativeRewrite.Foundation.GaussianDisplacementContinuity
