import Foundation.CauchyPoissonObservableEntropy
/-! Actual forward probability-law evolution paired against the full closed
generator domain on continuous circle observables. The dual action is contractive
and weakly continuous; no strong continuity of the whole dual, density-adjoint
domain, reversibility or logarithmic Sobolev inequality is asserted. -/
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonForwardDual
open CauchyPoissonFeller CauchyPoissonCoreGenerator CauchyPoissonGeneratorDomain CauchyPoissonMarkovKernel CauchyPoissonObservableEntropy

def lawFunctional (μ : Measure Circle) [IsProbabilityMeasure μ] : C(Circle,ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ z, f z ∂μ
      map_add' := fun f g => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c (fun z => f z) }
    1 (fun f => by simpa using norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall f.norm_coe_le_norm))

theorem lawFunctional_norm (μ : Measure Circle) [IsProbabilityMeasure μ] : ‖lawFunctional μ‖ ≤ 1 := by
  apply (lawFunctional μ).opNorm_le_bound (by norm_num)
  intro f
  change ‖∫ z, f z ∂μ‖ ≤ 1*‖f‖
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall f.norm_coe_le_norm)

def dualOrbit (q : ℝ) (hq : |q| < 1) (φ : C(Circle,ℂ) →L[ℂ] ℂ) (t : ℝ) : C(Circle,ℂ) →L[ℂ] ℂ :=
  φ.comp (operator q (max t 0) hq (le_max_right _ _))

theorem dualOrbit_apply (q : ℝ) (hq : |q| < 1) (φ : C(Circle,ℂ) →L[ℂ] ℂ) (t : ℝ) (f : C(Circle,ℂ)) :
    dualOrbit q hq φ t f = φ (orbit q hq f t) := rfl

theorem dualOrbit_bound (q : ℝ) (hq : |q| < 1) (φ : C(Circle,ℂ) →L[ℂ] ℂ) (t : ℝ) :
    ‖dualOrbit q hq φ t‖ ≤ ‖φ‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    have hh := operator_contraction q (max t 0) hq (le_max_right _ _)
    calc
      ‖φ‖*‖operator q (max t 0) hq (le_max_right _ _)‖ ≤ ‖φ‖*1 := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
      _ = _ := mul_one _)

theorem dualOrbit_zero (q : ℝ) (hq : |q| < 1) (φ : C(Circle,ℂ) →L[ℂ] ℂ) : dualOrbit q hq φ 0 = φ := by
  ext f
  simp only [dualOrbit_apply,orbit_zero]

theorem dualOrbit_add (q : ℝ) (hq : |q| < 1) (φ : C(Circle,ℂ) →L[ℂ] ℂ)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    dualOrbit q hq φ (s+t) = dualOrbit q hq (dualOrbit q hq φ s) t := by
  ext f
  simp only [dualOrbit_apply]
  rw [orbit_add q hq f s t hs ht]
  simp only [orbit,max_eq_left hs]

theorem actual_law_duality (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (f : C(Circle,ℂ)) :
    (∫ z, f z ∂(kernel q t) ∘ₘ μ) = lawFunctional μ (orbit q hq f t) := by
  let := kernel_markov q t hq ht
  have hi : Integrable f (((kernel q t) ∘ₖ Kernel.const Unit μ) ()) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := Kernel.integral_comp hi
  change (∫ z, f z ∂(kernel q t) ∘ₘ μ) = ∫ x, (orbit q hq f t) x ∂μ
  simpa only [Kernel.comp_apply,Kernel.const_apply,orbit,max_eq_left ht,operator_apply] using hh

theorem weak_forward_derivative (q : ℝ) (hq : |q| < 1) (μ : Measure Circle) [IsProbabilityMeasure μ]
    (f g : C(Circle,ℂ)) (h : (f,g) ∈ (generator q hq).graph) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => ∫ z, f z ∂(kernel q u) ∘ₘ μ) (∫ z, g z ∂(kernel q t) ∘ₘ μ) t := by
  have hd := ((lawFunctional μ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (graph_orbit_derivative q hq f g h t ht)
  have he : (fun u => ∫ z, f z ∂(kernel q u) ∘ₘ μ) =ᶠ[𝓝 t] fun u => lawFunctional μ (orbit q hq f u) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact actual_law_duality q u hq hu.le μ f
  rw [actual_law_duality q t hq ht.le μ g]
  exact hd.congr_of_eventuallyEq he


theorem dualOrbit_weak_continuous (q : ℝ) (hq : |q| < 1)
    (φ : C(Circle,ℂ) →L[ℂ] ℂ) (f : C(Circle,ℂ)) :
    Continuous (fun t => dualOrbit q hq φ t f) :=
  φ.continuous.comp (orbit_continuous q hq f)

theorem weak_forward_integrated (q : ℝ) (hq : |q| < 1)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) (t : ℝ) (ht : 0 ≤ t) :
    (∫ z, f z ∂(kernel q t) ∘ₘ μ) - (∫ z, f z ∂μ) =
      ∫ u in (0:ℝ)..t, ∫ z, g z ∂(kernel q u) ∘ₘ μ := by
  have hh := tangent_integrated q hq f g ((generator_graph_iff q hq f g).mp h) t ht
  have hc := congrArg (lawFunctional μ) hh
  rw [map_sub] at hc
  rw [← (lawFunctional μ).intervalIntegral_comp_comm
    ((orbit_continuous q hq g).intervalIntegrable 0 t)] at hc
  rw [actual_law_duality q t hq ht μ f]
  change lawFunctional μ (orbit q hq f t) - lawFunctional μ f = _
  rw [hc]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le ht] at hu
  exact (actual_law_duality q u hq hu.1 μ g).symm

end OperatorDerivativeRewrite.Foundation.CauchyPoissonForwardDual
