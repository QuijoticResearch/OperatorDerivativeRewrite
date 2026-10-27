import Foundation.CauchyPoissonEntropyLimit
import Mathlib.Analysis.Calculus.ParametricIntegral
open Complex MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped Topology
/-! Backward-observable entropy on the actual closed generator domain.
Uniform positivity justifies dominated logarithmic differentiation. Jensen and
invariance give nonpositive production, without a diffusion chain rule or
a forward-density adjoint identification. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonObservableEntropy
open CauchyPoissonFeller CauchyPoissonCoreGenerator CauchyPoissonGeneratorDomain CauchyPoissonMarkovKernel

theorem graph_orbit_derivative (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (orbit q hq f) (orbit q hq g t) t := by
  have hi := tangent_integrated q hq f g ((generator_graph_iff q hq f g).mp h)
  have hd := intervalIntegral.integral_hasDerivAt_right
    ((orbit_continuous q hq g).intervalIntegrable 0 t)
    (orbit_continuous q hq g).stronglyMeasurable.stronglyMeasurableAtFilter
    (orbit_continuous q hq g).continuousAt
  have he : orbit q hq f =ᶠ[𝓝 t] fun u => f+∫ s in (0:ℝ)..u, orbit q hq g s := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact (sub_eq_iff_eq_add.mp (hi u hu.le)).trans (add_comm _ _)
  exact (hd.const_add f).congr_of_eventuallyEq he

theorem orbit_real_lower (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) (δ : ℝ)
    (hf : ∀ z, δ ≤ (f z).re) (t : ℝ) (z : Circle) : δ ≤ (orbit q hq f t z).re := by
  let := kernel_markov q (max t 0) hq (le_max_right _ _)
  change δ ≤ (∫ w, f w ∂kernel q (max t 0) z).re
  have he : (∫ w, f w ∂kernel q (max t 0) z).re = ∫ w, (f w).re ∂kernel q (max t 0) z :=
    (Complex.reCLM.integral_comp_comm (observable_integrable q (max t 0) hq (le_max_right _ _) f z)).symm
  rw [he]
  have hi := integral_mono (integrable_const δ)
    (Complex.reCLM.integrable_comp (observable_integrable q (max t 0) hq (le_max_right _ _) f z)) hf
  simpa using hi

theorem orbit_real_derivative (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) (t : ℝ) (ht : 0 < t) (z : Circle) :
    HasDerivAt (fun u => (orbit q hq f u z).re) (orbit q hq g t z).re t := by
  have hd := ((ContinuousMap.evalCLM ℝ z : C(Circle,ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt t (graph_orbit_derivative q hq f g h t ht))
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  simpa only [Function.comp_def,ContinuousMap.evalCLM_apply,Complex.reCLM_apply] using hr

theorem observable_entropy_derivative (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) (δ : ℝ) (hδ : 0 < δ) (hf : ∀ z, δ ≤ (f z).re)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => ∫ z, klFun (orbit q hq f u z).re ∂invariantLaw q)
      (∫ z, Real.log (orbit q hq f t z).re * (orbit q hq g t z).re ∂invariantLaw q) t := by
  let := invariantLaw_probability q hq
  have hpos : ∀ u z, 0 < (orbit q hq f u z).re := fun u z => hδ.trans_le (orbit_real_lower q hq f δ hf u z)
  have hlog : ContinuousOn (fun x : ℝ => ‖Real.log x‖) (Icc δ ‖f‖) :=
    (Real.continuousOn_log.mono (fun x hx => ne_of_gt (hδ.trans_le hx.1))).norm
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hlog
  have hbound : ∀ u z, ‖Real.log (orbit q hq f u z).re * (orbit q hq g u z).re‖ ≤ B*‖g‖ := by
    intro u z
    rw [norm_mul]
    apply mul_le_mul _ _ (norm_nonneg _) (le_trans (norm_nonneg _) (hB ⟨δ,⟨le_rfl,by
      exact (hf 1).trans ((Complex.re_le_norm _).trans (f.norm_coe_le_norm 1))⟩,rfl⟩))
    · apply hB
      refine ⟨(orbit q hq f u z).re,⟨orbit_real_lower q hq f δ hf u z,?_⟩,rfl⟩
      exact (Complex.re_le_norm _).trans (((orbit q hq f u).norm_coe_le_norm z).trans (orbit_contraction q hq f u))
    · rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (((orbit q hq g u).norm_coe_le_norm z).trans (orbit_contraction q hq g u))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := invariantLaw q)
    (s := Ioi 0) (bound := fun _ => B*‖g‖) (Ioi_mem_nhds ht) ?_ ?_ ?_ ?_ (integrable_const _) ?_).2
  · exact Eventually.of_forall (fun u => (continuous_klFun.comp (Complex.continuous_re.comp (orbit q hq f u).continuous)).aestronglyMeasurable)
  · exact (continuous_klFun.comp (Complex.continuous_re.comp (orbit q hq f t).continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (((Complex.continuous_re.comp (orbit q hq f t).continuous).log (fun z => ne_of_gt (hpos t z))).mul
      (Complex.continuous_re.comp (orbit q hq g t).continuous)).aestronglyMeasurable
  · exact Eventually.of_forall (fun z u _ => hbound u z)
  · apply Eventually.of_forall
    intro z u hu
    simpa only [Function.comp_def] using (hasDerivAt_klFun (ne_of_gt (hpos u z))).comp u (orbit_real_derivative q hq f g h u hu z)


theorem kernel_entropy_jensen (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (f : C(Circle,ℂ)) (hf : ∀ z, 0 ≤ (f z).re) (z : Circle) :
    klFun (operator q t hq ht f z).re ≤ ∫ w, klFun (f w).re ∂kernel q t z := by
  let := kernel_markov q t hq ht
  have he : (operator q t hq ht f z).re = ∫ w, (f w).re ∂kernel q t z :=
    (Complex.reCLM.integral_comp_comm (observable_integrable q t hq ht f z)).symm
  rw [he]
  apply convexOn_klFun.map_integral_le continuous_klFun.continuousOn isClosed_Ici
    (Eventually.of_forall hf) (Complex.reCLM.integrable_comp (observable_integrable q t hq ht f z))
  exact (continuous_klFun.comp (Complex.continuous_re.comp f.continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem observable_entropy_decreases (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (f : C(Circle,ℂ)) (hf : ∀ z, 0 ≤ (f z).re) :
    (∫ z, klFun (orbit q hq f t z).re ∂invariantLaw q) ≤ ∫ z, klFun (f z).re ∂invariantLaw q := by
  let := kernel_markov q t hq ht
  let := invariantLaw_probability q hq
  have hc : ((kernel q t) ∘ₖ Kernel.const Unit (invariantLaw q)) () = invariantLaw q := by
    exact kernel_invariant q t hq ht
  have hi : Integrable (fun z => klFun (f z).re) (((kernel q t) ∘ₖ Kernel.const Unit (invariantLaw q)) ()) := by
    rw [hc]
    exact (continuous_klFun.comp (Complex.continuous_re.comp f.continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he := Kernel.integral_comp hi
  rw [hc] at he
  rw [he]
  apply integral_mono
  · exact (continuous_klFun.comp (Complex.continuous_re.comp (orbit q hq f t).continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hi.integral_comp
  · intro z
    simpa only [orbit,max_eq_left ht] using kernel_entropy_jensen q t hq ht f hf z

theorem observable_entropy_production_nonpos (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) (δ : ℝ) (hδ : 0 < δ) (hf : ∀ z, δ ≤ (f z).re)
    (t : ℝ) (ht : 0 < t) :
    (∫ z, Real.log (orbit q hq f t z).re * (orbit q hq g t z).re ∂invariantLaw q) ≤ 0 := by
  have hd := observable_entropy_derivative q hq f g h δ hδ hf t ht
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with u hu
  change 0 < u at hu
  have hh := observable_entropy_decreases q u hq hu.le (orbit q hq f t)
    (fun z => hδ.le.trans (orbit_real_lower q hq f δ hf t z))
  have he : orbit q hq f (t+u) = orbit q hq (orbit q hq f t) u := by
    rw [add_comm,orbit_add q hq f u t hu.le ht.le]
    simp only [orbit,max_eq_left hu.le]
  rw [← he] at hh
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hu.le) (sub_nonpos.mpr hh)

end OperatorDerivativeRewrite.Foundation.CauchyPoissonObservableEntropy
