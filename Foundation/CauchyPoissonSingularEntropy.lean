import Foundation.CauchyPoissonSpatialDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-! Actual singular jump-Bregman entropy identity. Fixed-product measure
conversion, absolute domination, diagonal limit and limiting integrability
are proved before identifying the derivative of actual relative entropy. -/
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonSingularEntropy
open CauchyPoissonFlow CauchyPoissonForwardDensity CauchyPoissonMarkovKernel
open CauchyPoissonBregmanStep CauchyPoissonSpatialDensity CauchyPoissonDensitySmooth

theorem ratio_poisson (q h : ℝ) (z w : Circle) :
    ratio q h z w = poissonKernel 0 (evolution q h z) w / poissonKernel 0 q w := by
  unfold ratio circleWeight
  field_simp

theorem joint_pairing (q h : ℝ) (hq : |q| < 1) (hh : 0 < h)
    (g : C(Circle × Circle,ℝ)) :
    (∫ p, g p ∂(invariantLaw q) ⊗ₘ kernel q h) =
      ∫ p, ratio q h p.1 p.2*g p ∂(invariantLaw q).prod (invariantLaw q) := by
  let := invariantLaw_probability q hq
  let := kernel_markov q h hq hh.le
  have hi : Integrable g ((invariantLaw q) ⊗ₘ kernel q h) :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp : Integrable (fun p : Circle × Circle => ratio q h p.1 p.2*g p)
      ((invariantLaw q).prod (invariantLaw q)) :=
    ((ratio_continuous q h hq hh).mul g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ z, ∫ w, g (z,w) ∂kernel q h z ∂invariantLaw q := Measure.integral_compProd hi
    _ = ∫ z, ∫ w, ratio q h z w*g (z,w) ∂invariantLaw q ∂invariantLaw q := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      let f : C(Circle,ℝ) := ⟨fun w => ratio q h z w,
        Continuous.comp (g := fun p : Circle × Circle => ratio q h p.1 p.2)
          (f := fun w : Circle => (z,w)) (ratio_continuous q h hq hh)
          (continuous_const.prodMk continuous_id)⟩
      let gz : C(Circle,ℝ) := ⟨fun w => g (z,w), g.continuous.comp
        (continuous_const.prodMk continuous_id)⟩
      exact (density_pairing q (kernel q h z) f gz (ratio_positive q h hq hh z)
        (kernel_density q h hq hh z)).symm
    _ = _ := (integral_prod _ hp).symm
theorem reference_reciprocal (q : ℝ) (hq : |q| < 1) (w : Circle) :
    (poissonKernel 0 q w)⁻¹ ≤ 4/(1-q^2) := by
  have hh := CauchyPoissonQuantitativeEntropy.poisson_lower (q:ℂ) (by simpa using hq)
    (w:ℂ) (by simp)
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs] at hh
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hp := CauchyPoissonKernelComposition.poisson_positive (q:ℂ) w (by simpa using hq) (by simp)
  have h := one_div_le_one_div_of_le (show 0 < (1-q^2)/4 by positivity) hh
  simpa only [one_div,inv_div] using h

theorem bregman_continuous (f : C(Circle,ℝ)) (hf : ∀ z, 0 < f z) :
    Continuous (fun p : Circle × Circle => bregman (f p.1) (f p.2)) := by
  simp_rw [bregman_expand _ _ (hf _) (hf _)]
  have ha : Continuous (fun p : Circle × Circle => f p.1) := f.continuous.comp continuous_fst
  have hb : Continuous (fun p : Circle × Circle => f p.2) := f.continuous.comp continuous_snd
  exact (((ha.mul (ha.log (fun p => (hf p.1).ne'))).sub
    (ha.mul (hb.log (fun p => (hf p.2).ne')))).sub ha).add hb

theorem bregman_pointwise_limit (q : ℝ) (hq : |q| < 1) (f : Circle → ℝ)
    (hf : ∀ z, 0 < f z) (z w : Circle) :
    Tendsto (fun h : ℝ => h⁻¹ * ratio q h z w * bregman (f z) (f w))
      (𝓝[>] 0) (𝓝 ((2/‖(w:ℂ)-(z:ℂ)‖^2)/poissonKernel 0 q w * bregman (f z) (f w))) := by
  by_cases hwz : w = z
  · subst w
    have hb : bregman (f z) (f z) = 0 := by simp [bregman,(hf z).ne']
    simp only [hb,mul_zero]
    exact tendsto_const_nhds
  · have hh := ((CauchyPoissonJumpLimit.off_diagonal_limit q hq z w hwz).div_const
      (poissonKernel 0 q w)).mul_const (bregman (f z) (f w))
    convert hh using 1
    funext h
    rw [ratio_poisson]
    ring

theorem ratio_bregman_domination (q : ℝ) (hq : |q| < 1) (f : Circle → ℝ)
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 ≤ L) (hf : ∀ z, δ ≤ f z)
    (hlip : ∀ z w : Circle, |f z-f w| ≤ L*‖(w:ℂ)-(z:ℂ)‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ z w : Circle,
      ‖h⁻¹ * ratio q h z w * bregman (f z) (f w)‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := CauchyPoissonJumpDomination.eventual_bregman_domination q hq f δ L hδ hL hf hlip
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  refine ⟨C*(4/(1-q^2)),by positivity,?_⟩
  filter_upwards [hb,self_mem_nhdsWithin] with h hh hp
  intro z w
  have hB := bregman_nonneg (f z) (f w) (hδ.trans_le (hf z)) (hδ.trans_le (hf w))
  have hP := CauchyPoissonKernelComposition.poisson_positive (q:ℂ) w (by simpa using hq) (by simp)
  have hR := ratio_positive q h hq hp z w
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hp.le) hR.le) hB)]
  have h1 := mul_le_mul_of_nonneg_right (hh z w) (inv_nonneg.mpr hP.le)
  have h2 := mul_le_mul_of_nonneg_left (reference_reciprocal q hq w) hC
  rw [ratio_poisson]
  calc
    _ = (h⁻¹ * poissonKernel 0 (evolution q h z) w * bregman (f z) (f w))*
        (poissonKernel 0 q w)⁻¹ := by ring
    _ ≤ C*(poissonKernel 0 q w)⁻¹ := h1
    _ ≤ _ := h2

theorem singular_limit (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℝ))
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 ≤ L) (hf : ∀ z, δ ≤ f z)
    (hlip : ∀ z w : Circle, |f z-f w| ≤ L*‖(w:ℂ)-(z:ℂ)‖) :
    Tendsto (fun h : ℝ => h⁻¹ * ∫ p, bregman (f p.1) (f p.2)
      ∂(invariantLaw q) ⊗ₘ kernel q h) (𝓝[>] 0)
      (𝓝 (∫ p : Circle × Circle, (2/‖(p.2:ℂ)-(p.1:ℂ)‖^2)/poissonKernel 0 q p.2 *
        bregman (f p.1) (f p.2) ∂(invariantLaw q).prod (invariantLaw q))) := by
  let := invariantLaw_probability q hq
  have hf0 : ∀ z, 0 < f z := fun z => hδ.trans_le (hf z)
  let g : C(Circle × Circle,ℝ) := ⟨fun p => bregman (f p.1) (f p.2),bregman_continuous f hf0⟩
  obtain ⟨C,hC,hb⟩ := ratio_bregman_domination q hq f δ L hδ hL hf hlip
  have hm : ∀ᶠ h in 𝓝[>] (0:ℝ), AEStronglyMeasurable
      (fun p : Circle × Circle => h⁻¹ * ratio q h p.1 p.2*g p)
      ((invariantLaw q).prod (invariantLaw q)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (((ratio_continuous q h hq hh).const_mul h⁻¹).mul g.continuous).aestronglyMeasurable
  have hbound : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᵐ p ∂(invariantLaw q).prod (invariantLaw q),
      ‖h⁻¹ * ratio q h p.1 p.2*g p‖ ≤ C := by
    filter_upwards [hb] with h hh
    exact Eventually.of_forall (fun p => hh p.1 p.2)
  have hd := tendsto_integral_filter_of_dominated_convergence (μ := (invariantLaw q).prod (invariantLaw q))
    (fun _ : Circle × Circle => C) hm hbound (integrable_const C)
    (Eventually.of_forall (fun p => bregman_pointwise_limit q hq f hf0 p.1 p.2))
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change (∫ p : Circle × Circle, h⁻¹ * ratio q h p.1 p.2*g p
    ∂(invariantLaw q).prod (invariantLaw q)) = h⁻¹ * ∫ p, g p ∂(invariantLaw q) ⊗ₘ kernel q h
  rw [joint_pairing q h hq hh g,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by dsimp [g]; ring)

theorem singular_integrable (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℝ))
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 ≤ L) (hf : ∀ z, δ ≤ f z)
    (hlip : ∀ z w : Circle, |f z-f w| ≤ L*‖(w:ℂ)-(z:ℂ)‖) :
    Integrable (fun p : Circle × Circle => (2/‖(p.2:ℂ)-(p.1:ℂ)‖^2)/poissonKernel 0 q p.2 *
      bregman (f p.1) (f p.2)) ((invariantLaw q).prod (invariantLaw q)) := by
  let := invariantLaw_probability q hq
  obtain ⟨C,hC,hb⟩ := ratio_bregman_domination q hq f δ L hδ hL hf hlip
  have hm : Measurable (fun p : Circle × Circle => (2/‖(p.2:ℂ)-(p.1:ℂ)‖^2)/poissonKernel 0 q p.2 *
      bregman (f p.1) (f p.2)) := by
    unfold poissonKernel bregman
    fun_prop
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  apply le_of_tendsto (bregman_pointwise_limit q hq f (fun z => hδ.trans_le (hf z)) p.1 p.2).norm
  filter_upwards [hb] with h hh
  exact hh p.1 p.2

theorem actual_singular_integrable (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    Integrable (fun p : Circle × Circle => (2/‖(p.2:ℂ)-(p.1:ℂ)‖^2)/poissonKernel 0 q p.2 *
      bregman (density q t μ p.1) (density q t μ p.2)) ((invariantLaw q).prod (invariantLaw q)) := by
  obtain ⟨L,hL,hl⟩ := density_lipschitz q t hq ht
  obtain ⟨δ,hδ,hf⟩ := density_lower q t hq ht μ
  let f : C(Circle,ℝ) := ⟨density q t μ,density_continuous q t hq ht μ⟩
  exact singular_integrable q hq f δ L hδ hL hf
    (fun z w => by simpa only [f,ContinuousMap.coe_mk,norm_sub_rev] using hl μ z w)

theorem actual_singular_identity (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (∫ p : Circle × Circle, (2/‖(p.2:ℂ)-(p.1:ℂ)‖^2)/poissonKernel 0 q p.2 *
      bregman (density q t μ p.1) (density q t μ p.2) ∂(invariantLaw q).prod (invariantLaw q)) =
      -(∫ w, Real.log (density q t μ w) *
        (deriv (densityCurve q hq μ) t w).re ∂invariantLaw q) := by
  obtain ⟨L,hL,hl⟩ := density_lipschitz q t hq ht
  obtain ⟨δ,hδ,hf⟩ := density_lower q t hq ht μ
  let f : C(Circle,ℝ) := ⟨density q t μ,density_continuous q t hq ht μ⟩
  have hs := singular_limit q hq f δ L hδ hL hf
    (fun z w => by simpa only [f,ContinuousMap.coe_mk,norm_sub_rev] using hl μ z w)
  exact tendsto_nhds_unique hs (dissipation_limit q t hq ht μ)

theorem actual_kl_singular_derivative (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    HasDerivAt (fun u => (InformationTheory.klDiv ((kernel q u) ∘ₘ μ) (invariantLaw q)).toReal)
      (-(∫ p : Circle × Circle, (2/‖(p.2:ℂ)-(p.1:ℂ)‖^2)/poissonKernel 0 q p.2 *
        bregman (density q t μ p.1) (density q t μ p.2) ∂(invariantLaw q).prod (invariantLaw q))) t := by
  rw [actual_singular_identity q t hq ht μ,neg_neg]
  simpa only [densityCurve_apply q t hq ht μ,Complex.ofReal_re] using
    CauchyPoissonForwardEntropy.actual_kl_derivative q t hq ht μ
end OperatorDerivativeRewrite.Foundation.CauchyPoissonSingularEntropy
