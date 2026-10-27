import Foundation.CauchyPoissonSingularEntropy
/-! Nonsharp modified logarithmic-Sobolev inequality for normalized positive
Lipschitz densities, using the actual singular jump-Bregman energy.
The stronger rate transfers to genuine forward entropy, including initial time.
No quadratic-energy sharp LSI or diffusion curvature implication is asserted. -/
open Complex MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonModifiedLSI
open CauchyPoissonFlow CauchyPoissonMarkovKernel CauchyPoissonBregmanStep
open CauchyPoissonSingularEntropy CauchyPoissonForwardDensity CauchyPoissonSpatialDensity

theorem reference_upper (q : ℝ) (hq : |q| < 1) (w : Circle) :
    (1-|q|)*poissonKernel 0 q w ≤ 1+|q| := by
  have hr : 1-|q| ≤ ‖(w:ℂ)-(q:ℂ)‖ := by
    simpa only [Circle.norm_coe,Complex.norm_real,Real.norm_eq_abs] using
      norm_sub_norm_le (w:ℂ) (q:ℂ)
  have hd : 0 < ‖(w:ℂ)-(q:ℂ)‖ := by linarith
  have hs : (1-|q|)^2 ≤ ‖(w:ℂ)-(q:ℂ)‖^2 := by nlinarith
  simp only [poissonKernel,sub_zero,Circle.norm_coe,one_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  have he : (1-|q|)*(1-q^2) = (1+|q|)*(1-|q|)^2 := by rw [← sq_abs q]; ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

theorem kernel_bregman_lower (q : ℝ) (hq : |q| < 1) (f : Circle → ℝ)
    (hf : ∀ z, 0 < f z) (z w : Circle) :
    ((1-|q|)/(2*(1+|q|)))*bregman (f z) (f w) ≤
      (2/‖(w:ℂ)-(z:ℂ)‖^2)/poissonKernel 0 q w * bregman (f z) (f w) := by
  by_cases hwz : w = z
  · subst w; simp [bregman,(hf z).ne']
  have hd : 0 < ‖(w:ℂ)-(z:ℂ)‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (sub_ne_zero.mpr (by intro h; exact hwz (Subtype.ext h))))
  have hp := CauchyPoissonKernelComposition.poisson_positive (q:ℂ) w (by simpa using hq) (by simp)
  have hc : ‖(w:ℂ)-(z:ℂ)‖^2 ≤ 4 := by
    have hh := norm_sub_le (w:ℂ) (z:ℂ)
    simp only [Circle.norm_coe] at hh
    nlinarith [norm_nonneg ((w:ℂ)-(z:ℂ))]
  have hr := reference_upper q hq w
  have hj : (1-|q|)/(2*(1+|q|)) ≤ (2/‖(w:ℂ)-(z:ℂ)‖^2)/poissonKernel 0 q w := by
    rw [div_div]
    apply (le_div_iff₀ (mul_pos hd hp)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 2*(1+|q|) by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg (sub_nonneg.mpr hq.le) hp.le)
    nlinarith [hh]
  exact mul_le_mul_of_nonneg_right hj (bregman_nonneg _ _ (hf z) (hf w))

theorem product_bregman (ν : Measure Circle) [IsProbabilityMeasure ν]
    (f : C(Circle,ℝ)) (hf : ∀ z, 0 < f z) (hm : ∫ z, f z ∂ν = 1) :
    (∫ p : Circle × Circle, bregman (f p.1) (f p.2) ∂ν.prod ν) =
      (∫ z, f z*Real.log (f z) ∂ν) - ∫ z, Real.log (f z) ∂ν := by
  let g : C(Circle,ℝ) := ⟨fun z => Real.log (f z),f.continuous.log (fun z => (hf z).ne')⟩
  have hi (F : C(Circle × Circle,ℝ)) : Integrable F (ν.prod ν) :=
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hA := hi ⟨fun p => f p.1*g p.1,by fun_prop⟩
  have hB := hi ⟨fun p => f p.1*g p.2,by fun_prop⟩
  have hC := hi ⟨fun p => f p.1,by fun_prop⟩
  have hD := hi ⟨fun p => f p.2,by fun_prop⟩
  simp only [ContinuousMap.coe_mk] at hA hB hC hD
  simp_rw [bregman_expand _ _ (hf _) (hf _)]
  change (∫ p : Circle × Circle, f p.1*g p.1-f p.1*g p.2-f p.1+f p.2 ∂ν.prod ν) = _
  have e1 := integral_add ((hA.sub hB).sub hC) hD
  have e2 := integral_sub (hA.sub hB) hC
  have e3 := integral_sub hA hB
  simp only [Pi.sub_apply] at e1 e2 e3
  rw [e1,e2,e3,integral_prod _ hA,integral_prod _ hB,integral_prod _ hC,integral_prod _ hD]
  simp only [integral_const,probReal_univ,one_smul,integral_const_mul,hm]
  dsimp [g]
  rw [integral_mul_const,hm]
  ring

theorem mean_log_nonpos (ν : Measure Circle) [IsProbabilityMeasure ν]
    (f : C(Circle,ℝ)) (hf : ∀ z, 0 < f z) (hm : ∫ z, f z ∂ν = 1) :
    (∫ z, Real.log (f z) ∂ν) ≤ 0 := by
  have hfint := f.continuous.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  have hgint := (f.continuous.log (fun z => (hf z).ne')).integrable_of_hasCompactSupport
    (μ := ν) (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono hgint (hfint.sub (integrable_const 1))
    (fun z => Real.log_le_sub_one_of_pos (hf z))
  have he := integral_sub hfint (integrable_const (1:ℝ))
  simp only [Pi.sub_apply] at hh
  rw [he,hm] at hh
  simpa using hh

theorem modified_lsi (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℝ))
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 ≤ L) (hf : ∀ z, δ ≤ f z)
    (hlip : ∀ z w : Circle, |f z-f w| ≤ L*‖(w:ℂ)-(z:ℂ)‖)
    (hm : ∫ z, f z ∂invariantLaw q = 1) :
    ((1-|q|)/(2*(1+|q|)))*(∫ z, f z*Real.log (f z) ∂invariantLaw q) ≤
      ∫ p : Circle × Circle, (2/‖(p.2:ℂ)-(p.1:ℂ)‖^2)/poissonKernel 0 q p.2 *
        bregman (f p.1) (f p.2) ∂(invariantLaw q).prod (invariantLaw q) := by
  let := invariantLaw_probability q hq
  have hf0 : ∀ z, 0 < f z := fun z => hδ.trans_le (hf z)
  have hi := (bregman_continuous f hf0).integrable_of_hasCompactSupport
    (μ := (invariantLaw q).prod (invariantLaw q)) (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono (hi.const_mul ((1-|q|)/(2*(1+|q|))))
    (singular_integrable q hq f δ L hδ hL hf hlip)
    (fun p => kernel_bregman_lower q hq f hf0 p.1 p.2)
  rw [integral_const_mul,product_bregman (invariantLaw q) f hf0 hm] at hh
  have hl := mean_log_nonpos (invariantLaw q) f hf0 hm
  have hp := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (1-|q|)/(2*(1+|q|)) from div_nonneg (sub_nonneg.mpr hq.le) (by positivity)) hl
  nlinarith

theorem normalized_entropy (ν : Measure Circle) [IsProbabilityMeasure ν]
    (f : C(Circle,ℝ)) (hf : ∀ z, 0 < f z) (hm : ∫ z, f z ∂ν = 1) :
    (∫ z, klFun (f z) ∂ν) = ∫ z, f z*Real.log (f z) ∂ν := by
  have hi := f.continuous.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  have hg := (f.continuous.mul (f.continuous.log (fun z => (hf z).ne'))).integrable_of_hasCompactSupport
    (μ := ν) (HasCompactSupport.of_compactSpace _)
  have h1 := integral_sub (hg.add (integrable_const 1)) hi
  have h2 := integral_add hg (integrable_const (1:ℝ))
  simp only [Pi.add_apply,Pi.mul_apply] at h1 h2
  simp only [klFun]
  rw [h1,h2,hm]
  simp

theorem density_mass (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (∫ z, density q t μ z ∂invariantLaw q) = 1 := by
  let := kernel_markov q t hq ht.le
  let f : C(Circle,ℝ) := ⟨density q t μ,density_continuous q t hq ht μ⟩
  have hh := density_pairing q ((kernel q t) ∘ₘ μ) f 1
    (density_positive q t hq ht μ) (forward_density q t hq ht μ)
  simpa [f] using hh

theorem density_entropy (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)).toReal =
      ∫ z, density q t μ z*Real.log (density q t μ z) ∂invariantLaw q := by
  let := invariantLaw_probability q hq
  have hh := CauchyPoissonForwardEntropy.entropy_actual_kl q t hq ht μ
  simp_rw [CauchyPoissonDensitySmooth.densityCurve_apply q t hq ht μ,Complex.ofReal_re] at hh
  exact hh.trans (normalized_entropy (invariantLaw q)
    ⟨density q t μ,density_continuous q t hq ht μ⟩ (density_positive q t hq ht μ)
    (density_mass q t hq ht μ))

theorem actual_production_bound (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (∫ w, Real.log (CauchyPoissonDensitySmooth.densityCurve q hq μ t w).re *
      (deriv (CauchyPoissonDensitySmooth.densityCurve q hq μ) t w).re ∂invariantLaw q) ≤
      -((1-|q|)/(2*(1+|q|)))*(klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)).toReal := by
  obtain ⟨L,hL,hl⟩ := density_lipschitz q t hq ht
  obtain ⟨δ,hδ,hf⟩ := density_lower q t hq ht μ
  let f : C(Circle,ℝ) := ⟨density q t μ,density_continuous q t hq ht μ⟩
  have hh := modified_lsi q hq f δ L hδ hL hf
    (fun z w => by simpa only [f,ContinuousMap.coe_mk,norm_sub_rev] using hl μ z w)
    (density_mass q t hq ht μ)
  change ((1-|q|)/(2*(1+|q|)))*(∫ z, density q t μ z*Real.log (density q t μ z) ∂invariantLaw q) ≤ _ at hh
  change _ ≤ ∫ p : Circle × Circle, (2/‖(p.2:ℂ)-(p.1:ℂ)‖^2)/poissonKernel 0 q p.2 *
      bregman (density q t μ p.1) (density q t μ p.2) ∂(invariantLaw q).prod (invariantLaw q) at hh
  rw [← density_entropy q t hq ht μ,actual_singular_identity q t hq ht μ] at hh
  simp_rw [CauchyPoissonDensitySmooth.densityCurve_apply q t hq ht μ,Complex.ofReal_re]
  linarith

theorem entropy_exponential (q s t : ℝ) (hq : |q| < 1) (hs : 0 < s) (hst : s ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)).toReal ≤
      Real.exp (-((1-|q|)/(2*(1+|q|)))*(t-s))*(klDiv ((kernel q s) ∘ₘ μ) (invariantLaw q)).toReal :=
  CauchyPoissonExponentialEntropy.decay_of_production q ((1-|q|)/(2*(1+|q|))) hq μ
    (fun u hu => actual_production_bound q u hq hu μ) s t hs hst
theorem entropy_initial_real (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ]
    (hfinite : klDiv μ (invariantLaw q) ≠ ⊤) :
    (klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)).toReal ≤
      Real.exp (-(((1-|q|)/(2*(1+|q|))))*t) * (klDiv μ (invariantLaw q)).toReal := by
  rcases eq_or_lt_of_le ht with he | ht
  · subst t; simp [kernel_zero]
  let c := ((1-|q|)/(2*(1+|q|)))
  let E0 := (klDiv μ (invariantLaw q)).toReal
  have hc : Continuous (fun s : ℝ => Real.exp (-c*(t-s))*E0) := by fun_prop
  have hl : Tendsto (fun s : ℝ => Real.exp (-c*(t-s))*E0)
      (𝓝[Ioi 0] 0) (𝓝 (Real.exp (-c*t)*E0)) := by
    simpa using (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs hslt
  change 0 < s at hs
  have hb := entropy_exponential q s t hq hs hslt.le μ
  have hm := ENNReal.toReal_mono hfinite
    (CauchyPoissonEntropy.relative_entropy_contracts q s hq hs.le μ)
  exact hb.trans (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)

theorem entropy_initial (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≤
      ENNReal.ofReal (Real.exp (-(((1-|q|)/(2*(1+|q|))))*t)) * klDiv μ (invariantLaw q) := by
  by_cases hfinite : klDiv μ (invariantLaw q) = ⊤
  · rw [hfinite,ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))]
    exact le_top
  have hf := CauchyPoissonEntropy.entropy_stays_finite q t hq ht μ hfinite
  have hh := ENNReal.ofReal_le_ofReal (entropy_initial_real q t hq ht μ hfinite)
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_toReal hf,ENNReal.ofReal_toReal hfinite] at hh
  exact hh

end OperatorDerivativeRewrite.Foundation.CauchyPoissonModifiedLSI
