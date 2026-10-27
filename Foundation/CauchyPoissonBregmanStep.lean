import Foundation.CauchyPoissonExponentialEntropy
import Mathlib.Probability.Kernel.Composition.WithDensity
/-! Actual stationary-transition reverse Bregman identity and dissipation limit.
Positive-time density smoothness differentiates every continuous observable.
No backward log-density domain or singular Levy-kernel identity is assumed. -/
open Complex MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonBregmanStep
open CauchyPoissonMarkovKernel CauchyPoissonForwardDensity CauchyPoissonDensitySmooth

def bregman (a b : ℝ) : ℝ := a*Real.log (a/b)-a+b

theorem bregman_nonneg (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 ≤ bregman a b := by
  have hh := mul_nonneg hb.le (klFun_nonneg (div_pos ha hb).le)
  have he : b*klFun (a/b) = bregman a b := by
    unfold klFun bregman
    field_simp
    <;> ring
  rwa [he] at hh

theorem bregman_expand (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    bregman a b = a*Real.log a-a*Real.log b-a+b := by
  unfold bregman
  rw [Real.log_div ha.ne' hb.ne']
  ring

theorem joint_fst (q h : ℝ) (hq : |q| < 1) (hh : 0 ≤ h)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (f : C(Circle,ℝ)) :
    (∫ p, f p.1 ∂μ ⊗ₘ kernel q h) = ∫ z, f z ∂μ := by
  let := kernel_markov q h hq hh
  have he := integral_map (μ := μ ⊗ₘ kernel q h) measurable_fst.aemeasurable f.continuous.aestronglyMeasurable
  rw [← Measure.fst,Measure.fst_compProd] at he
  exact he.symm

theorem joint_snd (q h : ℝ) (hq : |q| < 1) (hh : 0 ≤ h)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (f : C(Circle,ℝ)) :
    (∫ p, f p.2 ∂μ ⊗ₘ kernel q h) = ∫ z, f z ∂(kernel q h) ∘ₘ μ := by
  let := kernel_markov q h hq hh
  have he := integral_map (μ := μ ⊗ₘ kernel q h) measurable_snd.aemeasurable f.continuous.aestronglyMeasurable
  rw [← Measure.snd,Measure.snd_compProd] at he
  exact he.symm

theorem weighted_joint (q h : ℝ) (hq : |q| < 1) (hh : 0 ≤ h)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (f g : C(Circle,ℝ))
    (hf : ∀ z, 0 < f z) (hμ : (invariantLaw q).withDensity (fun z => ENNReal.ofReal (f z)) = μ) :
    (∫ p, f p.1*g p.2 ∂(invariantLaw q) ⊗ₘ kernel q h) =
      ∫ w, g w ∂(kernel q h) ∘ₘ μ := by
  let := invariantLaw_probability q hq
  let := kernel_markov q h hq hh
  have hm := Measure.withDensity_compProd (κ := kernel q h)
    (μ := invariantLaw q) (ENNReal.measurable_ofReal.comp f.continuous.measurable)
  simp only [Function.comp_def] at hm
  rw [hμ] at hm
  have he := integral_withDensity_eq_integral_toReal_smul
    (μ := (invariantLaw q) ⊗ₘ kernel q h)
    ((ENNReal.measurable_ofReal.comp f.continuous.measurable).comp measurable_fst)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun p : Circle × Circle => g p.2)
  simp only [Function.comp_def] at he
  rw [← hm] at he
  simp only [ENNReal.toReal_ofReal (hf _).le,smul_eq_mul] at he
  exact he.symm.trans (joint_snd q h hq hh μ g)



theorem density_pairing (q : ℝ) (μ : Measure Circle) (f g : C(Circle,ℝ))
    (hf : ∀ z, 0 < f z) (hμ : (invariantLaw q).withDensity (fun z => ENNReal.ofReal (f z)) = μ) :
    (∫ z, f z*g z ∂invariantLaw q) = ∫ z, g z ∂μ := by
  have he := integral_withDensity_eq_integral_toReal_smul (μ := invariantLaw q)
    (ENNReal.measurable_ofReal.comp f.continuous.measurable)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g
  simp only [Function.comp_def] at he
  rw [hμ] at he
  simpa only [ENNReal.toReal_ofReal (hf _).le,smul_eq_mul] using he.symm

theorem step_identity (q h : ℝ) (hq : |q| < 1) (hh : 0 ≤ h)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (f : C(Circle,ℝ))
    (hf : ∀ z, 0 < f z) (hμ : (invariantLaw q).withDensity (fun z => ENNReal.ofReal (f z)) = μ) :
    (∫ p, bregman (f p.1) (f p.2) ∂(invariantLaw q) ⊗ₘ kernel q h) =
      (∫ z, Real.log (f z) ∂μ) - ∫ z, Real.log (f z) ∂(kernel q h) ∘ₘ μ := by
  let := invariantLaw_probability q hq
  let := kernel_markov q h hq hh
  let g : C(Circle,ℝ) := ⟨fun z => Real.log (f z),f.continuous.log (fun z => (hf z).ne')⟩
  have hi (F : C(Circle × Circle,ℝ)) : Integrable F ((invariantLaw q) ⊗ₘ kernel q h) :=
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hA := hi ⟨fun p => f p.1*g p.1,by fun_prop⟩
  have hB := hi ⟨fun p => f p.1*g p.2,by fun_prop⟩
  have hC := hi ⟨fun p => f p.1,by fun_prop⟩
  have hD := hi ⟨fun p => f p.2,by fun_prop⟩
  simp only [ContinuousMap.coe_mk] at hA hB hC hD
  have hfst := joint_fst q h hq hh (invariantLaw q) (f*g)
  have hfstf := joint_fst q h hq hh (invariantLaw q) f
  have hsnd := joint_snd q h hq hh (invariantLaw q) f
  rw [CauchyPoissonEntropy.invariant_comp q h hq hh] at hsnd
  simp only [ContinuousMap.mul_apply] at hfst
  simp_rw [bregman_expand _ _ (hf _) (hf _)]
  change (∫ p, f p.1*g p.1-f p.1*g p.2-f p.1+f p.2 ∂(invariantLaw q) ⊗ₘ kernel q h) = _
  have e1 := integral_add ((hA.sub hB).sub hC) hD
  have e2 := integral_sub (hA.sub hB) hC
  have e3 := integral_sub hA hB
  simp only [Pi.sub_apply] at e1 e2 e3
  rw [e1,e2,e3,
    hfst,hfstf,hsnd,weighted_joint q h hq hh μ f g hf hμ,density_pairing q μ f g hf hμ]
  change (∫ z, g z ∂μ)-(∫ z, g z ∂(kernel q h) ∘ₘ μ)-(∫ z, f z ∂invariantLaw q)+
    (∫ z, f z ∂invariantLaw q) = (∫ z, g z ∂μ)-(∫ z, g z ∂(kernel q h) ∘ₘ μ)
  ring

theorem step_nonneg (q h : ℝ) (f : C(Circle,ℝ)) (hf : ∀ z, 0 < f z) :
    0 ≤ ∫ p, bregman (f p.1) (f p.2) ∂(invariantLaw q) ⊗ₘ kernel q h :=
  integral_nonneg (fun p => bregman_nonneg _ _ (hf p.1) (hf p.2))



theorem actual_step_identity (q t h : ℝ) (hq : |q| < 1) (ht : 0 < t) (hh : 0 ≤ h)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (∫ p, bregman (density q t μ p.1) (density q t μ p.2) ∂(invariantLaw q) ⊗ₘ kernel q h) =
      (∫ z, Real.log (density q t μ z) ∂(kernel q t) ∘ₘ μ) -
        ∫ z, Real.log (density q t μ z) ∂(kernel q (t+h)) ∘ₘ μ := by
  let := kernel_markov q t hq ht.le
  let f : C(Circle,ℝ) := ⟨density q t μ,density_continuous q t hq ht μ⟩
  have he := step_identity q h hq hh ((kernel q t) ∘ₘ μ) f
    (density_positive q t hq ht μ) (forward_density q t hq ht μ)
  rw [Measure.comp_assoc,kernel_composition q t h hq ht.le hh] at he
  exact he



open CauchyPoissonForwardDual

theorem continuous_pairing_derivative (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (f : C(Circle,ℂ)) :
    HasDerivAt (fun u => ∫ w, f w ∂(kernel q u) ∘ₘ μ)
      (∫ w, deriv (densityCurve q hq μ) t w * f w ∂invariantLaw q) t := by
  let := invariantLaw_probability q hq
  have hd := ((lawFunctional (invariantLaw q)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    ((densityCurve_hasDerivAt q t hq ht μ).mul_const f)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  rw [density_integral_pairing q u hq hu μ f]
  change (∫ w, density q u μ w • f w ∂invariantLaw q) =
    ∫ w, densityCurve q hq μ u w * f w ∂invariantLaw q
  apply integral_congr_ae
  filter_upwards with w
  rw [densityCurve_apply q u hq hu μ w]
  rfl

theorem real_pairing_derivative (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (g : C(Circle,ℝ)) :
    HasDerivAt (fun u => ∫ w, g w ∂(kernel q u) ∘ₘ μ)
      (∫ w, (deriv (densityCurve q hq μ) t w).re * g w ∂invariantLaw q) t := by
  let := invariantLaw_probability q hq
  let f : C(Circle,ℂ) := ⟨fun w => (g w:ℂ),Complex.continuous_ofReal.comp g.continuous⟩
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (continuous_pairing_derivative q t hq ht μ f)
  have hi : Integrable (fun w => deriv (densityCurve q hq μ) t w * f w) (invariantLaw q) :=
    ((deriv (densityCurve q hq μ) t).continuous.mul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := Complex.reCLM.integral_comp_comm hi
  simp only [Function.comp_def,Complex.reCLM_apply] at hd he
  rw [← he] at hd
  have hv : (fun u => ∫ w, g w ∂(kernel q u) ∘ₘ μ) =ᶠ[𝓝 t]
      fun u => (∫ w, f w ∂(kernel q u) ∘ₘ μ).re := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    let := kernel_markov q u hq hu.le
    have hh := Complex.reCLM.integral_comp_comm
      (f.continuous.integrable_of_hasCompactSupport (μ := (kernel q u) ∘ₘ μ) (HasCompactSupport.of_compactSpace _))
    simpa [f,Function.comp_def] using hh
  have hh := hd.congr_of_eventuallyEq hv
  simpa [f,Complex.mul_re] using hh

theorem dissipation_limit (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    Tendsto (fun h : ℝ => h⁻¹ *
      ∫ p, bregman (density q t μ p.1) (density q t μ p.2) ∂(invariantLaw q) ⊗ₘ kernel q h)
      (𝓝[Ioi 0] 0)
      (𝓝 (-(∫ w, Real.log (density q t μ w) *
        (deriv (densityCurve q hq μ) t w).re ∂invariantLaw q))) := by
  let g : C(Circle,ℝ) := ⟨fun w => Real.log (density q t μ w),
    (density_continuous q t hq ht μ).log (fun w => (density_positive q t hq ht μ w).ne')⟩
  have hg : HasDerivAt (fun u => ∫ w, g w ∂(kernel q u) ∘ₘ μ)
      (∫ w, (deriv (densityCurve q hq μ) t w).re * g w ∂invariantLaw q) (t+0) := by
    simpa using real_pairing_derivative q t hq ht μ g
  have hd := hg.comp_const_add t 0
  have hs := (hd.const_sub (∫ w, g w ∂(kernel q t) ∘ₘ μ)).tendsto_slope_zero_right
  have hs' : Tendsto (fun h : ℝ => h⁻¹ * ((∫ w, g w ∂(kernel q t) ∘ₘ μ)-
      ∫ w, g w ∂(kernel q (t+h)) ∘ₘ μ)) (𝓝[Ioi 0] 0)
      (𝓝 (-(∫ w, Real.log (density q t μ w) *
        (deriv (densityCurve q hq μ) t w).re ∂invariantLaw q))) := by
    simpa [Function.comp_def,g,mul_comm] using hs
  apply hs'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change 0 < h at hh
  rw [actual_step_identity q t h hq ht hh.le μ]
  rfl

end OperatorDerivativeRewrite.Foundation.CauchyPoissonBregmanStep
