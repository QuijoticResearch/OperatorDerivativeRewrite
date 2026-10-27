import Foundation.CauchyPoissonResidualKernel
open MeasureTheory Set Filter InformationTheory
open scoped ENNReal NNReal
/-! Relative-entropy contraction for the actual drifted circle Poisson kernel.
The coefficient depends on a fixed positive time. Infinite initial entropy is
allowed, but no instant finiteness or sharp logarithmic Sobolev constant follows. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonMixtureEntropy

theorem klFun_mix (a b x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (hx : 0 ≤ x) :
    klFun (a+b*x) ≤ b*klFun x := by
  have hh := convexOn_klFun.2 (show (1:ℝ) ∈ Ici 0 by norm_num) hx ha hb hab
  simpa only [smul_eq_mul,mul_one,klFun_one,mul_zero,zero_add] using hh

theorem mixture_rnDeriv {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℝ≥0) :
    (a • ν+b • μ).rnDeriv ν =ᵐ[ν] fun x => (a:ℝ≥0∞)+(b:ℝ≥0∞)*μ.rnDeriv ν x := by
  filter_upwards [Measure.rnDeriv_add (a • ν) (b • μ) ν,
    Measure.rnDeriv_smul_left ν ν a,Measure.rnDeriv_smul_left μ ν b,Measure.rnDeriv_self ν]
    with x hsum ha hb hself
  simpa only [Pi.add_apply,Pi.smul_apply,ENNReal.smul_def,smul_eq_mul,hself,mul_one] using hsum.trans (congrArg₂ (·+·) ha hb)

theorem mixture_kl_bound {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℝ≥0) (hab : a+b=1)
    (hac : μ ≪ ν) :
    klDiv (a • ν+b • μ) ν ≤ (b:ℝ≥0∞)*klDiv μ ν := by
  have hmix : a • ν+b • μ ≪ ν := (Measure.AbsolutelyContinuous.rfl.smul_left a).add_left (hac.smul_left b)
  rw [klDiv_eq_lintegral_klFun_of_ac hmix,klDiv_eq_lintegral_klFun_of_ac hac,
    ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_mono_ae
  filter_upwards [mixture_rnDeriv μ ν a b,Measure.rnDeriv_lt_top μ ν] with x hx hfin
  rw [hx,ENNReal.toReal_add ENNReal.coe_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin.ne),ENNReal.toReal_mul]
  simp only [ENNReal.coe_toReal]
  have hh := klFun_mix (a:ℝ) (b:ℝ) (μ.rnDeriv ν x).toReal a.coe_nonneg b.coe_nonneg
    (by exact_mod_cast hab) ENNReal.toReal_nonneg
  have he := ENNReal.ofReal_le_ofReal hh
  simpa only [ENNReal.ofReal_mul b.coe_nonneg,ENNReal.ofReal_coe_nnreal] using he


theorem mixture_kl_bound_all {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℝ≥0) (hab : a+b=1) :
    klDiv (a • ν+b • μ) ν ≤ (b:ℝ≥0∞)*klDiv μ ν := by
  by_cases hb : b=0
  · subst b
    simp only [add_zero] at hab
    subst a
    simp [klDiv_self]
  by_cases hac : μ ≪ ν
  · exact mixture_kl_bound μ ν a b hab hac
  · rw [klDiv_of_not_ac hac,ENNReal.mul_top (by exact_mod_cast hb)]
    exact le_top

open ProbabilityTheory CauchyPoissonFlow CauchyPoissonKernelComposition
  CauchyPoissonMarkovKernel CauchyPoissonResidualKernel

theorem entropy_contraction (q t ε : ℝ) (hq : |q| < 1) (ht : 0 < t) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (h : ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi), ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≤ ENNReal.ofReal (1-ε)*klDiv μ (invariantLaw q) := by
  let := residualKernel_markov q t ε hq ht hε1 h
  let := invariantLaw_probability q hq
  have hd := klDiv_comp_right_le μ (invariantLaw q) (residualKernel q t ε)
  rw [residualKernel_invariant q t ε hq ht hε0 hε1 h] at hd
  let a : ℝ≥0 := ⟨ε,hε0⟩
  let b : ℝ≥0 := ⟨1-ε,(sub_pos.mpr hε1).le⟩
  have hab : a+b=1 := by ext; change ε+(1-ε)=1; ring
  have hm := mixture_kl_bound_all ((residualKernel q t ε) ∘ₘ μ) (invariantLaw q) a b hab
  have ha : (a:ℝ≥0∞)=ENNReal.ofReal ε := by exact (ENNReal.ofReal_eq_coe_nnreal hε0).symm
  have hb : (b:ℝ≥0∞)=ENNReal.ofReal (1-ε) := by exact (ENNReal.ofReal_eq_coe_nnreal (sub_pos.mpr hε1).le).symm
  change klDiv ((a:ℝ≥0∞) • invariantLaw q+(b:ℝ≥0∞) • ((residualKernel q t ε) ∘ₘ μ)) (invariantLaw q) ≤ _ at hm
  rw [ha,hb,forward_split q t ε hq ht hε0 hε1 h μ] at hm
  exact hm.trans (by gcongr)

theorem exists_entropy_contraction (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ (μ : Measure Circle) [IsProbabilityMeasure μ],
      klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≤ ENNReal.ofReal c*klDiv μ (invariantLaw q) := by
  obtain ⟨ε,hε,hε1,h⟩ := strict_density_minorization q t hq ht
  refine ⟨1-ε,sub_pos.mpr hε1,by linarith,fun μ _ => ?_⟩
  exact entropy_contraction q t ε hq ht hε.le hε1 h μ


theorem entropy_geometric (q t c : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (hc : ∀ (μ : Measure Circle) [IsProbabilityMeasure μ],
      klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≤ ENNReal.ofReal c*klDiv μ (invariantLaw q))
    (μ : Measure Circle) [IsProbabilityMeasure μ] (n : ℕ) :
    klDiv ((kernel q (n*t)) ∘ₘ μ) (invariantLaw q) ≤ (ENNReal.ofReal c)^n*klDiv μ (invariantLaw q) := by
  induction n with
  | zero => simp [kernel_zero]
  | succ n ih =>
    have hn : 0 ≤ (n:ℝ)*t := mul_nonneg (Nat.cast_nonneg n) ht
    let := kernel_markov q ((n:ℝ)*t) hq hn
    have hs := hc ((kernel q ((n:ℝ)*t)) ∘ₘ μ)
    rw [Measure.comp_assoc,kernel_composition q ((n:ℝ)*t) t hq hn ht] at hs
    have he : ((n+1:ℕ):ℝ)*t=(n:ℝ)*t+t := by push_cast; ring
    rw [he]
    calc
      _ ≤ ENNReal.ofReal c*klDiv ((kernel q ((n:ℝ)*t)) ∘ₘ μ) (invariantLaw q) := hs
      _ ≤ ENNReal.ofReal c*((ENNReal.ofReal c)^n*klDiv μ (invariantLaw q)) := by gcongr
      _ = _ := by rw [pow_succ]; ring

theorem exists_geometric_entropy_decay (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ (μ : Measure Circle) [IsProbabilityMeasure μ] (n : ℕ),
      klDiv ((kernel q (n*t)) ∘ₘ μ) (invariantLaw q) ≤ (ENNReal.ofReal c)^n*klDiv μ (invariantLaw q) := by
  obtain ⟨c,hc0,hc1,hc⟩ := exists_entropy_contraction q t hq ht
  exact ⟨c,hc0,hc1,fun μ _ n => entropy_geometric q t c hq ht.le hc μ n⟩

end OperatorDerivativeRewrite.Foundation.CauchyPoissonMixtureEntropy
