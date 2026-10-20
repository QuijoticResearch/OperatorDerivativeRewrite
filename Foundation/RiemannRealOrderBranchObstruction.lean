import Foundation.RiemannRealOrderLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
/-! No holomorphic germ through zero matches the even actual density at
half-integer orders with odd numerator and nonzero time. A positive half-line
extension still exists. No general impossibility of contour deformation or
obstruction to the already constructed entire Fourier family is asserted. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderBranchObstruction
open RiemannRealOrderFlow RiemannThetaComplexKernel RiemannQuarticKernel

theorem no_analytic_even_odd_exponential (n : ℕ) (hn : Odd n) (t : ℝ) (ht : t ≠ 0) :
    ¬ ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧
      ∀ᶠ x : ℝ in 𝓝 0, f (x : ℂ)=((Real.exp (t*|x|^n) : ℝ) : ℂ) := by
  rintro ⟨f,hf,hreal⟩
  let g := fun z : ℂ => Complex.exp ((t : ℂ)*z^n)
  have hg : AnalyticAt ℂ g 0 := (analyticAt_const.mul (analyticAt_id.pow n)).cexp
  have hpos : ∀ᶠ x : ℝ in 𝓝[Ioi (0 : ℝ)] 0, 0 < x := self_mem_nhdsWithin
  have hp : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[Ioi (0 : ℝ)] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [hpos] with x hx
      simpa only [mem_compl_iff,mem_singleton_iff] using Complex.ofReal_ne_zero.mpr hx.ne'
  have hneg : Tendsto (fun x : ℝ => (-x : ℂ)) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def,neg_zero,Complex.ofReal_zero,Complex.ofReal_neg] using
      ((Complex.continuous_ofReal.comp continuous_neg).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  rcases hf.eventually_eq_or_eventually_ne hg with heq | hne
  · have hnr : Tendsto (fun x : ℝ => -x) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ)) := by
      simpa only [neg_zero] using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hall := (hneg.eventually heq).and ((hnr.eventually hreal).and hpos)
    obtain ⟨x,hx⟩ := hall.exists
    have hfx := hx.1
    have hrx := hx.2.1
    have hx0 := hx.2.2
    have harg : (t : ℂ)*(-x : ℂ)^n=((-t*x^n : ℝ) : ℂ) := by
      rw [hn.neg_pow]
      push_cast
      ring
    change f (-x : ℂ)=Complex.exp ((t : ℂ)*(-x : ℂ)^n) at hfx
    rw [harg,← Complex.ofReal_exp] at hfx
    simp only [Complex.ofReal_neg,abs_neg,abs_of_pos hx0] at hrx
    rw [hrx] at hfx
    have hh := Real.exp_injective (Complex.ofReal_injective hfx)
    have hz : t*x^n=0 := by linarith
    exact (mul_eq_zero.mp hz).elim ht (pow_pos hx0 n).ne'
  · have hall := (hp.eventually hne).and ((hreal.filter_mono nhdsWithin_le_nhds).and hpos)
    obtain ⟨x,hx⟩ := hall.exists
    apply hx.1
    change f (x : ℂ)=Complex.exp ((t : ℂ)*(x : ℂ)^n)
    calc
      _ = ((Real.exp (t*x^n) : ℝ) : ℂ) := by simpa only [abs_of_pos hx.2.2] using hx.2.1
      _ = _ := by rw [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_pow]

theorem no_analytic_half_integer_density (n : ℕ) (hn : Odd n) (t : ℝ) (ht : t ≠ 0) :
    ¬ ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧
      ∀ᶠ x : ℝ in 𝓝 0, f (x : ℂ)=((weighted ((n : ℝ)/2) 0 t 0 x : ℝ) : ℂ) := by
  rintro ⟨f,hf,hreal⟩
  have hK : AnalyticAt ℂ kernelComplex 0 := kernelComplex_analyticAt 0 (by simp)
  have hK0 : kernelComplex 0 ≠ 0 := by
    have hp := (kernel_pos 0 (by norm_num)).ne'
    rw [← Complex.ofReal_zero,kernelComplex_real]
    exact Complex.ofReal_ne_zero.mpr hp
  have hquot : AnalyticAt ℂ (fun z => f z/kernelComplex z) 0 := hf.div hK hK0
  have hne : ∀ᶠ x : ℝ in 𝓝 0, kernelComplex (x : ℂ) ≠ 0 :=
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).eventually
      (by simpa only [Complex.ofReal_zero] using hK.continuousAt.eventually_ne hK0)
  apply no_analytic_even_odd_exponential n hn t ht
  refine ⟨fun z => f z/kernelComplex z,hquot,?_⟩
  filter_upwards [hreal,hne] with x hx hnx
  have he : 2*((n : ℝ)/2)=(n : ℝ) := by ring
  have hw : weighted ((n : ℝ)/2) 0 t 0 x=Real.exp (t*|x|^n)*kernel x := by
    simp only [weighted,pow_zero,one_mul,zero_mul,add_zero,he,Real.rpow_natCast]
  rw [hx,hw,Complex.ofReal_mul,← kernelComplex_real, mul_div_cancel_right₀ _ hnx]

theorem three_halves_actual_density_obstruction (t : ℝ) (ht : t ≠ 0) :
    ¬ ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧
      ∀ᶠ x : ℝ in 𝓝 0, f (x : ℂ)=((weighted (3/2) 0 t 0 x : ℝ) : ℂ) := by
  simpa only [Nat.cast_ofNat] using no_analytic_half_integer_density 3 (by decide) t ht

theorem positive_half_line_density_extension (n : ℕ) (t : ℝ) :
    AnalyticAt ℂ (fun z => Complex.exp ((t : ℂ)*z^n)*kernelComplex z) 0 ∧
      ∀ x : ℝ, 0 ≤ x → Complex.exp ((t : ℂ)*(x : ℂ)^n)*kernelComplex (x : ℂ)=
        ((weighted ((n : ℝ)/2) 0 t 0 x : ℝ) : ℂ) := by
  refine ⟨(analyticAt_const.mul (analyticAt_id.pow n)).cexp.mul
    (kernelComplex_analyticAt 0 (by simp)),?_⟩
  intro x hx
  have he : 2*((n : ℝ)/2)=(n : ℝ) := by ring
  simp only [weighted,pow_zero,one_mul,zero_mul,add_zero,he,abs_of_nonneg hx,Real.rpow_natCast,
    kernelComplex_real,← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_exp]

theorem positive_extension_wrong_at_minus_one (n : ℕ) (hn : Odd n)
    (t : ℝ) (ht : t ≠ 0) :
    Complex.exp ((t : ℂ)*(-1 : ℂ)^n)*kernelComplex (-1) ≠
      ((weighted ((n : ℝ)/2) 0 t 0 (-1) : ℝ) : ℂ) := by
  intro h
  have hk : kernel (-1 : ℝ) ≠ 0 := by
    rw [RiemannQuarticKernelReflection.kernel_even]
    exact (kernel_pos 1 (by norm_num)).ne'
  have hkr : kernelComplex (-1 : ℂ) = (kernel (-1 : ℝ) : ℂ) := by
    simpa using kernelComplex_real (-1)
  have he : Complex.exp (-(t : ℂ)) = (Real.exp (-t) : ℂ) := by
    simpa using (Complex.ofReal_exp (-t)).symm
  simp only [weighted,pow_zero,one_mul,zero_mul,add_zero,abs_neg,abs_one,
    Real.one_rpow,hn.neg_one_pow,mul_neg_one,hkr,he] at h
  have hh : Real.exp (-t)*kernel (-1) = Real.exp t*kernel (-1) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul,mul_one,neg_zero,add_zero] using h
  have htneg := Real.exp_injective (mul_right_cancel₀ hk hh)
  exact ht (by linarith)

theorem zero_time_density_extension (a : ℝ) :
    AnalyticAt ℂ kernelComplex 0 ∧ ∀ x : ℝ,
      kernelComplex (x : ℂ) = ((weighted a 0 0 0 x : ℝ) : ℂ) := by
  refine ⟨kernelComplex_analyticAt 0 (by simp),?_⟩
  intro x
  simp only [weighted,pow_zero,one_mul,zero_mul,add_zero,Real.exp_zero,kernelComplex_real]

theorem half_integer_fourier_entire_despite_density (n : ℕ) (hn : Odd n)
    (t : ℝ) (ht : t ≠ 0) :
    Differentiable ℂ (flow ((n : ℝ)/2) t) ∧ 0 < (flow ((n : ℝ)/2) t 0).re ∧
      ¬ ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧
        ∀ᶠ x : ℝ in 𝓝 0, f (x : ℂ)=((weighted ((n : ℝ)/2) 0 t 0 x : ℝ) : ℂ) := by
  exact ⟨flow_differentiable _ (by positivity) t,actual_flow_zero_pos _ (by positivity) t,
    no_analytic_half_integer_density n hn t ht⟩

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderBranchObstruction
