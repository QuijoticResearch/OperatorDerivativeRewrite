import Foundation.HigherHeatSchwartzJets

/-! A physical differential equation and Stein identity for the actual higher-heat kernel. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatKernelStein
open HigherHeatL2 HigherHeatSpatialGenerator HigherHeatSchwartzJets GaussianSchwartzKernel

def odeCoefficient (m : ℕ) (t : ℝ≥0) : ℂ := -(2*m:ℕ)*(-1:ℂ)^(m+1)*(t:ℝ)

theorem symbol_deriv (m : ℕ) (t : ℝ≥0) (ξ : ℝ) :
    deriv (symbol m t) ξ=
      ((-(t:ℝ)*(2*m:ℕ)*(2*Real.pi)^(2*m)*ξ^(2*m-1):ℝ):ℂ)*symbol m t ξ := by
  let a : ℝ := -(t:ℝ)*(2*Real.pi)^(2*m)
  have he : symbol m t=(fun y : ℝ => (Real.exp (a*y^(2*m)):ℂ)) := by
    funext y
    simp only [symbol,a,mul_pow]
    congr 2
    ring
  have h : HasDerivAt (fun y : ℝ => Real.exp (a*y^(2*m)))
      (Real.exp (a*ξ^(2*m))*(a*(2*m:ℕ)*ξ^(2*m-1))) ξ := by
    convert (((hasDerivAt_id ξ).pow (2*m)).const_mul a).exp using 1 <;> simp <;> ring
  rw [he]
  convert h.ofReal_comp.deriv using 1 <;> dsimp only [a] <;> push_cast <;> ring

theorem coefficient_factor (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ξ : ℝ) :
    (-2*Real.pi*Complex.I)*odeCoefficient m t*(2*Real.pi*Complex.I*(ξ:ℂ))^(2*m-1)=
      ((-(t:ℝ)*(2*m:ℕ)*(2*Real.pi)^(2*m)*ξ^(2*m-1):ℝ):ℂ) := by
  have he : 2*m-1+1=2*m := by omega
  have hi : (-1:ℂ)^(m+1)*Complex.I^(2*m-1)*Complex.I= -1 := by
    rw [mul_assoc,← pow_succ,he,pow_mul,Complex.I_sq,← pow_add]
    rw [show m+1+m=2*m+1 by omega,pow_add,pow_mul]
    norm_num
  have hc : (2*Real.pi:ℂ)^(2*m-1)*(2*Real.pi)=(2*Real.pi:ℂ)^(2*m) := by
    rw [← pow_succ,he]
  calc
    _ = (2*m:ℕ)*(t:ℝ)*((-1:ℂ)^(m+1)*Complex.I^(2*m-1)*Complex.I)*
        ((2*Real.pi:ℂ)^(2*m-1)*(2*Real.pi))*(ξ:ℂ)^(2*m-1) := by
      simp only [odeCoefficient,mul_pow]
      ring
    _ = _ := by rw [hi,hc]; push_cast; ring

theorem kernel_ode_schwartz (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    weighted (evenKernel m hm t ht)=odeCoefficient m t • jet (2*m-1) (evenKernel m hm t ht) := by
  apply (fourierEquiv ℂ 𝓢(ℝ,ℂ)).injective
  ext ξ
  change 𝓕 (weighted (evenKernel m hm t ht)) ξ=
    𝓕 (odeCoefficient m t • jet (2*m-1) (evenKernel m hm t ht)) ξ
  have hF : 𝓕 (evenKernel m hm t ht : ℝ → ℂ)=symbol m t := by
    funext x
    rw [← SchwartzMap.fourier_coe,evenKernel_fourier,evenSymbol_apply]
  have hd := fourier_weighted (evenKernel m hm t ht) ξ
  rw [hF,symbol_deriv] at hd
  rw [FourierTransform.fourier_smul,SchwartzMap.smul_apply,smul_eq_mul,jet_fourier,
    evenKernel_fourier,evenSymbol_apply]
  apply mul_left_cancel₀ (show (-2*Real.pi*Complex.I:ℂ) ≠ 0 by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  calc
    _ = ((-(t:ℝ)*(2*m:ℕ)*(2*Real.pi)^(2*m)*ξ^(2*m-1):ℝ):ℂ)*symbol m t ξ := hd.symm
    _ = _ := by rw [← mul_assoc,← mul_assoc,coefficient_factor m hm t ξ]

theorem kernel_ode (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (x : ℝ) :
    (x:ℂ)*evenKernel m hm t ht x=
      odeCoefficient m t*iteratedDeriv (2*m-1) (evenKernel m hm t ht : ℝ → ℂ) x := by
  have h := congrArg (fun f : 𝓢(ℝ,ℂ) => f x) (kernel_ode_schwartz m hm t ht)
  simpa only [weighted_apply,SchwartzMap.smul_apply,smul_eq_mul,jet_coe] using h

theorem schwartz_stein (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (f : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, (x:ℂ)*f x*evenKernel m hm t ht x)=
      (2*m:ℕ)*(-1:ℂ)^(m+1)*(t:ℝ)*
        (∫ x : ℝ, jet (2*m-1) f x*evenKernel m hm t ht x) := by
  have ho : Odd (2*m-1) := ⟨m-1,by omega⟩
  calc
    _ = odeCoefficient m t*(∫ x : ℝ, jet (2*m-1) (evenKernel m hm t ht) x*f x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        have h := congrArg (fun g : 𝓢(ℝ,ℂ) => g x) (kernel_ode_schwartz m hm t ht)
        simp only [weighted_apply,SchwartzMap.smul_apply,smul_eq_mul] at h
        linear_combination f x*h
    _ = odeCoefficient m t*((-1:ℂ)^(2*m-1)*
        (∫ x : ℝ, evenKernel m hm t ht x*jet (2*m-1) f x)) := by
      rw [integral_jet_mul]
    _ = _ := by
      rw [ho.neg_one_pow]
      have he : (∫ x : ℝ, evenKernel m hm t ht x*jet (2*m-1) f x)=
          (∫ x : ℝ, jet (2*m-1) f x*evenKernel m hm t ht x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => mul_comm _ _
      rw [he]
      unfold odeCoefficient
      ring

end OperatorDerivativeRewrite.Foundation.HigherHeatKernelStein
