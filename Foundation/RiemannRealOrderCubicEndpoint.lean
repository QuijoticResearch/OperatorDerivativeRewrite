import Foundation.RiemannRealOrderCubicFourier
import Foundation.RiemannQuarticKernelReflection
import Foundation.RiemannQuarticZeroCounting

/-! Actual endpoint coefficients for the one-sided cubic arithmetic density.
The local evenness of the theta kernel is kept separate from the cubic tilt. -/
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderCubicEndpoint
open RiemannThetaComplexKernel RiemannRealOrderCubicDensity
open RiemannRealOrderCubicFourier RiemannQuarticKernelReflection

theorem odd_kernel_derivative_zero (n : ℕ) (hn : Odd n) :
    iteratedDeriv n kernelComplex 0 = 0 := by
  have h0 : (0 : ℂ) ∈ strip := by
    change -Real.pi/8 < (0 : ℂ).im ∧ (0 : ℂ).im < Real.pi/8
    simp only [Complex.zero_im]
    constructor <;> linarith [Real.pi_pos]
  have hopen : IsOpen strip := isOpen_Ioo.preimage Complex.continuous_im
  have he : (fun z : ℂ => kernelComplex (-z)) =ᶠ[𝓝 0] kernelComplex := by
    have hs : ∀ᶠ z : ℂ in 𝓝 0, z ∈ strip := hopen.mem_nhds h0
    filter_upwards [hs] with z hz
    exact kernelComplex_even z hz
  have h := he.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg,hn.neg_one_pow,neg_zero,neg_one_smul] at h
  linear_combination -h/2

private theorem cubic_exponential_endpoint_jets (t : ℝ) :
    iteratedDeriv 1 (fun z : ℂ => Complex.exp ((t : ℂ)*z^3)) 0 = 0 ∧
    iteratedDeriv 2 (fun z : ℂ => Complex.exp ((t : ℂ)*z^3)) 0 = 0 ∧
    iteratedDeriv 3 (fun z : ℂ => Complex.exp ((t : ℂ)*z^3)) 0 = 6*(t : ℂ) := by
  let E : ℂ → ℂ := fun z => Complex.exp ((t : ℂ)*z^3)
  have hE (z : ℂ) : HasDerivAt E (3*(t : ℂ)*z^2*E z) z := by
    have h := (((hasDerivAt_id z).pow 3).const_mul (t : ℂ)).cexp
    convert h using 1 <;> first | rfl | (dsimp [E]; ring)
  have hD1 : deriv E = fun z => 3*(t : ℂ)*z^2*E z := funext fun z => (hE z).deriv
  have hE2 (z : ℂ) : HasDerivAt (fun w => 3*(t : ℂ)*w^2*E w)
      ((6*(t : ℂ)*z+9*(t : ℂ)^2*z^4)*E z) z := by
    have h := (((hasDerivAt_id z).pow 2).const_mul (3*(t : ℂ))).mul (hE z)
    convert h using 1 <;> first | rfl | (dsimp [E]; ring)
  have hD2 : iteratedDeriv 2 E = fun z => (6*(t : ℂ)*z+9*(t : ℂ)^2*z^4)*E z := by
    rw [show (2 : ℕ) = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,hD1]
    exact funext fun z => (hE2 z).deriv
  have hE3 : HasDerivAt (fun z => (6*(t : ℂ)*z+9*(t : ℂ)^2*z^4)*E z)
      (6*(t : ℂ)) 0 := by
    have hp := ((hasDerivAt_id (0 : ℂ)).const_mul (6*(t : ℂ))).add
      (((hasDerivAt_id (0 : ℂ)).pow 4).const_mul (9*(t : ℂ)^2))
    have h := hp.mul (hE 0)
    convert h using 1 <;> first | rfl | simp [E]
  refine ⟨?_,?_,?_⟩
  · rw [iteratedDeriv_one,hD1]
    simp
  · rw [hD2]
    simp
  · rw [show (3 : ℕ) = 2+1 by rfl,iteratedDeriv_succ,hD2]
    exact hE3.deriv

theorem density_endpoint_coefficients (t : ℝ) :
    iteratedDeriv 1 (density t) 0 = 0 ∧
      iteratedDeriv 3 (density t) 0 = 6*(t : ℂ)*kernelComplex 0 := by
  let E : ℂ → ℂ := fun z => Complex.exp ((t : ℂ)*z^3)
  have ha : AnalyticAt ℂ E 0 := (analyticAt_const.mul (analyticAt_id.pow 3)).cexp
  have hk : AnalyticAt ℂ kernelComplex 0 := kernelComplex_analyticAt 0 (by simp)
  have hj := cubic_exponential_endpoint_jets t
  change iteratedDeriv 1 E 0 = 0 ∧ iteratedDeriv 2 E 0 = 0 ∧
    iteratedDeriv 3 E 0 = 6*(t : ℂ) at hj
  have hE0 : E 0 = 1 := by simp [E]
  have hK1 := odd_kernel_derivative_zero 1 (by decide)
  have hK3 := odd_kernel_derivative_zero 3 (by decide)
  constructor
  · change iteratedDeriv 1 (E*kernelComplex) 0 = 0
    rw [iteratedDeriv_mul ha.contDiffAt hk.contDiffAt]
    norm_num [Finset.sum_range_succ,iteratedDeriv_zero,hE0,hj.1,hK1]
  · change iteratedDeriv 3 (E*kernelComplex) 0 = 6*(t : ℂ)*kernelComplex 0
    rw [iteratedDeriv_mul ha.contDiffAt hk.contDiffAt]
    norm_num [Finset.sum_range_succ,iteratedDeriv_zero,hE0,hj.1,hj.2.1,hj.2.2,hK1,hK3]

theorem actual_flow_exact_endpoint_identity (t x : ℝ) :
    (x : ℂ)^4*RiemannRealOrderFlow.flow (3/2) t (x : ℂ) =
      ((6*t*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ)+cosineIntegral 4 t x := by
  have hc := density_endpoint_coefficients t
  rw [actual_flow_fourth_identity,hc.1,hc.2]
  simp only [mul_zero,neg_zero,zero_add]
  have hk0 : kernelComplex 0 = (RiemannQuarticKernel.kernel 0 : ℂ) := by
    simpa only [Complex.ofReal_zero] using kernelComplex_real 0
  rw [hk0]
  push_cast
  ring

theorem actual_flow_scaled_limit (t : ℝ) :
    Tendsto (fun x : ℝ => (x : ℂ)^4*RiemannRealOrderFlow.flow (3/2) t (x : ℂ))
      (cocompact ℝ) (𝓝 ((6*t*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ)) := by
  have h : Tendsto (fun x : ℝ => ((6*t*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ)+
      cosineIntegral 4 t x) (cocompact ℝ)
      (𝓝 (((6*t*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ)+0)) :=
    tendsto_const_nhds.add (cosineIntegral_tendsto_zero 4 t)
  simpa only [← actual_flow_exact_endpoint_identity,add_zero] using h

theorem actual_flow_scaled_real_limit (t : ℝ) :
    Tendsto (fun x : ℝ => x^4*(RiemannRealOrderFlow.flow (3/2) t (x : ℂ)).re)
      (cocompact ℝ) (𝓝 (6*t*RiemannQuarticKernel.kernel 0)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (actual_flow_scaled_limit t)
  have he (x : ℝ) : ((x : ℂ)^4*RiemannRealOrderFlow.flow (3/2) t (x : ℂ)).re =
      x^4*(RiemannRealOrderFlow.flow (3/2) t (x : ℂ)).re := by
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change Tendsto (fun x : ℝ => ((x : ℂ)^4*
    RiemannRealOrderFlow.flow (3/2) t (x : ℂ)).re) (cocompact ℝ)
    (𝓝 (((6*t*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ).re)) at h
  simpa only [he,Complex.ofReal_re] using h

theorem eventually_time_signed_positive (t : ℝ) (ht : t ≠ 0) :
    ∀ᶠ x : ℝ in cocompact ℝ, 0 < t*(RiemannRealOrderFlow.flow (3/2) t (x : ℂ)).re := by
  have hk : 0 < RiemannQuarticKernel.kernel 0 := RiemannQuarticKernel.kernel_pos 0 (by norm_num)
  have hc : 0 < t*(6*t*RiemannQuarticKernel.kernel 0) := by
    have h := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 6) (sq_pos_of_ne_zero ht)) hk
    nlinarith
  have h := ((actual_flow_scaled_real_limit t).const_mul t).eventually (Ioi_mem_nhds hc)
  filter_upwards [h] with x hx
  change 0 < t*(x^4*(RiemannRealOrderFlow.flow (3/2) t (x : ℂ)).re) at hx
  by_contra hneg
  have hn := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ x^4) (le_of_not_gt hneg)
  nlinarith

theorem eventually_actual_flow_nonzero (t : ℝ) (ht : t ≠ 0) :
    ∀ᶠ x : ℝ in cocompact ℝ, RiemannRealOrderFlow.flow (3/2) t (x : ℂ) ≠ 0 := by
  filter_upwards [eventually_time_signed_positive t ht] with x hx
  intro hz
  rw [hz,Complex.zero_re,mul_zero] at hx
  exact (lt_irrefl 0) hx

theorem actual_real_zero_set_finite (t : ℝ) (ht : t ≠ 0) :
    {x : ℝ | RiemannRealOrderFlow.flow (3/2) t (x : ℂ) = 0}.Finite := by
  let F : ℂ → ℂ := RiemannRealOrderFlow.flow (3/2) t
  have ha : AnalyticOnNhd ℂ F univ :=
    (RiemannRealOrderFlow.flow_differentiable (3/2) (by norm_num) t).differentiableOn.analyticOnNhd
      isOpen_univ
  have hn : F 0 ≠ 0 := by
    have hp := RiemannRealOrderFlow.actual_flow_zero_pos (3/2) (by norm_num) t
    intro hz
    change RiemannRealOrderFlow.flow (3/2) t 0 = 0 at hz
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hm0 : meromorphicOrderAt F 0 ≠ ⊤ := by
    rw [(ha 0 (mem_univ _)).meromorphicOrderAt_eq,
      (ha 0 (mem_univ _)).analyticOrderAt_eq_zero.mpr hn]
    simp
  have horder (z : ℂ) : meromorphicOrderAt F z ≠ ⊤ :=
    (ha.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).mp
      ⟨⟨0,mem_univ _⟩,hm0⟩ ⟨z,mem_univ _⟩
  have he : {x : ℝ | F (x : ℂ) ≠ 0} ∈ cocompact ℝ := eventually_actual_flow_nonzero t ht
  obtain ⟨K,hK,hsub⟩ := mem_cocompact'.mp he
  let L : Set ℂ := Complex.ofReal '' K
  have hL : IsCompact L := hK.image Complex.continuous_ofReal
  have hZ : (L ∩ F ⁻¹' {0}).Finite := by
    have hlocal := ha.mono (subset_univ L)
    rw [hlocal.meromorphicNFOn.zero_set_eq_divisor_support (fun z => horder z)]
    exact (MeromorphicOn.divisor F L).finiteSupport hL
  have hpre : (Complex.ofReal ⁻¹' (L ∩ F ⁻¹' {0})).Finite :=
    Set.Finite.preimage (fun x _ y _ h => Complex.ofReal_injective h) hZ
  apply hpre.subset
  intro x hx
  change F (x : ℂ) = 0 at hx
  have hxK : x ∈ K := hsub (by simpa only [mem_compl_iff,mem_setOf_eq,not_not] using hx)
  exact ⟨⟨x,hxK,rfl⟩,hx⟩

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderCubicEndpoint
