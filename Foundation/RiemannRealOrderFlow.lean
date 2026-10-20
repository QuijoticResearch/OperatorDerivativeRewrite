import Foundation.RiemannEvenEntireGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
/-! Genuine real-order arithmetic Fourier flows. The multiplier is the REAL
function |u|^(2a); no holomorphic complex-power branch is selected. Integer
agreement and entire spatial dependence require actual integral proofs. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFlow
open RiemannQuarticKernel
open RiemannQuarticFlow (halfLine)

def weighted (a : ℝ) (j : ℕ) (t B u : ℝ) : ℝ :=
  u^j*Real.exp (t*|u|^(2*a)+B*u)*kernel u

def integrand (a : ℝ) (j : ℕ) (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (weighted a 0 t 0 u : ℂ)*(Complex.I*(u : ℂ))^j*Complex.exp (Complex.I*(u : ℂ)*z)

def jet (a : ℝ) (j : ℕ) (t : ℝ) (z : ℂ) : ℂ := ∫ u, integrand a j t z u ∂halfLine

def flow (a t : ℝ) (z : ℂ) : ℂ := (jet a 0 t z+jet a 0 t (-z))/2

theorem real_power_bound (a : ℝ) (N : ℕ) (ha : 0 ≤ a) (haN : a ≤ N)
    (u : ℝ) (hu : 0 ≤ u) : |u|^(2*a) ≤ 1+u^(2*(N+2)) := by
  rw [abs_of_nonneg hu]
  by_cases h : u ≤ 1
  · have hh := Real.rpow_le_one hu h (show 0 ≤ 2*a by positivity)
    linarith [pow_nonneg hu (2*(N+2))]
  · have horder : 2*a ≤ ((2*(N+2) : ℕ) : ℝ) := by push_cast; linarith
    have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) horder
    rw [Real.rpow_natCast] at hh
    linarith

theorem weighted_nonneg (a : ℝ) (j : ℕ) (t B u : ℝ) (hu : 0 ≤ u) :
    0 ≤ weighted a j t B u := by
  unfold weighted
  exact mul_nonneg (mul_nonneg (pow_nonneg hu _) (Real.exp_pos _).le) (kernel_pos u hu).le

theorem weighted_mono (a : ℝ) (j : ℕ) {t T B C u : ℝ}
    (ht : t ≤ T) (hB : B ≤ C) (hu : 0 ≤ u) :
    weighted a j t B u ≤ weighted a j T C u := by
  unfold weighted
  apply mul_le_mul_of_nonneg_right _ (kernel_pos u hu).le
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
  apply Real.exp_le_exp.mpr
  exact add_le_add (mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (abs_nonneg _) _))
    (mul_le_mul_of_nonneg_right hB hu)

theorem weighted_tilt_bound (a : ℝ) (N j : ℕ) (ha : 0 ≤ a) (haN : a ≤ N)
    (t T R u : ℝ) (hT : 0 ≤ T) (ht : t ≤ T) (hR : 0 ≤ R) (hu : 0 ≤ u) :
    weighted a j t R u ≤ Real.exp (T+1+R*Real.sqrt R)*
      RiemannEvenDomain.weighted (N+2) j (T+1) 0 u := by
  have hp := real_power_bound a N ha haN u hu
  have h3 : u^3 ≤ 1+u^(2*(N+2)) := by
    by_cases h : u ≤ 1
    · have hh := pow_le_pow_left₀ hu h 3
      norm_num at hh
      linarith [pow_nonneg hu (2*(N+2))]
    · have hh := pow_le_pow_right₀ (le_of_not_ge h) (show 3 ≤ 2*(N+2) by omega)
      linarith
  have hlin := RiemannQuarticEntireGrowth.linear_tilt_bound R u hR hu
  have htime := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (abs_nonneg u) (2*a))
  have hpoly := mul_le_mul_of_nonneg_left hp hT
  have hphase : t*|u|^(2*a)+R*u ≤ T+1+R*Real.sqrt R+(T+1)*u^(2*(N+2)) := by
    nlinarith
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (pow_nonneg hu j)
  have hbound := mul_le_mul_of_nonneg_right he (kernel_pos u hu).le
  convert hbound using 1 <;>
    simp only [weighted,RiemannEvenDomain.weighted,zero_mul,add_zero,Real.exp_add] <;> ring

theorem weighted_continuousOn (a : ℝ) (ha : 0 ≤ a) (j : ℕ) (t B : ℝ) :
    ContinuousOn (weighted a j t B) (Ici 0) := by
  have hp : Continuous (fun u : ℝ => |u|^(2*a)) :=
    (Real.continuous_rpow_const (by positivity : 0 ≤ 2*a)).comp continuous_abs
  have h : Continuous (fun u : ℝ => u^j*Real.exp (t*|u|^(2*a)+B*u)) := by fun_prop
  exact h.continuousOn.mul kernel_continuousOn

theorem weighted_integrable (a : ℝ) (ha : 0 ≤ a) (j : ℕ) (t B : ℝ) :
    Integrable (weighted a j t B) halfLine := by
  obtain ⟨N,hN⟩ := exists_nat_ge a
  let T := max t 0
  let R := max B 0
  have hmajor : Integrable (fun u : ℝ => Real.exp (T+1+R*Real.sqrt R)*
      RiemannEvenDomain.weighted (N+2) j (T+1) 0 u) halfLine :=
    (RiemannEvenDomain.weighted_integrable (N+2) j (T+1) 0).const_mul _
  apply hmajor.mono' ((weighted_continuousOn a ha j t B).aestronglyMeasurable measurableSet_Ici)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  rw [Real.norm_eq_abs,abs_of_nonneg (weighted_nonneg a j t B u hu)]
  exact (weighted_mono a j le_rfl (le_max_left _ _) hu).trans
    (weighted_tilt_bound a N j ha hN t T R u (le_max_right _ _) (le_max_left _ _) (le_max_right _ _) hu)

theorem integrand_bound (a : ℝ) (j : ℕ) (t : ℝ) (z : ℂ) (u : ℝ) (hu : 0 ≤ u) :
    ‖integrand a j t z u‖ ≤ weighted a j t ‖z‖ u := by
  have hp := ComplexRootExponentialDomain.phase_norm_bound u z
  rw [abs_of_nonneg hu] at hp
  have hw := weighted_nonneg a 0 t 0 u hu
  simp only [integrand,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hw,Complex.norm_I,one_mul,abs_of_nonneg hu]
  calc
    _ ≤ weighted a 0 t 0 u*u^j*Real.exp (u*‖z‖) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hw (pow_nonneg hu _))
    _ = weighted a j t ‖z‖ u := by
      simp only [weighted,pow_zero,one_mul,zero_mul,add_zero,Real.exp_add]
      ring

theorem integrand_continuousOn (a : ℝ) (ha : 0 ≤ a) (j : ℕ) (t : ℝ) (z : ℂ) :
    ContinuousOn (integrand a j t z) (Ici 0) := by
  exact (((Complex.continuous_ofReal.comp_continuousOn (weighted_continuousOn a ha 0 t 0)).mul
    (by fun_prop : Continuous (fun u : ℝ => (Complex.I*(u : ℂ))^j)).continuousOn).mul
    (by fun_prop : Continuous (fun u : ℝ => Complex.exp (Complex.I*(u : ℂ)*z))).continuousOn)

theorem integrand_integrable (a : ℝ) (ha : 0 ≤ a) (j : ℕ) (t : ℝ) (z : ℂ) :
    Integrable (integrand a j t z) halfLine := by
  apply (weighted_integrable a ha j t ‖z‖).mono'
    ((integrand_continuousOn a ha j t z).aestronglyMeasurable measurableSet_Ici)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  exact integrand_bound a j t z u hu

theorem integrand_hasDerivAt (a : ℝ) (j : ℕ) (t u : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => integrand a j t w u) (integrand a (j+1) t z u) z := by
  have h := BandLimitedEntireCalculus.phase_derivative
    (fun v => (weighted a 0 t 0 v : ℂ)*(Complex.I*(v : ℂ))^j) u z
  convert h using 1
  · rfl
  · simp only [integrand,BandLimitedEntireCalculus.derivativeProfile,pow_succ]
    ring

theorem jet_hasDerivAt (a : ℝ) (ha : 0 ≤ a) (j : ℕ) (t : ℝ) (z₀ : ℂ) :
    HasDerivAt (jet a j t) (jet a (j+1) t z₀) z₀ := by
  let s : Set ℂ := {z | ‖z‖ ≤ ‖z₀‖+1}
  have hs : s ∈ 𝓝 z₀ := by
    have ht := (continuous_norm : Continuous (fun z : ℂ => ‖z‖)).continuousAt.tendsto (x := z₀)
    exact (ht.eventually (Iio_mem_nhds (by linarith : ‖z₀‖ < ‖z₀‖+1))).mono fun _ h => h.le
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := halfLine) (F := fun z u => integrand a j t z u)
    (F' := fun z u => integrand a (j+1) t z u) hs
    (Eventually.of_forall fun z => (integrand_integrable a ha j t z).aestronglyMeasurable)
    (integrand_integrable a ha j t z₀) (integrand_integrable a ha (j+1) t z₀).aestronglyMeasurable
    (bound := weighted a (j+1) t (‖z₀‖+1)) ?_
    (weighted_integrable a ha (j+1) t (‖z₀‖+1)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    intro z hz
    exact (integrand_bound a (j+1) t z u hu).trans (weighted_mono a (j+1) le_rfl hz hu)
  · exact Eventually.of_forall fun u z _ => integrand_hasDerivAt a j t u z

theorem flow_differentiable (a : ℝ) (ha : 0 ≤ a) (t : ℝ) : Differentiable ℂ (flow a t) := by
  have hj (j : ℕ) : Differentiable ℂ (jet a j t) := fun z => (jet_hasDerivAt a ha j t z).differentiableAt
  exact ((hj 0).add ((hj 0).comp differentiable_neg)).div_const 2

theorem weighted_nat (m j : ℕ) (t B u : ℝ) (hu : 0 ≤ u) :
    weighted (m : ℝ) j t B u=RiemannEvenDomain.weighted m j t B u := by
  have he : 2*(m : ℝ)=((2*m : ℕ) : ℝ) := by push_cast; ring
  simp only [weighted,RiemannEvenDomain.weighted,abs_of_nonneg hu,he,Real.rpow_natCast]

theorem jet_nat (m j : ℕ) (t : ℝ) (z : ℂ) : jet (m : ℝ) j t z=RiemannEvenFlow.jet m j t z := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  simp only [integrand,RiemannEvenFlow.integrand,weighted_nat m 0 t 0 u hu]

theorem flow_nat (m : ℕ) (t : ℝ) (z : ℂ) : flow (m : ℝ) t z=RiemannEvenFlow.flow m t z := by
  simp only [flow,RiemannEvenFlow.flow,jet_nat]

theorem cosine_integrand (a t u : ℝ) (z : ℂ) :
    (integrand a 0 t z u+integrand a 0 t (-z) u)/2 =
      (weighted a 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*z) := by
  simp only [integrand,pow_zero,mul_one,Complex.cos]
  rw [show Complex.I*(u : ℂ)*z=((u : ℂ)*z)*Complex.I by ring,
    show Complex.I*(u : ℂ)*(-z)=-((u : ℂ)*z)*Complex.I by ring]
  ring

theorem cosine_integrable (a : ℝ) (ha : 0 ≤ a) (t : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => (weighted a 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*z)) halfLine := by
  have h := ((integrand_integrable a ha 0 t z).add (integrand_integrable a ha 0 t (-z))).div_const 2
  exact h.congr (Eventually.of_forall fun u => cosine_integrand a t u z)

theorem flow_eq_cosine_integral (a : ℝ) (ha : 0 ≤ a) (t : ℝ) (z : ℂ) :
    flow a t z=∫ u, (weighted a 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*z) ∂halfLine := by
  unfold flow jet
  rw [← integral_add (integrand_integrable a ha 0 t z) (integrand_integrable a ha 0 t (-z)),
    ← integral_div]
  exact integral_congr_ae (Eventually.of_forall fun u => cosine_integrand a t u z)

theorem flow_even (a t : ℝ) (z : ℂ) : flow a t (-z)=flow a t z := by
  simp only [flow,neg_neg,add_comm]

theorem flow_conj (a : ℝ) (ha : 0 ≤ a) (t : ℝ) (z : ℂ) :
    flow a t (conj z)=conj (flow a t z) := by
  rw [flow_eq_cosine_integral a ha,flow_eq_cosine_integral a ha,← integral_conj]
  apply integral_congr_ae
  filter_upwards with u
  simp only [map_mul,Complex.conj_ofReal,← Complex.cos_conj]

theorem flow_zero_eq_mass (a t : ℝ) :
    flow a t 0=((∫ u : ℝ, weighted a 0 t 0 u ∂halfLine : ℝ) : ℂ) := by
  simp only [flow,neg_zero,add_self_div_two,jet,integrand,pow_zero,mul_one,mul_zero,
    Complex.exp_zero]
  exact integral_ofReal

theorem actual_flow_zero_pos (a : ℝ) (ha : 0 ≤ a) (t : ℝ) : 0 < (flow a t 0).re := by
  rw [flow_zero_eq_mass,Complex.ofReal_re]
  have hp (u : ℝ) (hu : 0 ≤ u) : 0 < weighted a 0 t 0 u := by
    simp only [weighted,pow_zero,one_mul,zero_mul,add_zero]
    exact mul_pos (Real.exp_pos _) (kernel_pos u hu)
  apply (setIntegral_pos_iff_support_of_nonneg_ae (μ := volume) (s := Ici (0 : ℝ))
    (by filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu; exact (hp u hu).le)
    (weighted_integrable a ha 0 t 0)).mpr
  have hs : Icc (0 : ℝ) 1 ⊆ Function.support (weighted a 0 t 0) ∩ Ici 0 := by
    intro u hu
    exact ⟨(hp u hu.1).ne',hu.1⟩
  exact lt_of_lt_of_le (by simp : 0 < volume (Icc (0 : ℝ) 1)) (measure_mono hs)

theorem flow_zero_time (a : ℝ) (z : ℂ) : flow a 0 z=RiemannEvenFlow.flow 1 0 z := by
  have hj (w : ℂ) : jet a 0 0 w=RiemannEvenFlow.jet 1 0 0 w := by
    apply integral_congr_ae
    filter_upwards with u
    simp only [integrand,RiemannEvenFlow.integrand,weighted,RiemannEvenDomain.weighted,
      zero_mul,zero_add]
  simp only [flow,RiemannEvenFlow.flow,hj]

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFlow
