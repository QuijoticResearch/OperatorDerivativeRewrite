import Foundation.RiemannEvenFlow
import Foundation.HigherEvenHeatTransformLimit
/-! Actual integer-even growing Xi-kernel flows and their signed generator.
The stable higher-heat Fourier multiplier has the opposite time direction. -/
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenEvolution
open RiemannEvenDomain RiemannEvenFlow RiemannQuarticKernel
open RiemannQuarticFlow (halfLine)

theorem jet_iteratedDeriv (m k n : ℕ) (t : ℝ) :
    iteratedDeriv n (jet m k t)=jet m (k+n) t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext z
    simpa [Nat.add_assoc] using (jet_hasDerivAt m (k+n) t z).deriv

private theorem growing_phase_power (m : ℕ) (u : ℝ) :
    (-1 : ℂ)^m*(Complex.I*(u : ℂ))^(2*m)=(u : ℂ)^(2*m) := by
  have h := HigherEvenHeatTransformLimit.fourier_exponent m u
  rw [pow_succ,mul_neg_one,neg_mul,neg_inj] at h
  exact h

theorem integrand_time_hasDerivAt (m k : ℕ) (t u : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => integrand m k s z u)
      ((-1 : ℂ)^m*integrand m (k+2*m) t z u) t := by
  have h := ((((hasDerivAt_id t).mul_const (u^(2*m))).exp).ofReal_comp).mul_const
    ((kernel u : ℂ)*(Complex.I*(u : ℂ))^k*Complex.exp (Complex.I*(u : ℂ)*z))
  have he := growing_phase_power m u
  convert h using 1
  · funext s
    simp only [integrand,weighted,pow_zero,one_mul,zero_mul,add_zero,Complex.ofReal_mul,id_eq]
    ring
  · simp only [integrand,weighted,pow_zero,one_mul,zero_mul,add_zero,Complex.ofReal_mul,
      Complex.ofReal_pow,id_eq,pow_add]
    linear_combination (Complex.exp (Complex.I*(u : ℂ)*z)*(Real.exp (t*u^(2*m)) : ℂ)*
      (kernel u : ℂ)*(Complex.I*(u : ℂ))^k)*he

theorem jet_time_hasDerivAt (m k : ℕ) (t₀ : ℝ) (z : ℂ) :
    HasDerivAt (fun t : ℝ => jet m k t z) ((-1 : ℂ)^m*jet m (k+2*m) t₀ z) t₀ := by
  let s : Set ℝ := {t | |t| ≤ |t₀|+1}
  have hs : s ∈ 𝓝 t₀ := by
    have ht := (continuous_abs : Continuous (fun t : ℝ => |t|)).continuousAt.tendsto (x := t₀)
    exact (ht.eventually (Iio_mem_nhds (by linarith : |t₀| < |t₀|+1))).mono fun _ h => h.le
  have hdi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := halfLine) (F := fun t u => integrand m k t z u)
    (F' := fun t u => (-1 : ℂ)^m*integrand m (k+2*m) t z u) hs
    (Eventually.of_forall fun t => (integrand_integrable m k t z).aestronglyMeasurable)
    (integrand_integrable m k t₀ z) ((integrand_integrable m (k+2*m) t₀ z).const_mul _).aestronglyMeasurable
    (bound := weighted m (k+2*m) (|t₀|+1) ‖z‖) ?_
    (weighted_integrable m (k+2*m) (|t₀|+1) ‖z‖) ?_
  · simpa only [jet,integral_const_mul] using hdi.2
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    intro t ht
    rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact (integrand_bound m (k+2*m) t z u hu).trans
      (weighted_mono m (k+2*m) ((le_abs_self t).trans ht) le_rfl hu)
  · exact Eventually.of_forall fun u t _ => integrand_time_hasDerivAt m k t u z

def symmetricJet (m k : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  (jet m k t z+(-1 : ℂ)^k*jet m k t (-z))/2

theorem symmetricJet_zero (m : ℕ) (t : ℝ) : symmetricJet m 0 t = flow m t := by
  funext z
  simp [symmetricJet, flow]

theorem symmetricJet_hasDerivAt (m k : ℕ) (t : ℝ) (z : ℂ) :
    HasDerivAt (symmetricJet m k t) (symmetricJet m (k+1) t z) z := by
  have h := ((jet_hasDerivAt m k t z).add
    (((jet_hasDerivAt m k t (-z)).comp z (hasDerivAt_neg z)).const_mul ((-1 : ℂ)^k))).div_const 2
  convert h using 1
  · rfl
  · simp only [symmetricJet, pow_succ]
    ring

theorem flow_iteratedDeriv (m n : ℕ) (t : ℝ) :
    iteratedDeriv n (flow m t) = symmetricJet m n t := by
  induction n with
  | zero => simp [symmetricJet_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (symmetricJet_hasDerivAt m n t z).deriv

theorem even_order_heat_equation (m : ℕ) (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => flow m s z)
      ((-1 : ℂ)^m*iteratedDeriv (2*m) (flow m t) z) t := by
  rw [flow_iteratedDeriv]
  have h := ((jet_time_hasDerivAt m 0 t z).add
    (jet_time_hasDerivAt m 0 t (-z))).const_smul (1/2 : ℝ)
  have hsign : (-1 : ℂ)^(2*m)=1 := by rw [pow_mul]; norm_num
  convert h using 1
  · funext s
    change (jet m 0 s z+jet m 0 s (-z))/2 = (1/2 : ℝ) • (jet m 0 s z+jet m 0 s (-z))
    rw [Complex.real_smul]
    push_cast
    ring
  · simp only [symmetricJet,hsign,one_mul,zero_add,Complex.real_smul]
    push_cast
    ring

theorem sixth_order_heat_equation (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => flow 3 s z) (-iteratedDeriv 6 (flow 3 t) z) t := by
  have h := even_order_heat_equation 3 t z
  norm_num at h
  exact h

theorem cosine_integrand (m : ℕ) (t u : ℝ) (z : ℂ) :
    (integrand m 0 t z u+integrand m 0 t (-z) u)/2 =
      (weighted m 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*z) := by
  simp only [integrand, pow_zero, mul_one, Complex.cos]
  rw [show Complex.I*(u : ℂ)*z=((u : ℂ)*z)*Complex.I by ring,
    show Complex.I*(u : ℂ)*(-z)=-((u : ℂ)*z)*Complex.I by ring]
  ring

theorem cosine_integrable (m : ℕ) (t : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => (weighted m 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*z)) halfLine := by
  have h := ((integrand_integrable m 0 t z).add (integrand_integrable m 0 t (-z))).div_const 2
  exact h.congr (Eventually.of_forall fun u => cosine_integrand m t u z)

theorem flow_eq_cosine_integral (m : ℕ) (t : ℝ) (z : ℂ) :
    flow m t z = ∫ u, (weighted m 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*z) ∂halfLine := by
  unfold flow jet
  rw [← integral_add (integrand_integrable m 0 t z) (integrand_integrable m 0 t (-z)),
    ← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => cosine_integrand m t u z

theorem flow_even (m : ℕ) (t : ℝ) (z : ℂ) : flow m t (-z) = flow m t z := by
  simp only [flow, neg_neg, add_comm]


end OperatorDerivativeRewrite.Foundation.RiemannEvenEvolution
