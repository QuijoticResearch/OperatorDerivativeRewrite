import Foundation.RiemannQuarticFlow

/-! The literal growing arithmetic transform satisfies +D^4, on its actual
integral domain.  No assertion about zeros or its completed-zeta identification. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticEvolution
open RiemannQuarticKernel RiemannQuarticDomain RiemannQuarticFlow

theorem jet_iteratedDeriv (k n : ℕ) (t : ℝ) :
    iteratedDeriv n (jet k t) = jet (k+n) t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    simpa [Nat.add_assoc] using (jet_hasDerivAt (k+n) t z).deriv

theorem integrand_time_hasDerivAt (k : ℕ) (t u : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => integrand k s z u) (integrand (k+4) t z u) t := by
  have h := ((((hasDerivAt_id t).mul_const (u^4)).exp).ofReal_comp).mul_const
    ((kernel u : ℂ)*(Complex.I*(u : ℂ))^k*Complex.exp (Complex.I*(u : ℂ)*z))
  convert h using 1
  · funext s
    simp only [integrand, weighted, pow_zero, one_mul, zero_mul, add_zero,
      Complex.ofReal_mul, id_eq]
    ring
  · simp only [integrand, weighted, pow_zero, one_mul, zero_mul, add_zero,
      Complex.ofReal_mul, pow_add, mul_pow, Complex.I_pow_four, one_mul,
      Complex.ofReal_pow, id_eq]
    ring

theorem jet_time_hasDerivAt (k : ℕ) (t₀ : ℝ) (z : ℂ) :
    HasDerivAt (fun t : ℝ => jet k t z) (jet (k+4) t₀ z) t₀ := by
  let s : Set ℝ := {t | |t| ≤ |t₀|+1}
  have hs : s ∈ 𝓝 t₀ := by
    have ht := (continuous_abs : Continuous (fun t : ℝ => |t|)).continuousAt.tendsto (x := t₀)
    exact (ht.eventually (Iio_mem_nhds (by linarith : |t₀| < |t₀|+1))).mono fun _ h => h.le
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := halfLine) (F := fun t u => integrand k t z u)
    (F' := fun t u => integrand (k+4) t z u) hs
    (Eventually.of_forall fun t => (integrand_integrable k t z).aestronglyMeasurable)
    (integrand_integrable k t₀ z) (integrand_integrable (k+4) t₀ z).aestronglyMeasurable
    (bound := weighted (k+4) (|t₀|+1) ‖z‖) ?_
    (weighted_integrable (k+4) (|t₀|+1) ‖z‖) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    intro t ht
    exact (integrand_bound (k+4) t z u hu).trans
      (weighted_mono (k+4) ((le_abs_self t).trans ht) le_rfl hu)
  · exact Eventually.of_forall fun u t _ => integrand_time_hasDerivAt k t u z

def symmetricJet (k : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  (jet k t z+(-1 : ℂ)^k*jet k t (-z))/2

theorem symmetricJet_zero (t : ℝ) : symmetricJet 0 t = flow t := by
  funext z
  simp [symmetricJet, flow]

theorem symmetricJet_hasDerivAt (k : ℕ) (t : ℝ) (z : ℂ) :
    HasDerivAt (symmetricJet k t) (symmetricJet (k+1) t z) z := by
  have h := ((jet_hasDerivAt k t z).add
    (((jet_hasDerivAt k t (-z)).comp z (hasDerivAt_neg z)).const_mul ((-1 : ℂ)^k))).div_const 2
  convert h using 1
  · rfl
  · simp only [symmetricJet, pow_succ]
    ring

theorem flow_iteratedDeriv (n : ℕ) (t : ℝ) :
    iteratedDeriv n (flow t) = symmetricJet n t := by
  induction n with
  | zero => simp [symmetricJet_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (symmetricJet_hasDerivAt n t z).deriv

theorem fourth_order_heat_equation (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => flow s z) (iteratedDeriv 4 (flow t) z) t := by
  rw [flow_iteratedDeriv]
  have h := ((jet_time_hasDerivAt 0 t z).add
    (jet_time_hasDerivAt 0 t (-z))).const_smul (1/2 : ℝ)
  convert h using 1
  · funext s
    change (jet 0 s z+jet 0 s (-z))/2 = (1/2 : ℝ) • (jet 0 s z+jet 0 s (-z))
    rw [Complex.real_smul]
    push_cast
    ring
  · norm_num [symmetricJet, Complex.real_smul]
    ring

theorem cosine_integrand (t u : ℝ) (z : ℂ) :
    (integrand 0 t z u+integrand 0 t (-z) u)/2 =
      (weighted 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*z) := by
  simp only [integrand, pow_zero, mul_one, Complex.cos]
  rw [show Complex.I*(u : ℂ)*z=((u : ℂ)*z)*Complex.I by ring,
    show Complex.I*(u : ℂ)*(-z)=-((u : ℂ)*z)*Complex.I by ring]
  ring

theorem cosine_integrable (t : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => (weighted 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*z)) halfLine := by
  have h := ((integrand_integrable 0 t z).add (integrand_integrable 0 t (-z))).div_const 2
  exact h.congr (Eventually.of_forall fun u => cosine_integrand t u z)

theorem flow_eq_cosine_integral (t : ℝ) (z : ℂ) :
    flow t z = ∫ u, (weighted 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*z) ∂halfLine := by
  unfold flow jet
  rw [← integral_add (integrand_integrable 0 t z) (integrand_integrable 0 t (-z)),
    ← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => cosine_integrand t u z

theorem flow_even (t : ℝ) (z : ℂ) : flow t (-z) = flow t z := by
  simp only [flow, neg_neg, add_comm]

end OperatorDerivativeRewrite.Foundation.RiemannQuarticEvolution
