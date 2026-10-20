import Foundation.RiemannEvenDomain
import Foundation.RiemannQuarticFlow
import Foundation.BandLimitedEntireCalculus

/-! The growing integer-even transforms of the literal arithmetic kernel, with
actual half-line integrals and their complex spatial derivatives. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenFlow
open RiemannQuarticKernel RiemannEvenDomain
open RiemannQuarticFlow (halfLine)

def integrand (m k : ℕ) (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (weighted m 0 t 0 u : ℂ)*(Complex.I*(u : ℂ))^k*Complex.exp (Complex.I*(u : ℂ)*z)

theorem weighted_nonneg (m k : ℕ) (T B u : ℝ) (hu : 0 ≤ u) : 0 ≤ weighted m k T B u := by
  unfold weighted
  exact mul_nonneg (mul_nonneg (pow_nonneg hu _) (Real.exp_pos _).le) (kernel_pos u hu).le

theorem integrand_bound (m k : ℕ) (t : ℝ) (z : ℂ) (u : ℝ) (hu : 0 ≤ u) :
    ‖integrand m k t z u‖ ≤ weighted m k t ‖z‖ u := by
  have hp := ComplexRootExponentialDomain.phase_norm_bound u z
  rw [abs_of_nonneg hu] at hp
  have hw := weighted_nonneg m 0 t 0 u hu
  simp only [integrand, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hw, Complex.norm_I, one_mul, abs_of_nonneg hu]
  calc
    _ ≤ weighted m 0 t 0 u*u^k*Real.exp (u*‖z‖) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hw (pow_nonneg hu _))
    _ = weighted m k t ‖z‖ u := by
      simp only [weighted, pow_zero, one_mul, zero_mul, add_zero, Real.exp_add]
      ring

theorem integrand_continuousOn (m k : ℕ) (t : ℝ) (z : ℂ) :
    ContinuousOn (integrand m k t z) (Ici 0) := by
  exact (((Complex.continuous_ofReal.comp_continuousOn (weighted_continuousOn m 0 t 0)).mul
    (by fun_prop : Continuous (fun u : ℝ => (Complex.I*(u : ℂ))^k)).continuousOn).mul
    (by fun_prop : Continuous (fun u : ℝ => Complex.exp (Complex.I*(u : ℂ)*z))).continuousOn)

theorem integrand_integrable (m k : ℕ) (t : ℝ) (z : ℂ) :
    Integrable (integrand m k t z) halfLine := by
  apply (weighted_integrable m k t ‖z‖).mono'
    ((integrand_continuousOn m k t z).aestronglyMeasurable measurableSet_Ici)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  exact integrand_bound m k t z u hu

def jet (m k : ℕ) (t : ℝ) (z : ℂ) : ℂ := ∫ u, integrand m k t z u ∂halfLine

def flow (m : ℕ) (t : ℝ) (z : ℂ) : ℂ := (jet m 0 t z+jet m 0 t (-z))/2

theorem integrand_hasDerivAt (m k : ℕ) (t u : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => integrand m k t w u) (integrand m (k+1) t z u) z := by
  have h := BandLimitedEntireCalculus.phase_derivative
    (fun v => (weighted m 0 t 0 v : ℂ)*(Complex.I*(v : ℂ))^k) u z
  convert h using 1
  · rfl
  · simp only [integrand, BandLimitedEntireCalculus.derivativeProfile, pow_succ]
    ring

theorem jet_hasDerivAt (m k : ℕ) (t : ℝ) (z₀ : ℂ) :
    HasDerivAt (jet m k t) (jet m (k+1) t z₀) z₀ := by
  let s : Set ℂ := {z | ‖z‖ ≤ ‖z₀‖+1}
  have hs : s ∈ 𝓝 z₀ := by
    have ht := (continuous_norm : Continuous (fun z : ℂ => ‖z‖)).continuousAt.tendsto (x := z₀)
    exact (ht.eventually (Iio_mem_nhds (by linarith : ‖z₀‖ < ‖z₀‖+1))).mono fun _ h => h.le
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := halfLine) (F := fun z u => integrand m k t z u)
    (F' := fun z u => integrand m (k+1) t z u) hs
    (Eventually.of_forall fun z => (integrand_integrable m k t z).aestronglyMeasurable)
    (integrand_integrable m k t z₀) (integrand_integrable m (k+1) t z₀).aestronglyMeasurable
    (bound := weighted m (k+1) t (‖z₀‖+1)) ?_
    (weighted_integrable m (k+1) t (‖z₀‖+1)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    intro z hz
    exact (integrand_bound m (k+1) t z u hu).trans (weighted_mono m (k+1) le_rfl hz hu)
  · exact Eventually.of_forall fun u z _ => integrand_hasDerivAt m k t u z

theorem jet_differentiable (m k : ℕ) (t : ℝ) : Differentiable ℂ (jet m k t) :=
  fun z => (jet_hasDerivAt m k t z).differentiableAt

theorem flow_differentiable (m : ℕ) (t : ℝ) : Differentiable ℂ (flow m t) :=
  ((jet_differentiable m 0 t).add ((jet_differentiable m 0 t).comp differentiable_neg)).div_const 2

theorem flow_quartic (t : ℝ) : flow 2 t=RiemannQuarticFlow.flow t := rfl

end OperatorDerivativeRewrite.Foundation.RiemannEvenFlow
