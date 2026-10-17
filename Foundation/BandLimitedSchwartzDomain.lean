import Foundation.BandLimitedComplexExtension
import Foundation.SmoothAtomicJet
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Concrete admissible Schwartz tests from smooth compactly supported spectral profiles. -/
noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped NNReal Topology SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.BandLimitedSchwartzDomain
open BandLimitedComplexExtension

def smoothProfile : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ (SmoothAtomicJet.bump : ℝ → ℝ)) :=
    SmoothAtomicJet.bump.hasCompactSupport.comp_left rfl
  exact hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp SmoothAtomicJet.bump.contDiff)

theorem smoothProfile_zero_outside (x : ℝ) (hx : x ∉ Icc (-2 : ℝ) 2) : smoothProfile x = 0 := by
  have ha : 2 ≤ |x| := by
    by_contra h
    exact hx (abs_le.mp (lt_of_not_ge h).le)
  change (SmoothAtomicJet.bump x : ℂ) = 0
  rw [SmoothAtomicJet.bump.zero_of_le_dist (by simpa [SmoothAtomicJet.bump, Real.dist_eq] using ha)]
  simp

theorem smoothProfile_nonzero : smoothProfile ≠ 0 := by
  intro he
  have hz := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) he
  change (SmoothAtomicJet.bump 0 : ℂ) = 0 at hz
  have hb : SmoothAtomicJet.bump 0 = 1 :=
    SmoothAtomicJet.bump.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_self]
      exact SmoothAtomicJet.bump.rIn_pos.le)
  rw [hb, Complex.ofReal_one] at hz
  exact one_ne_zero hz

theorem scaled_fourierInv (R : ℝ≥0) (φ : 𝓢(ℝ, ℂ))
    (hφ : ∀ ξ, ξ ∉ Icc (-(R : ℝ)) (R : ℝ) → φ ξ = 0) (x : ℝ) :
    extension R φ ((2*Real.pi*x : ℝ) : ℂ) = (𝓕⁻ φ) x := by
  rw [SchwartzMap.fourierInv_coe]
  rw [extension, band, setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun ξ hξ => by rw [hφ ξ hξ]; simp), Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

theorem scaled_trace_isSchwartz (R : ℝ≥0) (φ : 𝓢(ℝ, ℂ))
    (hφ : ∀ ξ, ξ ∉ Icc (-(R : ℝ)) (R : ℝ) → φ ξ = 0) :
    ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, extension R φ ((2*Real.pi*x : ℝ) : ℂ) = g x :=
  ⟨𝓕⁻ φ, scaled_fourierInv R φ hφ⟩

theorem concrete_process_integrable (t : ℝ≥0) (a : ℝ) :
    Integrable (fun ω => extension 2 smoothProfile (MarkedRenewalMartingale.process a t ω))
      MarkedRootRenewalProcess.probability :=
  process_integrable 2 smoothProfile smoothProfile.integrable.restrict t a

theorem concrete_nonzero_schwartz_trace :
    ∃ g : 𝓢(ℝ, ℂ), g ≠ 0 ∧
      ∀ x : ℝ, extension 2 smoothProfile ((2*Real.pi*x : ℝ) : ℂ) = g x := by
  refine ⟨𝓕⁻ smoothProfile, ?_, scaled_fourierInv 2 smoothProfile smoothProfile_zero_outside⟩
  intro he
  apply smoothProfile_nonzero
  have hf := congrArg (fun f : 𝓢(ℝ, ℂ) => 𝓕 f) he
  simpa using hf

theorem concrete_extension_nonzero : ∃ z : ℂ, extension 2 smoothProfile z ≠ 0 := by
  obtain ⟨g,hg,htrace⟩ := concrete_nonzero_schwartz_trace
  by_contra h
  have hz : ∀ z : ℂ, extension 2 smoothProfile z = 0 := by simpa using h
  apply hg
  ext x
  rw [← htrace x, hz]
  rfl

def schwartzObservable (z : ℂ) : ℂ :=
  extension 2 smoothProfile ((2*Real.pi : ℝ)*z)

theorem schwartzObservable_real (x : ℝ) :
    schwartzObservable x = (𝓕⁻ smoothProfile) x := by
  unfold schwartzObservable
  convert scaled_fourierInv 2 smoothProfile smoothProfile_zero_outside x using 1 <;> push_cast <;> rfl

theorem schwartzObservable_process_integrable (t : ℝ≥0) (a : ℝ) :
    Integrable (fun ω => schwartzObservable (MarkedRenewalMartingale.process a t ω))
      MarkedRootRenewalProcess.probability := by
  apply ComplexRootExponentialDomain.process_integrable t a schwartzObservable
    ((extension_continuous 2 smoothProfile smoothProfile.integrable.restrict).measurable.comp
      (by fun_prop : Measurable (fun z : ℂ => (2*Real.pi : ℝ)*z)))
    (∫ ξ, ‖smoothProfile ξ‖ ∂band 2) (4*Real.pi) (by positivity)
  intro z
  have hb := norm_bound 2 smoothProfile smoothProfile.integrable.restrict ((2*Real.pi : ℝ)*z)
  have hn : ‖(2*Real.pi : ℝ)*(z : ℂ)‖ = (2*Real.pi)*‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have he : (2 : ℝ)*((2*Real.pi)*‖z‖) = (4*Real.pi)*‖z‖ := by ring
  simpa only [schwartzObservable, show ((2 : ℝ≥0) : ℝ) = 2 from rfl, hn, he] using hb

end OperatorDerivativeRewrite.Foundation.BandLimitedSchwartzDomain
