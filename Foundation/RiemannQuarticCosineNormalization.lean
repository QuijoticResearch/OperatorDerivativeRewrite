import Foundation.RiemannQuarticCommonProfileLimit
/-! Nonvanishing common Gaussian normalization and a cosh-weighted error bound.
The normalized actual quartic flow is compared with cos(u*z) on growing disks.
This supplies quantitative input for zero counts, not zero counts themselves. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCosineNormalization
open RiemannQuarticCommonProfile RiemannQuarticCommonProfileLimit
open RiemannQuarticGaussianPrefactor RiemannQuarticPhaseRemainder
open RiemannQuarticSaddleTimes RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannQuarticDomain

def gaussianEnvelope (t u : ℝ) (z : ℂ) : ℂ :=
  saddleWeight t 0 (u : ℂ)*gaussianFactor t (u : ℂ)*
    Complex.exp (z^2/(2*deriv (complexSlope t) (u : ℂ)))

theorem envelope_ne_zero (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) : gaussianEnvelope t u z ≠ 0 := by
  have h := centerContribution_ne_zero t u ht hu hs 0
  simp only [centerContribution,quadraticSaddleWeight,zero_mul,mul_zero,zero_pow,
    Nat.cast_ofNat,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_div,add_zero,Complex.exp_zero,mul_one] at h
  exact mul_ne_zero h (Complex.exp_ne_zero _)

theorem center_eq_envelope_exp (t u : ℝ) (z : ℂ) :
    centerContribution t u z=gaussianEnvelope t u z*Complex.exp (Complex.I*(u : ℂ)*z) := by
  simp only [centerContribution,quadraticSaddleWeight,gaussianEnvelope,Complex.exp_add]
  ring

theorem center_norm_average (t u : ℝ) (z : ℂ) :
    (‖centerContribution t u z‖+‖centerContribution t u (-z)‖)/2=
      ‖gaussianEnvelope t u z‖*Real.cosh (u*z.im) := by
  have he : gaussianEnvelope t u (-z)=gaussianEnvelope t u z := by simp only [gaussianEnvelope,neg_sq]
  rw [center_eq_envelope_exp,center_eq_envelope_exp,he,norm_mul,norm_mul,
    Complex.norm_exp,Complex.norm_exp,Real.cosh_eq]
  have h1 : (Complex.I*(u : ℂ)*z).re= -(u*z.im) := by simp [Complex.mul_re,Complex.mul_im]
  have h2 : (Complex.I*(u : ℂ)*(-z)).re=u*z.im := by simp [Complex.mul_re,Complex.mul_im]
  rw [h1,h2]
  ring

theorem uniform_normalized_cosine (γ : ℝ) (hγ : γ < 2/3) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : phaseSlope t u=0) (z : ℂ),
      ‖z‖ ≤ (t*u^3+1)^γ →
      ‖RiemannQuarticFlow.flow t z/gaussianEnvelope t u z-Complex.cos ((u : ℂ)*z)‖ ≤
        ε*Real.cosh (u*z.im) := by
  filter_upwards [uniform_gaussian_cosine γ hγ ε hε] with t hmodel
  intro ht u hu hm hs z hz
  have h := hmodel ht u hu hm hs z hz
  change ‖RiemannQuarticFlow.flow t z-gaussianEnvelope t u z*Complex.cos ((u : ℂ)*z)‖ ≤ _ at h
  rw [show ε*(‖centerContribution t u z‖+‖centerContribution t u (-z)‖)/2=
    ε*((‖centerContribution t u z‖+‖centerContribution t u (-z)‖)/2) by ring,center_norm_average] at h
  have hn := envelope_ne_zero t u ht.le (by linarith) hs z
  have he : RiemannQuarticFlow.flow t z/gaussianEnvelope t u z-Complex.cos ((u : ℂ)*z)=
      (RiemannQuarticFlow.flow t z-gaussianEnvelope t u z*Complex.cos ((u : ℂ)*z))/gaussianEnvelope t u z := by field_simp
  rw [he,norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCosineNormalization
