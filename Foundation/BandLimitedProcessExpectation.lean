import Foundation.BandLimitedComplexExtension

/-! Actual stochastic expectations of compact-frequency complex Fourier extensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BandLimitedProcessExpectation
open BandLimitedComplexExtension

theorem shifted_joint_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (κ : ℝ) (t : ℝ≥0) (a : ℝ) :
    Integrable (fun p : ℝ × ℂ => φ p.1*Complex.exp (Complex.I*((p.1+κ : ℝ) : ℂ)*p.2))
      ((band R).prod (ComplexRootPoissonLaw.law t a)) := by
  have hdom := hφ.norm.mul_prod
    (ComplexRootExponentialDomain.radial_real_integrable t a ((R : ℝ)+|κ|) (by positivity))
  have hm : AEStronglyMeasurable (fun p : ℝ × ℂ =>
      φ p.1*Complex.exp (Complex.I*((p.1+κ : ℝ) : ℂ)*p.2))
      ((band R).prod (ComplexRootPoissonLaw.law t a)) :=
    hφ.aestronglyMeasurable.comp_fst.mul
      (by fun_prop : Measurable (fun p : ℝ × ℂ =>
        Complex.exp (Complex.I*((p.1+κ : ℝ) : ℂ)*p.2))).aestronglyMeasurable
  apply hdom.mono' hm
  have hp : MeasurePreserving (Prod.fst : ℝ × ℂ → ℝ)
      ((band R).prod (ComplexRootPoissonLaw.law t a)) (band R) := measurePreserving_fst
  filter_upwards [hp.quasiMeasurePreserving.ae (frequency_bound R)] with p hξ
  change ‖φ p.1*Complex.exp (Complex.I*((p.1+κ : ℝ) : ℂ)*p.2)‖ ≤
    ‖φ p.1‖*Real.exp (((R : ℝ)+|κ|)*‖p.2‖)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (ComplexRootExponentialDomain.phase_norm_bound (p.1+κ) p.2).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    ((abs_add_le _ _).trans (add_le_add hξ (le_refl |κ|))) (norm_nonneg _)

theorem shifted_compound_mean (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (κ : ℝ) (t : ℝ≥0) (a : ℝ) :
    (∫ z, (∫ η, φ η*Complex.exp (Complex.I*((η+κ : ℝ) : ℂ)*z) ∂band R)
      ∂ComplexRootPoissonLaw.law t a) =
      ∫ η, φ η*Complex.exp ((t : ℂ)*MarkedHolomorphicExponential.symbol a (η+κ)) ∂band R := by
  rw [← integral_integral_swap (shifted_joint_integrable R φ hφ κ t a)]
  simp_rw [integral_const_mul, ComplexRootPoissonTransform.transform]
  rfl

theorem compound_mean (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (t : ℝ≥0) (a : ℝ) :
    (∫ z, extension R φ z ∂ComplexRootPoissonLaw.law t a) =
      ∫ η, φ η*Complex.exp ((t : ℂ)*MarkedHolomorphicExponential.symbol a η) ∂band R := by
  simpa only [extension, add_zero] using shifted_compound_mean R φ hφ 0 t a

theorem process_mean (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (t : ℝ≥0) (a : ℝ) :
    (∫ ω, extension R φ (MarkedRenewalMartingale.process a t ω)
      ∂MarkedRootRenewalProcess.probability) =
      ∫ η, φ η*Complex.exp ((t : ℂ)*MarkedHolomorphicExponential.symbol a η) ∂band R := by
  have he := integral_map (μ := MarkedRootRenewalProcess.probability)
    (MarkedRenewalMartingale.process_measurable a t).aemeasurable
    (extension_continuous R φ hφ).aestronglyMeasurable
  rw [MarkedRenewalMartingale.process_law] at he
  exact he.symm.trans (compound_mean R φ hφ t a)

theorem tilted_mean (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (κ : ℝ) (t : ℝ≥0) (a : ℝ) :
    (∫ᵛ z, extension R φ z ∂[ContinuousLinearMap.mul ℝ ℂ; ComplexRootTiltedLaw.law a κ t]) =
      ∫ η, φ η*Complex.exp ((t : ℂ)*(MarkedHolomorphicExponential.symbol a (η+κ)-
        MarkedHolomorphicExponential.symbol a κ)) ∂band R := by
  have hi := ComplexDensityUnbounded.integrable_product (ComplexRootPoissonLaw.law t a)
    (ComplexRootTiltedLaw.density a κ t) (ComplexRootTiltedLaw.density_integrable a κ t)
    (extension R φ) (extension_continuous R φ hφ).measurable
    (tilted_integrable R φ hφ t a κ)
  rw [ComplexRootTiltedLaw.law, ComplexDensityUnbounded.integral_density _ _
    (ComplexRootTiltedLaw.density_integrable a κ t) (extension R φ)
    (extension_continuous R φ hφ).measurable hi]
  have hfun : (fun z => extension R φ z*ComplexRootTiltedLaw.density a κ t z) =
      (fun z => Complex.exp (-(t : ℂ)*MarkedHolomorphicExponential.symbol a κ) *
        ∫ η, φ η*Complex.exp (Complex.I*((η+κ : ℝ) : ℂ)*z) ∂band R) := by
    funext z
    unfold extension ComplexRootTiltedLaw.density
    rw [mul_left_comm, ← integral_mul_const]
    congr 1
    apply integral_congr_ae
    filter_upwards with η
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfun, integral_const_mul, shifted_compound_mean R φ hφ κ t a, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with η
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

end OperatorDerivativeRewrite.Foundation.BandLimitedProcessExpectation
