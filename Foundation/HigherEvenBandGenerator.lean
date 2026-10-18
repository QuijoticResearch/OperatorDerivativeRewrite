import Foundation.HigherEvenBandHeatLimit
import Foundation.BandLimitedEntireCalculus

/-! Finite jump operators converge to the signed higher derivative on an explicit entire test domain. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherEvenBandGenerator
open BandLimitedComplexExtension BandLimitedEntireCalculus HigherEvenRenewalEnergy
open HigherEvenHeatTransformLimit HigherEvenBandHeatLimit

def profile (m : ℕ) [NeZero m] (n : ℕ) (φ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  φ ξ*HigherEvenRenewalTransform.normalizedSymbol m (smallAmplitude n) (Complex.I*(ξ : ℂ))

theorem symbol_measurable (m : ℕ) [NeZero m] (a : ℝ) :
    Measurable (fun ξ : ℝ => HigherEvenRenewalTransform.normalizedSymbol m a (Complex.I*(ξ : ℂ))) := by
  have hz : Measurable (HigherEvenRootInnovation.innovation m a) := measurable_of_countable _
  have hf : Measurable (fun p : ℝ × ZMod (2*m) => Complex.exp
      (Complex.I*(p.1 : ℂ)*HigherEvenRootInnovation.innovation m a p.2)) :=
    Complex.continuous_exp.measurable.comp
      ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_fst)).mul
        (hz.comp measurable_snd))
  exact measurable_const.mul
    ((hf.stronglyMeasurable.integral_prod_right'
      (ν := CyclicRootProbabilityNoise.probability (2*m))).measurable.sub measurable_const)

theorem profile_integrable (m : ℕ) [NeZero m] (n : ℕ) (R : ℝ≥0)
    (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) : Integrable (profile m n φ) (band R) := by
  apply hφ.mul_bdd (c := bound m R) (symbol_measurable m _).aestronglyMeasurable
  exact (frequency_bound R).mono fun ξ hξ => symbol_bound m n R ξ hξ

theorem mark_frequency_integrable (m : ℕ) [NeZero m] (a : ℝ) (R : ℝ≥0)
    (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) (x : ℂ) :
    Integrable (fun p : ZMod (2*m) × ℝ => φ p.2*Complex.exp
      (Complex.I*(p.2 : ℂ)*(x+HigherEvenRootInnovation.innovation m a p.1)))
      ((CyclicRootProbabilityNoise.probability (2*m)).prod (band R)) := by
  have hz : Measurable (HigherEvenRootInnovation.innovation m a) := measurable_of_countable _
  have hm : Measurable (fun p : ZMod (2*m) × ℝ => Complex.exp
      (Complex.I*(p.2 : ℂ)*(x+HigherEvenRootInnovation.innovation m a p.1))) :=
    Complex.continuous_exp.measurable.comp
      ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_snd)).mul
        (measurable_const.add (hz.comp measurable_fst)))
  apply (integrable_prod_iff
    (hφ.aestronglyMeasurable.comp_snd.mul hm.aestronglyMeasurable)).mpr
  exact ⟨Eventually.of_forall fun k => integrand_integrable R φ hφ
    (x+HigherEvenRootInnovation.innovation m a k),Integrable.of_finite⟩

theorem generator_identity (m : ℕ) [NeZero m] (n : ℕ) (R : ℝ≥0)
    (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) (x : ℂ) :
    CyclicPolynomialKernel.generator m (smallAmplitude n) (extension R φ) x =
      extension R (profile m n φ) x := by
  have hi := mark_frequency_integrable m (smallAmplitude n) R φ hφ x
  change (CyclicPolynomialKernel.rate m (smallAmplitude n) : ℂ)*
    ((∫ k, (∫ ξ, φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*
      (x+HigherEvenRootInnovation.innovation m (smallAmplitude n) k)) ∂band R)
        ∂CyclicRootProbabilityNoise.probability (2*m))-
      (∫ ξ, φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*x) ∂band R)) = _
  rw [integral_integral_swap hi,
    ← integral_sub hi.integral_prod_right (integrand_integrable R φ hφ x),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  have he (k : ZMod (2*m)) : φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*
      (x+HigherEvenRootInnovation.innovation m (smallAmplitude n) k)) =
    (φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*x))*Complex.exp
      (Complex.I*(ξ : ℂ)*HigherEvenRootInnovation.innovation m (smallAmplitude n) k) := by
    rw [mul_add,Complex.exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  unfold profile HigherEvenRenewalTransform.normalizedSymbol HigherEvenRenewalTransform.symbol
    HigherEvenRenewalTransform.markTransform MarkedRenewalExponentialTransform.oneStep
  ring

theorem generator_tendsto (m : ℕ) [NeZero m] (R : ℝ≥0)
    (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) (x : ℂ) :
    Tendsto (fun n => CyclicPolynomialKernel.generator m (smallAmplitude n) (extension R φ) x)
      atTop (𝓝 ((-1 : ℂ)^(m+1)*iteratedDeriv (2*m) (extension R φ) x)) := by
  simp_rw [generator_identity m _ R φ hφ x]
  rw [iterated_derivative_formula R φ hφ,extension,← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ => ‖φ ξ‖*bound m R*Real.exp ((R : ℝ)*‖x‖)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun n =>
      (integrand_integrable R _ (profile_integrable m n R φ hφ) x).aestronglyMeasurable
  · exact Eventually.of_forall fun n => (frequency_bound R).mono fun ξ hξ => by
      change ‖(φ ξ*HigherEvenRenewalTransform.normalizedSymbol m (smallAmplitude n)
        (Complex.I*(ξ : ℂ)))*Complex.exp (Complex.I*(ξ : ℂ)*x)‖ ≤ _
      simp only [norm_mul]
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left (symbol_bound m n R ξ hξ) (norm_nonneg _))
        ((ComplexRootExponentialDomain.phase_norm_bound ξ x).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hξ (norm_nonneg _))))
        (norm_nonneg _) (by unfold bound; positivity)
  · exact (hφ.norm.mul_const _).mul_const _
  · exact Eventually.of_forall fun ξ => by
      have h := ((symbol_tendsto m (Complex.I*(ξ : ℂ))).const_mul (φ ξ)).mul_const
        (Complex.exp (Complex.I*(ξ : ℂ)*x))
      simpa only [profile,orderProfile,mul_assoc,mul_left_comm,mul_comm] using h

end OperatorDerivativeRewrite.Foundation.HigherEvenBandGenerator
