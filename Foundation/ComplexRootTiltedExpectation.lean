import Foundation.ComplexRootTiltedSemigroup
import Foundation.ComplexRootTiltedLaw

/-! The compensated operator semigroup is realized by actual finite complex coordinate laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootTiltedExpectation
open ComplexRootTransitionOperator (Test)
open ComplexRootTiltedStep ComplexRootTiltedWalk ComplexRootTiltedSemigroup

local instance : Nontrivial Test := ⟨⟨BoundedContinuousFunction.const ℂ 0,
    BoundedContinuousFunction.const ℂ 1, by
      intro h
      have he := congrArg (fun f : Test => f 0) h
      norm_num at he⟩⟩
local instance : NormOneClass (Test →L[ℂ] Test) := ⟨ContinuousLinearMap.norm_id⟩

theorem average_compound_expectation (a ξ : ℝ) (r : ℝ≥0) (f : Test) (z : ℂ) :
    (∫ n : ℕ, ((weightedStep a ξ)^n) f z ∂poissonMeasure r) =
      ∫ y, Complex.exp (Complex.I*(ξ : ℂ)*y) * f (z+y)
        ∂ComplexRootPoissonLaw.law r a := by
  let F : ℂ → ℂ := fun y => Complex.exp (Complex.I*(ξ : ℂ)*y) * f (z+y)
  have hF : Continuous F :=
    ((continuous_const.mul continuous_id).cexp).mul
      (f.continuous.comp (continuous_const.add continuous_id))
  have hi : Integrable F (ComplexRootPoissonLaw.law r a) :=
    (ComplexRootPoissonTransform.exponential_integrable r a ξ).mul_bdd
      (f.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => f.norm_coe_le_norm (z+y))
  rw [ComplexRootPoissonLaw.law_sum] at hi
  have hs := hasSum_integral_measure hi
  simp_rw [integral_smul_measure, ENNReal.toReal_ofReal (ComplexRootPoissonLaw.weight_nonneg r _),
    ComplexRootPoissonGrowth.walk_integral a F hF] at hs
  have hiN : Integrable (fun n : ℕ => ((weightedStep a ξ)^n) f z) (poissonMeasure r) := by
    apply ((PoissonEntireMoments.real_powers_integrable r ‖weightedStep a ξ‖).mul_const ‖f‖).mono'
      StronglyMeasurable.of_discrete.aestronglyMeasurable
    exact Eventually.of_forall fun n =>
      ((((weightedStep a ξ)^n) f).norm_coe_le_norm z).trans
        ((((weightedStep a ξ)^n).le_opNorm f).trans
          (mul_le_mul_of_nonneg_right (norm_pow_le (weightedStep a ξ) n) (norm_nonneg f)))
  have hn := hasSum_integral_poissonMeasure hiN
  change HasSum (fun n => ComplexRootPoissonLaw.weight r n • ((weightedStep a ξ)^n) f z)
    (∫ n : ℕ, ((weightedStep a ξ)^n) f z ∂poissonMeasure r) at hn
  simp_rw [weightedStep_pow_apply] at hn
  have he := hn.unique hs
  rw [← ComplexRootPoissonLaw.law_sum] at he
  simp_rw [weightedStep_pow_apply]
  exact he

theorem transition_law (a ξ : ℝ) (r : ℝ≥0) (f : Test) (z : ℂ) :
    transition a ξ r f z = ∫ᵛ y, f (z+y)
      ∂[ContinuousLinearMap.mul ℝ ℂ; ComplexRootTiltedLaw.law a ξ r] := by
  rw [transition_average_apply, average_compound_expectation,
    ComplexRootTiltedLaw.law, ComplexDensityIntegral.integral_density _ _
      (ComplexRootTiltedLaw.density_integrable a ξ r) (fun y : ℂ => f (z+y))
      (f.continuous.comp (continuous_const.add continuous_id)).measurable
      ‖f‖ (norm_nonneg f) (fun y => f.norm_coe_le_norm (z+y))]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  unfold ComplexRootTiltedLaw.density
  ring

end OperatorDerivativeRewrite.Foundation.ComplexRootTiltedExpectation
