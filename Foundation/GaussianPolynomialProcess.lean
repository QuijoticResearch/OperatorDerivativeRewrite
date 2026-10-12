import Foundation.GaussianPolynomialHeat
import Foundation.GaussianWeightedTimeHermite

/-! Actual L² evaluation and time integration of arbitrary space-time polynomials. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPolynomialProcess
open InfiniteGaussian GaussianPolynomialHeat GaussianTerminalRepresentation
open GaussianTimeSpaceHermite GaussianHermiteIntegrand GaussianTimeProcess

def valueL2 (t : ℝ≥0) : SpaceTimePolynomial →ₗ[ℝ] GaussianL2 :=
  (terminalPolynomial t).comp (specialize t).toLinearMap

theorem valueL2_coeFn (t : ℝ≥0) (p : SpaceTimePolynomial) :
    valueL2 t p =ᵐ[gaussianProduct] fun ω => eval ![(t : ℝ), process t ω] p := by
  filter_upwards [GaussianTimeDivergence.pastCoefficient_coeFn
    (fun _ : Unit => t) (specialize t p)] with ω hω
  exact hω.trans (eval_specialize _ _ _)

theorem valueL2_basis (t : ℝ≥0) (k n : ℕ) :
    valueL2 t (basisPolynomial (k, n)) = (t : ℝ) ^ k • (brownianCore t n : GaussianL2) := by
  change terminalPolynomial t (specialize t _) = _
  rw [specialize_basis, map_smul, terminalPolynomial_hermite]

theorem valueL2_continuous (p : SpaceTimePolynomial) : Continuous (fun t => valueL2 t p) := by
  have hp : p ∈ Submodule.span ℝ (Set.range basisPolynomial) := by rw [basisPolynomial_span]; trivial
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨⟨k, n⟩, rfl⟩ := hp
    simp only [valueL2_basis]
    exact (NNReal.continuous_coe.pow k).smul (brownianCore_continuous n)
  | zero => simp only [map_zero]; exact continuous_const
  | add p q hp hq ihp ihq =>
    simp only [map_add]
    exact continuous_add.comp (ihp.prodMk ihq)
  | smul c p hp ih =>
    simp only [map_smul]
    exact continuous_smul.comp ((continuous_const : Continuous (fun _ : ℝ≥0 => c)).prodMk ih)

theorem valueL2_intervalIntegrable (p : SpaceTimePolynomial) (T : ℝ≥0) :
    IntervalIntegrable (fun t => valueL2 t.toNNReal p) volume 0 T :=
  ((valueL2_continuous p).comp continuous_real_toNNReal).intervalIntegrable _ _

def timeIntegral (T : ℝ≥0) : SpaceTimePolynomial →ₗ[ℝ] GaussianL2 where
  toFun p := ∫ t in 0..(T : ℝ), valueL2 t.toNNReal p
  map_add' p q := by
    simp only [map_add]
    exact intervalIntegral.integral_add (valueL2_intervalIntegrable p T) (valueL2_intervalIntegrable q T)
  map_smul' c p := by simp only [map_smul, intervalIntegral.integral_smul, RingHom.id_apply]

def noiseTarget (T : ℝ≥0) : SpaceTimePolynomial →ₗ[ℝ] GaussianL2 :=
  valueL2 T - valueL2 0 - (timeIntegral T).comp heat

theorem noiseTarget_apply (T : ℝ≥0) (p : SpaceTimePolynomial) :
    noiseTarget T p = valueL2 T p - valueL2 0 p -
      ∫ t in 0..(T : ℝ), valueL2 t.toNNReal (heat p) := rfl

theorem brownianCore_zero_degree (t : ℝ≥0) : (brownianCore t 0 : GaussianL2) = gaussianOne :=
  core_zero _ _

theorem brownianCore_zero_time (n : ℕ) : (brownianCore 0 (n + 1) : GaussianL2) = 0 := by
  have h := brownianCore_norm_sq 0 (n + 1)
  simp only [NNReal.coe_zero, zero_pow (Nat.succ_ne_zero n), mul_zero] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (brownianCore 0 (n + 1) : GaussianL2)])

theorem timeIntegral_basis_heat (k n : ℕ) (T : ℝ≥0) :
    timeIntegral T (heat (basisPolynomial (k, n))) =
      ∫ t in 0..(T : ℝ), ((k : ℝ) * t ^ (k - 1)) • (brownianCore t.toNNReal n : GaussianL2) := by
  change (∫ t in 0..(T : ℝ), valueL2 t.toNNReal _) = _
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  have ht0 : 0 ≤ t := (uIcc_of_le T.coe_nonneg ▸ ht).1
  rw [basis_heat, map_smul, valueL2_basis, smul_smul, Real.coe_toNNReal _ ht0]

theorem noiseTarget_basis_zero (k : ℕ) (T : ℝ≥0) : noiseTarget T (basisPolynomial (k, 0)) = 0 := by
  change valueL2 T _ - valueL2 0 _ - timeIntegral T (heat _) = 0
  rw [valueL2_basis, valueL2_basis, timeIntegral_basis_heat]
  simp only [brownianCore_zero_degree, NNReal.coe_zero, intervalIntegral.integral_smul_const]
  have hi : (∫ t in 0..(T : ℝ), (k : ℝ) * t ^ (k - 1)) = (T : ℝ) ^ k - 0 ^ k :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_pow k t)
      ((continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _)
  rw [hi, sub_smul]
  module

end OperatorDerivativeRewrite.Foundation.GaussianPolynomialProcess
