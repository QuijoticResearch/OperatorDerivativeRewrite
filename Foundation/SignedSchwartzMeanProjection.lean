import Foundation.SignedSchwartzFundamentalSymmetry
import Foundation.HigherHeatKernelMoments
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The genuine signed mean projection has norm equal to total variation, not one. -/
noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzMeanProjection
open SignedSchwartzL2Rigging SignedSchwartzFundamentalSymmetry

def unitVector (K : 𝓢(ℝ, ℝ)) : H K :=
  (memLp_const (1: ℂ) : MemLp (fun _ : ℝ => (1: ℂ)) 2 (measure K)).toLp _

theorem unitVector_ae (K : 𝓢(ℝ, ℝ)) :
    unitVector K =ᵐ[measure K] (fun _ => (1: ℂ)) := MemLp.coeFn_toLp _

theorem weighted_integral (K : 𝓢(ℝ, ℝ)) (f : ℝ → ℝ) :
    (∫ x, f x ∂measure K) = ∫ x : ℝ, |K x| * f x := by
  have hm : Measurable (fun x : ℝ => |K x|) := by
    simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
  rw [SignedSchwartzL2Rigging.measure, SignedAbsoluteIntegration.absoluteDensity,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top (r := |K x|)))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change (ENNReal.ofReal |K x|).toReal * f x = |K x| * f x
    rw [ENNReal.toReal_ofReal (abs_nonneg _)])

theorem unitVector_norm_sq (K : 𝓢(ℝ, ℝ)) : ‖unitVector K‖^2 = ∫ x : ℝ, |K x| := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  have he : (fun x => inner ℝ ((unitVector K) x) ((unitVector K) x)) =ᵐ[measure K]
      (fun _ : ℝ => (1: ℝ)) := by
    filter_upwards [unitVector_ae K] with x hx
    rw [hx]
    simp
  rw [integral_congr_ae he, weighted_integral]
  simp only [mul_one]

theorem unitVector_mass (K : 𝓢(ℝ, ℝ)) :
    inner ℂ (symmetry K (unitVector K)) (unitVector K) = (((∫ x : ℝ, K x): ℝ): ℂ) := by
  have he : inner ℂ (symmetry K (unitVector K)) (unitVector K) =
      ∫ x, (sign K x: ℂ) ∂measure K := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [symmetry_ae K (unitVector K), unitVector_ae K] with x hx hu
    change inner ℂ ((symmetry K (unitVector K)) x) ((unitVector K) x) = _
    rw [hx, hu]
    simp [Complex.real_smul, RCLike.inner_apply, mul_comm]
  rw [he, integral_complex_ofReal, weighted_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => sign_density K x)

def projection (K : 𝓢(ℝ, ℝ)) : H K →L[ℂ] H K :=
  InnerProductSpace.rankOne ℂ (unitVector K) (symmetry K (unitVector K))

theorem projection_norm (K : 𝓢(ℝ, ℝ)) : ‖projection K‖ = ∫ x : ℝ, |K x| := by
  rw [projection, InnerProductSpace.norm_rankOne, symmetry_norm, ← pow_two, unitVector_norm_sq]

theorem projection_idempotent (K : 𝓢(ℝ, ℝ)) (hK : (∫ x : ℝ, K x) = 1) :
    (projection K).comp (projection K) = projection K := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, projection, InnerProductSpace.rankOne_apply,
    inner_smul_right, unitVector_mass, hK, Complex.ofReal_one, mul_one]

theorem projection_expands (K : 𝓢(ℝ, ℝ)) (hK : 1 < ∫ x : ℝ, |K x|) :
    ‖symmetry K (unitVector K)‖ < ‖projection K (symmetry K (unitVector K))‖ := by
  have hn : 1 < ‖unitVector K‖^2 := by rwa [unitVector_norm_sq]
  have hp : 0 < ‖unitVector K‖ := by nlinarith [norm_nonneg (unitVector K)]
  have he : ‖projection K (symmetry K (unitVector K))‖ = ‖unitVector K‖^2 * ‖unitVector K‖ := by
    rw [projection, InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, norm_smul,
      symmetry_norm]
    simp
  rw [he, symmetry_norm]
  simpa only [one_mul] using mul_lt_mul_of_pos_right hn hp

theorem higherHeat_norm_gt_one (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t) :
    1 < ‖projection (HigherHeatSignedLaws.realKernel m (by omega) t ht)‖ := by
  rw [projection_norm]
  simpa only [Real.norm_eq_abs] using HigherHeatKernelMoments.norm_integral_gt_one m hm t ht

theorem higherHeat_idempotent (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    (projection (HigherHeatSignedLaws.realKernel m hm t ht)).comp
      (projection (HigherHeatSignedLaws.realKernel m hm t ht)) =
      projection (HigherHeatSignedLaws.realKernel m hm t ht) :=
  projection_idempotent _ (HigherHeatSignedLaws.realKernel_integral m hm t ht)

theorem higherHeat_expands (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t) :
    let K := HigherHeatSignedLaws.realKernel m (by omega : 0 < m) t ht
    ‖symmetry K (unitVector K)‖ < ‖projection K (symmetry K (unitVector K))‖ := by
  apply projection_expands
  simpa only [Real.norm_eq_abs] using HigherHeatKernelMoments.norm_integral_gt_one m hm t ht


theorem projection_core (K : 𝓢(ℝ, ℝ)) (f : 𝓢(ℝ, ℂ)) :
    projection K (SignedSchwartzClosedDerivative.coreInput K f) =
      (∫ᵛ x : ℝ, f x ∂<•volume.withDensityᵥ (K: ℝ → ℝ)) • unitVector K := by
  have hc : inner ℂ (symmetry K (unitVector K))
      (SignedSchwartzClosedDerivative.coreInput K f) = ∫ x : ℝ, K x • f x := by
    have he : inner ℂ (symmetry K (unitVector K))
        (SignedSchwartzClosedDerivative.coreInput K f) =
        ∫ x, sign K x • f x ∂measure K := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [symmetry_ae K (unitVector K), unitVector_ae K,
        f.coeFn_toLp 2 (measure K)] with x hx hu hf
      change inner ℂ ((symmetry K (unitVector K)) x) ((f.toLp 2 (measure K)) x) = _
      rw [hx, hu, hf]
      simp [Complex.real_smul, RCLike.inner_apply, mul_comm]
    have hm : Measurable (fun x : ℝ => |K x|) := by
      simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
    rw [he, SignedSchwartzL2Rigging.measure, SignedAbsoluteIntegration.absoluteDensity,
      integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
        (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top (r := |K x|)))]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      change (ENNReal.ofReal |K x|).toReal • (sign K x • f x) = K x • f x
      rw [ENNReal.toReal_ofReal (abs_nonneg _), smul_smul, sign_density])
  rw [projection, InnerProductSpace.rankOne_apply, hc,
    SignedAbsoluteIntegration.integral_density volume K K.integrable K.continuous.measurable
      f (f.integrable (μ := measure K))]

end OperatorDerivativeRewrite.Foundation.SignedSchwartzMeanProjection
