import Foundation.IBMQuarticPrimitiveLimit
import Foundation.IBMClockCubicTimeProjection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! A specified spatial weak topology: actual second-source quartic kernels
tested against clamped C² functions converge strongly in Gaussian L². -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticSpatialWeakLimit
open InfiniteGaussian IBMQuarticSecondPrimitive IBMQuarticPrimitiveLimit
open IBMQuarticSecondGeometry IBMQuadraticSpatialCalculus IBMQuarticSecondChaos
open GaussianTimeSpaceHermite IBMGaussianSteinMoments IBMVarianceClockGeometry

theorem cross_curve_continuous (n : ℕ) (i j : Fin 3) :
    Continuous (fun r => cross (tripleCoefficient n r i) (tripleCoefficient n r j)) := by
  change Continuous (fun r => crossBilinear (tripleCoefficient n r i) (tripleCoefficient n r j))
  exact (crossBilinear.continuous.comp (IBMClockCubicTimeProjection.tripleCoefficient_continuous n i)).clm_apply
    (IBMClockCubicTimeProjection.tripleCoefficient_continuous n j)

theorem projected_continuous (n : ℕ) :
    Continuous (fun r => GaussianNumberSectors.projection 2 (spatialQuartic n r)) := by
  have hw (i : Fin 3) : Continuous (fun r => (wick (tripleCoefficient n r i) 2 : GaussianL2)) :=
    (GaussianWickContinuity.wick_continuous 2).comp
      (IBMClockCubicTimeProjection.tripleCoefficient_continuous n i)
  have hc := (variance_smooth n).continuous
  have hd := (RealSteklovApprox.deriv_contDiff_one _ (variance_smooth n)).continuous
  simp_rw [spatialQuartic_projection_two]
  exact (((IBMMollifier.kernel_smooth n).continuous.div_const 2).smul (hw 0)).add
    (hd.smul (cross_curve_continuous n 0 1)) |>.add
      ((hc.div_const 2).smul ((hw 1).add (cross_curve_continuous n 0 2)))

theorem slope_continuous (n : ℕ) : Continuous (slope n) :=
  continuous_iff_continuousAt.mpr fun r => (slope_hasDerivAt n r).continuousAt

theorem projected_test_eq (n : ℕ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (a b : ℝ)
    (ha : ψ a = 0) (hb : ψ b = 0) (hda : deriv ψ a = 0) (hdb : deriv ψ b = 0) :
    (∫ r in a..b, ψ r • GaussianNumberSectors.projection 2 (spatialQuartic n r)) =
      ∫ r in a..b, deriv (deriv ψ) r • primitive n r := by
  have hd := RealSteklovApprox.deriv_contDiff_one ψ hψ
  have hi₁ := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    hψ.continuous.continuousOn (slope_continuous n).continuousOn
    (fun r _ => (hψ.differentiable (by norm_num) r).hasDerivAt)
    (fun r _ => slope_hasDerivAt n r)
    (hd.continuous.intervalIntegrable a b) ((projected_continuous n).intervalIntegrable a b)
  have hi₂ := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    hd.continuous.continuousOn (primitive_continuous n).continuousOn
    (fun r _ => (hd.differentiable (by norm_num) r).hasDerivAt)
    (fun r _ => primitive_hasDerivAt n r)
    (hd.continuous_deriv_one.intervalIntegrable a b) ((slope_continuous n).intervalIntegrable a b)
  rw [hi₁, hi₂, ha, hb, hda, hdb]
  simp

/-- Actual projected kernels converge when tested in the spatial evaluation
coordinate, with strong Gaussian-L² convergence of each test integral. -/
theorem projected_test_tendsto (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (a b : ℝ) (hab : a ≤ b)
    (ha : ψ a = 0) (hb : ψ b = 0) (hda : deriv ψ a = 0) (hdb : deriv ψ b = 0) :
    Tendsto (fun n => ∫ r in a..b, ψ r • GaussianNumberSectors.projection 2 (spatialQuartic n r))
      atTop (𝓝 (∫ r in Set.Icc a b, deriv (deriv ψ) r • primitiveLimit r)) := by
  have he (n : ℕ) : (∫ r in a..b, ψ r • GaussianNumberSectors.projection 2 (spatialQuartic n r)) =
      ∫ r in Set.Icc a b, deriv (deriv ψ) r • primitive n r := by
    rw [projected_test_eq n ψ hψ a b ha hb hda hdb,
      intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  simpa only [he] using test_integral_tendsto (deriv (deriv ψ))
    (RealSteklovApprox.deriv_contDiff_one ψ hψ).continuous_deriv_one a b

end OperatorDerivativeRewrite.Foundation.IBMQuarticSpatialWeakLimit
