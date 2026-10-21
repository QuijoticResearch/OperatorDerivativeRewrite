import Foundation.EvenEntireCanonicalApproximation
import Foundation.RiemannQuarticCanonicalLimit
import Mathlib.Analysis.Analytic.Uniqueness

/-! The actual finite reciprocal canonical product is analytic on the
closed disk, including its original zero locations. Reconstruction is
proved there as an identity of functions, rather than only off a discrete set. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalReconstruction
open RiemannQuarticFlow RiemannQuarticReality RiemannQuarticZeroCounting

def inverseZeroProduct (t R : ℝ) : ℂ → ℂ :=
  ∏ᶠ a : ℂ, (canonicalFactor R a) ^ (-divisor (flow t) (ball 0 R) a)

theorem canonical_reciprocal_eq (R : ℝ) (a z : ℂ) :
    (canonicalFactor R a z)⁻¹ = (R : ℂ)*(z-a)/((R : ℂ)^2-conj a*z) := by
  exact EvenEntireCanonicalApproximation.canonical_reciprocal_eq
    R a z

theorem canonical_numerator_ne_zero (R : ℝ) (a z : ℂ)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ closedBall (0 : ℂ) R) :
    (R : ℂ)^2-conj a*z ≠ 0 := by
  exact EvenEntireCanonicalApproximation.canonical_numerator_ne_zero
    R a z ha hz

theorem canonical_reciprocal_analytic (R : ℝ) (a : ℂ) (ha : a ∈ ball (0 : ℂ) R) :
    AnalyticOnNhd ℂ (fun z => (canonicalFactor R a z)⁻¹) (closedBall 0 R) := by
  exact EvenEntireCanonicalApproximation.canonical_reciprocal_analytic
    R a ha

theorem inverseZeroProduct_apply (t R : ℝ) (z : ℂ) :
    inverseZeroProduct t R z =
      ∏ᶠ a : ℂ, canonicalFactor R a z ^ (-divisor (flow t) (ball 0 R) a) := by
  exact EvenEntireCanonicalApproximation.inverseZeroProduct_apply
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t) R z

theorem inverseZeroProduct_analytic (t R : ℝ) :
    AnalyticOnNhd ℂ (inverseZeroProduct t R) (closedBall 0 R) := by
  exact EvenEntireCanonicalApproximation.inverseZeroProduct_analytic
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t) R

theorem actual_reconstruction (t R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) :
    ∀ z ∈ closedBall (0 : ℂ) R, flow t z = inverseZeroProduct t R z * h z := by
  exact EvenEntireCanonicalApproximation.reconstruction
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t) R hR h D hboundary

theorem inverseZeroProduct_origin_ne_zero (t R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) : inverseZeroProduct t R 0 ≠ 0 := by
  exact EvenEntireCanonicalApproximation.inverseZeroProduct_origin_ne_zero
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t)
    (by simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0) R hR h D hboundary

theorem normalized_reconstruction (t R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) :
    ∀ z ∈ closedBall (0 : ℂ) R, flow t z / flow t 0 =
      (inverseZeroProduct t R z / inverseZeroProduct t R 0) * (h z/h 0) := by
  exact EvenEntireCanonicalApproximation.normalized_reconstruction
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t) R hR h D hboundary

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalReconstruction
