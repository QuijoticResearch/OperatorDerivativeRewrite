import Foundation.IBMSpatialFourthSums

/-! An AUXILIARY Hilbert model for reusing verified integration/separation.
This is NOT the physical zero-order Sobolev embedding or a white-noise map. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialHilbertRetract
open InfiniteGaussian GaussianTimeHilbert IBMPhysicalWeakWiener
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

def model : TimeHilbert →ₗᵢ[ℝ] Kernel where
  toLinearMap :=
    ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).toLinearMap.comp
      (BochnerLinearIsometry.lift (volume : Measure ℝ) Complex.ofRealLI).toLinearMap
  norm_map' u := by
    change ‖(BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).symm
      (BochnerLinearIsometry.lift (volume : Measure ℝ) Complex.ofRealLI u)‖ = ‖u‖
    rw [LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]

def recover : Kernel →L[ℝ] TimeHilbert :=
  (ComplexL2Isometry.realPart (volume : Measure ℝ)).comp
    ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

theorem recover_model (u : TimeHilbert) : recover (model u) = u := by
  change ComplexL2Isometry.realPart (volume : Measure ℝ)
    ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2)
      ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).symm
        (BochnerLinearIsometry.lift (volume : Measure ℝ) Complex.ofRealLI u))) = u
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLpL
      (BochnerLinearIsometry.lift (volume : Measure ℝ) Complex.ofRealLI u),
    BochnerLinearIsometry.lift_coeFn (volume : Measure ℝ) Complex.ofRealLI u] with x hr hc
  change ComplexL2Isometry.realPart (volume : Measure ℝ) _ x = _ at hr
  rw [hr, hc]
  rfl

def lift : Lp TimeHilbert 2 gaussianProduct →ₗᵢ[ℝ] Lp Kernel 2 gaussianProduct :=
  BochnerLinearIsometry.lift gaussianProduct model

theorem lift_ae (U : Lp TimeHilbert 2 gaussianProduct) :
    lift U =ᵐ[gaussianProduct] fun Y => model (U Y) :=
  BochnerLinearIsometry.lift_coeFn gaussianProduct model U

theorem recover_lift (U : Lp TimeHilbert 2 gaussianProduct) :
    recover.compLpL 2 gaussianProduct (lift U) = U := by
  apply Lp.ext
  filter_upwards [recover.coeFn_compLpL (lift U), lift_ae U] with Y hr hu
  rw [hr, hu, recover_model]

end OperatorDerivativeRewrite.Foundation.IBMSpatialHilbertRetract
