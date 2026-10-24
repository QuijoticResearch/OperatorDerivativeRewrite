import Foundation.IBMPhysicalCorrectionIntegral

/-! The actual probability-space L2 to L1 inclusion for physical kernels.
This changes integrability exponent, never the stochastic representative. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalL2ToL1
open InfiniteGaussian IBMPhysicalWeakWiener
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

def value (U : Lp Kernel 2 gaussianProduct) : Lp Kernel 1 gaussianProduct :=
  ((Lp.memLp U).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp U

theorem value_ae (U : Lp Kernel 2 gaussianProduct) : value U =ᵐ[gaussianProduct] U :=
  MemLp.coeFn_toLp _

theorem value_norm_le (U : Lp Kernel 2 gaussianProduct) : ‖value U‖ ≤ ‖U‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top U)
  calc
    eLpNorm (value U) 1 gaussianProduct = eLpNorm U 1 gaussianProduct :=
      eLpNorm_congr_ae (value_ae U)
    _ ≤ eLpNorm U 2 gaussianProduct :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)

private def valueLinear : Lp Kernel 2 gaussianProduct →ₗ[ℝ] Lp Kernel 1 gaussianProduct where
  toFun := value
  map_add' U V := by
    apply Lp.ext
    filter_upwards [value_ae (U+V), value_ae U, value_ae V,
      Lp.coeFn_add U V, Lp.coeFn_add (value U) (value V)] with Y ha hu hv hs ht
    simp only [ha, ht, hs, Pi.add_apply, hu, hv]
  map_smul' r U := by
    apply Lp.ext
    filter_upwards [value_ae (r • U), value_ae U,
      Lp.coeFn_smul r U, Lp.coeFn_smul r (value U)] with Y ha hu hs ht
    simp only [RingHom.id_apply, ha, ht, hs, Pi.smul_apply, hu]

def inclusion : Lp Kernel 2 gaussianProduct →L[ℝ] Lp Kernel 1 gaussianProduct :=
  valueLinear.mkContinuous 1 (fun U => by
    change ‖value U‖ ≤ 1*‖U‖
    simpa only [one_mul] using value_norm_le U)

theorem inclusion_ae (U : Lp Kernel 2 gaussianProduct) : inclusion U =ᵐ[gaussianProduct] U :=
  value_ae U

theorem inclusion_norm_le (U : Lp Kernel 2 gaussianProduct) : ‖inclusion U‖ ≤ ‖U‖ :=
  value_norm_le U

theorem inclusion_injective : Function.Injective inclusion := by
  intro U V h
  apply Lp.ext
  filter_upwards [inclusion_ae U, inclusion_ae V] with Y hu hv
  rw [← hu, ← hv, h]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalL2ToL1
