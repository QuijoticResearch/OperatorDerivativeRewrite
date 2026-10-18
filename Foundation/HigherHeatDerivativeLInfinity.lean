import Foundation.HigherHeatTimeDerivative
import Mathlib.MeasureTheory.Function.Holder

/-! Genuine L-infinity time-field lifts of the completed cutoff derivatives. -/
noncomputable section
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatDerivativeLInfinity
open HigherHeatAnalyticCylinderDomain HigherHeatTimeDerivative MeasureTheory Filter
variable (μ : Measure ℝ)

theorem field_memLp (r : ℕ) (u : Domain) : MemLp (fun t : ℝ => ((atTime t)^r) u) ∞ μ :=
  memLp_top_of_bound (stronglyMeasurable_pow r u).aestronglyMeasurable ‖u‖
    (Eventually.of_forall (fun t => atTime_pow_bound t r u))

def element (r : ℕ) (u : Domain) : Lp Domain ∞ μ :=
  (field_memLp μ r u).toLp (fun t : ℝ => ((atTime t)^r) u)

theorem element_ae (r : ℕ) (u : Domain) :
    element μ r u =ᵐ[μ] fun t : ℝ => ((atTime t)^r) u := MemLp.coeFn_toLp _

theorem element_norm (r : ℕ) (u : Domain) : ‖element μ r u‖ ≤ ‖u‖ := by
  rw [element, Lp.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal (norm_nonneg u)
  rw [eLpNorm_exponent_top (field_memLp μ r u).aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound
    (Eventually.of_forall (fun t => atTime_pow_bound t r u))

def linear (r : ℕ) : Domain →ₗ[ℝ] Lp Domain ∞ μ where
  toFun := element μ r
  map_add' u v := by
    apply Lp.ext
    filter_upwards [element_ae μ r (u+v), element_ae μ r u, element_ae μ r v,
      Lp.coeFn_add (element μ r u) (element μ r v)] with t hsum hu hv ha
    rw [hsum, ha]
    simp only [Pi.add_apply, hu, hv, map_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [element_ae μ r (c • u), element_ae μ r u,
      Lp.coeFn_smul c (element μ r u)] with t hs hu hc
    simp only [RingHom.id_apply]
    rw [hs, hc]
    simp only [Pi.smul_apply, hu, map_smul, RingHom.id_apply]

def lift (r : ℕ) : Domain →L[ℝ] Lp Domain ∞ μ :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Domain) (F := Lp Domain ∞ μ)
    (linear μ r) 1 (fun u => by
      change ‖element μ r u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using element_norm μ r u)

theorem lift_ae (r : ℕ) (u : Domain) :
    lift μ r u =ᵐ[μ] fun t : ℝ => ((atTime t)^r) u := element_ae μ r u

theorem lift_norm (r : ℕ) : ‖lift μ r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖element μ r u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using element_norm μ r u

end OperatorDerivativeRewrite.Foundation.HigherHeatDerivativeLInfinity
