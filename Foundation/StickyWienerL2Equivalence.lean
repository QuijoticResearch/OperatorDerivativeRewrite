import Foundation.StickyWienerPathEquivalence
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! The actual Wiener/sticky whole-path law equivalence gives a genuine
linear isometry equivalence of their real L2 spaces. This supplies operator
transport, without identifying transported operators with physical generators. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyWienerL2Equivalence
open StickyWienerPathEquivalence StickyWienerPathRealization
set_option backward.isDefEq.respectTransparency false

abbrev WienerL2 := Lp ℝ 2 wienerLaw
abbrev StickyL2 (κ : ℝ≥0) := Lp ℝ 2 (stickyLaw κ)

def toWiener (κ : ℝ≥0) : StickyL2 κ →ₗᵢ[ℝ] WienerL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (stickyPath κ) (sticky_preserving κ)

def fromWiener (κ : ℝ≥0) : WienerL2 →ₗᵢ[ℝ] StickyL2 κ :=
  Lp.compMeasurePreservingₗᵢ ℝ (recovery κ) (recovery_preserving κ)

theorem to_from (κ : ℝ≥0) (f : WienerL2) :
    toWiener κ (fromWiener κ f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (fromWiener κ f) (sticky_preserving κ),
    (sticky_preserving κ).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving f (recovery_preserving κ)),
    left_inverse_ae κ] with p h1 h2 h3
  change toWiener κ (fromWiener κ f) p = fromWiener κ f (stickyPath κ p) at h1
  change fromWiener κ f (stickyPath κ p) = f (recovery κ (stickyPath κ p)) at h2
  rw [h1,h2,h3]

theorem from_to (κ : ℝ≥0) (f : StickyL2 κ) :
    fromWiener κ (toWiener κ f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (toWiener κ f) (recovery_preserving κ),
    (recovery_preserving κ).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving f (sticky_preserving κ)),
    right_inverse_ae κ] with p h1 h2 h3
  change fromWiener κ (toWiener κ f) p = toWiener κ f (recovery κ p) at h1
  change toWiener κ f (recovery κ p) = f (stickyPath κ (recovery κ p)) at h2
  rw [h1,h2,h3]

def equivalence (κ : ℝ≥0) : StickyL2 κ ≃ₗᵢ[ℝ] WienerL2 :=
  LinearIsometryEquiv.ofSurjective (toWiener κ) (fun f => ⟨fromWiener κ f,to_from κ f⟩)

theorem equivalence_apply (κ : ℝ≥0) (f : StickyL2 κ) :
    equivalence κ f = toWiener κ f := rfl

theorem equivalence_symm_apply (κ : ℝ≥0) (f : WienerL2) :
    (equivalence κ).symm f = fromWiener κ f := by
  apply (equivalence κ).injective
  rw [LinearIsometryEquiv.apply_symm_apply,equivalence_apply,to_from]

end OperatorDerivativeRewrite.Foundation.StickyWienerL2Equivalence
