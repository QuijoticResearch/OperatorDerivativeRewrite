import Foundation.FourierPathTimeFieldSeries
import Foundation.FourierPathControlFrechet
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A genuine, uniquely representing Bochner time-gradient density on completed path tests. -/
noncomputable section
open MeasureTheory
open scoped lp NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathTimeGradient
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatFourierBanach
open FourierPathBoundedControls BochnerTimeControlPairing FourierPathControlGradient

theorem pairing_compLp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (u : Control) (f : BochnerTimeControlPairing.Field E) :
    pairing F u (L.compLpL 1 volume f) = L (pairing E u f) := by
  rw [pairing_integral, pairing_integral]
  have hi : Integrable (fun s => u s • f s) :=
    memLp_one_iff_integrable.mp ((Lp.memLp u).smul (Lp.memLp f))
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [L.coeFn_compLpL f] with s hs
  rw [hs, map_smul]

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem quotient_norm : ‖((kernel levels ξ).mkQL : Coeff →L[ℂ] TestSpace levels ξ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simp only [one_mul]
  exact Submodule.Quotient.norm_mk_le (kernel levels ξ) a

def coefficientField (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Coeff →L[ℂ] BochnerTimeControlPairing.Field (TestSpace levels ξ) :=
  ((kernel levels ξ).mkQL.compLpL 1 volume).comp (FourierPathTimeFieldSeries.series levels ξ m hm T hT)

theorem coefficientField_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖coefficientField levels ξ m hm T hT‖ ≤ 1+(T:ℝ)⁻¹ := by
  calc
    _ ≤ ‖(kernel levels ξ).mkQL.compLpL 1 volume‖ *
        ‖FourierPathTimeFieldSeries.series levels ξ m hm T hT‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*(1+(T:ℝ)⁻¹) := mul_le_mul
      ((ContinuousLinearMap.norm_compLpL_le _).trans (quotient_norm levels ξ))
      (FourierPathTimeFieldSeries.series_bound levels ξ m hm T hT) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem coefficientField_pairing (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (a : Coeff) (u : Control) :
    pairing (TestSpace levels ξ) u (coefficientField levels ξ m hm T hT a) =
      (kernel levels ξ).mkQ (FourierPathControlGradientSeries.family levels ξ m hm T hT a u) := by
  have hh := pairing_compLp ((kernel levels ξ).mkQL.restrictScalars ℝ) u
    (FourierPathTimeFieldSeries.series levels ξ m hm T hT a)
  change pairing (TestSpace levels ξ) u (coefficientField levels ξ m hm T hT a) =
    (kernel levels ξ).mkQ (pairing Coeff u (FourierPathTimeFieldSeries.series levels ξ m hm T hT a)) at hh
  rwa [FourierPathTimeFieldSeries.series_pairing] at hh

theorem kernel_le_field (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    kernel levels ξ ≤ (coefficientField levels ξ m hm T hT).ker := by
  intro a ha
  apply annihilator_zero (TestSpace levels ξ)
  intro u
  change pairing (TestSpace levels ξ) u (coefficientField levels ξ m hm T hT a) = 0
  rw [coefficientField_pairing levels ξ m hm T hT a u]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (FourierPathControlGradientSeries.family_preserves_kernel levels ξ m hm T hT a ha u)

def timeGradient (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    TestSpace levels ξ →L[ℂ] BochnerTimeControlPairing.Field (TestSpace levels ξ) :=
  (kernel levels ξ).liftQL (coefficientField levels ξ m hm T hT) (kernel_le_field levels ξ m hm T hT)

theorem timeGradient_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    ‖timeGradient levels ξ m hm T hT q‖ ≤ (1+(T:ℝ)⁻¹)*‖q‖ := by
  let C := 1+(T:ℝ)⁻¹
  have hC : 0 < C := by dsimp [C]; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,hna⟩ := Submodule.Quotient.norm_mk_lt q (div_pos hε hC)
  have he : timeGradient levels ξ m hm T hT q = coefficientField levels ξ m hm T hT a := by
    rw [← ha]; rfl
  rw [he]
  calc
    _ ≤ C*‖a‖ := (coefficientField levels ξ m hm T hT).le_of_opNorm_le
      (coefficientField_bound levels ξ m hm T hT) a
    _ ≤ C*‖q‖+ε := by
      have hh := mul_lt_mul_of_pos_left hna hC
      have hc : C*(ε/C)=ε := by field_simp
      nlinarith

theorem timeGradient_pairing (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control) :
    pairing (TestSpace levels ξ) u (timeGradient levels ξ m hm T hT q) =
      gradient levels ξ m hm T hT q u := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [gradient_mk]
  exact coefficientField_pairing levels ξ m hm T hT a u

theorem timeGradient_integral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control) :
    (∫ s, u s • timeGradient levels ξ m hm T hT q s) = gradient levels ξ m hm T hT q u := by
  rw [← pairing_integral]
  exact timeGradient_pairing levels ξ m hm T hT q u

theorem timeGradient_unique (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (f : BochnerTimeControlPairing.Field (TestSpace levels ξ))
    (hf : ∀ u : Control, pairing (TestSpace levels ξ) u f = gradient levels ξ m hm T hT q u) :
    f = timeGradient levels ξ m hm T hT q := by
  apply pairing_injective (TestSpace levels ξ)
  ext u
  exact (hf u).trans (timeGradient_pairing levels ξ m hm T hT q u).symm

end OperatorDerivativeRewrite.Foundation.FourierPathTimeGradient
