import Foundation.HigherHeatDerivativeLInfinity
import Foundation.HigherHeatPairedDualCausality
import Mathlib.Analysis.Normed.Module.DoubleDual

/-! A genuine bounded weak time adjoint from actual L1 dual fields to the analytic dual.
Agreement with signed stochastic step sums is a separate obligation. -/
noncomputable section
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatWeakTimeAdjoint
open HigherHeatAnalyticCylinderDomain HigherHeatTimeDerivative HigherHeatDerivativeLInfinity
open HigherHeatPairedDualCausality MeasureTheory Filter

abbrev Field (μ : Measure ℝ) := Lp Dual 1 μ

/-- The canonical Mathlib operator norm, with all inference parameters explicit. -/
@[instance_reducible] def evaluationNorm : Norm (Dual →L[ℝ] Domain →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Dual)
    (F := Domain →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

attribute [local instance] evaluationNorm

def evaluation : Dual →L[ℝ] Domain →L[ℝ] ℝ :=
  (NormedSpace.inclusionInDoubleDual ℝ Domain).flip

theorem evaluation_norm : ‖evaluation‖ ≤ 1 := by
  rw [evaluation, ContinuousLinearMap.opNorm_flip (NormedSpace.inclusionInDoubleDual ℝ Domain)]
  exact NormedSpace.inclusionInDoubleDual_norm_le ℝ Domain

def transpose (μ : Measure ℝ) (r : ℕ) : Field μ →L[ℝ] Dual :=
  ((lift μ r).precomp ℝ).comp (evaluation.lpPairing (𝕜 := ℝ) (E := Dual) (F := Domain) (G := ℝ) μ 1 ∞)

theorem transpose_apply (μ : Measure ℝ) (r : ℕ) (A : Field μ) (G : Domain) :
    transpose μ r A G = ∫ t : ℝ, A t (((atTime t)^r) G) ∂μ := by
  change evaluation.lpPairing (𝕜 := ℝ) (E := Dual) (F := Domain) (G := ℝ) μ 1 ∞ A (lift μ r G) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral (𝕜 := ℝ) (E := Dual) (F := Domain) (G := ℝ)]
  apply integral_congr_ae
  filter_upwards [lift_ae μ r G] with t ht
  change A t ((lift μ r G) t) = _
  rw [ht]

theorem evaluation_integrable (μ : Measure ℝ) (r : ℕ) (A : Field μ) (G : Domain) :
    Integrable (fun t : ℝ => A t (((atTime t)^r) G)) μ := by
  have hi := memLp_one_iff_integrable.mp
    (evaluation.memLp_of_bilin (𝕜 := ℝ) (E := Dual) (F := Domain) (G := ℝ) 1 (Lp.memLp A) (Lp.memLp (lift μ r G)))
  apply hi.congr
  filter_upwards [lift_ae μ r G] with t ht
  change A t ((lift μ r G) t) = _
  rw [ht]

theorem transpose_bound (μ : Measure ℝ) (r : ℕ) (A : Field μ) :
    ‖transpose μ r A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro G
  rw [transpose_apply]
  letI : ContinuousENorm Dual := SeminormedAddGroup.toContinuousENorm (E := Dual)
  have hA : Integrable A μ := memLp_one_iff_integrable.mp (Lp.memLp A)
  have hANorm : Integrable (fun t : ℝ => ‖A t‖) μ :=
    Integrable.norm (α := ℝ) (β := Dual) (μ := μ) (f := fun t : ℝ => A t) hA
  have hB : Integrable (fun t : ℝ => ‖A t‖ * ‖G‖) μ := hANorm.mul_const ‖G‖
  have he (t : ℝ) : ‖A t (((atTime t)^r) G)‖ ≤ ‖A t‖ * ‖G‖ :=
    ((A t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (atTime_pow_bound t r G) (ContinuousLinearMap.opNorm_nonneg _))
  calc
    _ ≤ ∫ t : ℝ, ‖A t‖ * ‖G‖ ∂μ :=
      norm_integral_le_of_norm_le hB (Eventually.of_forall he)
    _ = (∫ t : ℝ, ‖A t‖ ∂μ) * ‖G‖ := integral_mul_const ‖G‖ _
    _ = ‖A‖ * ‖G‖ := by rw [← L1.norm_eq_integral_norm A]

def timeMeasure : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

def coefficient (m : ℕ) (T : ℝ≥0) : ℝ := ((2*m:ℕ):ℝ)*(-1:ℝ)^(m+1)*(T:ℝ)

def firstChannel (m : ℕ) (T : ℝ≥0) : Field timeMeasure →L[ℝ] Dual :=
  coefficient m T • transpose timeMeasure (2*m-1)

theorem firstChannel_apply (m : ℕ) (T : ℝ≥0) (A : Field timeMeasure) (G : Domain) :
    firstChannel m T A G = coefficient m T *
      ∫ t : ℝ, A t (((atTime t)^(2*m-1)) G) ∂timeMeasure := by
  rw [firstChannel, smul_apply, smul_apply, transpose_apply]
  rfl

theorem firstChannel_bound (m : ℕ) (T : ℝ≥0) (A : Field timeMeasure) :
    ‖firstChannel m T A‖ ≤ ((2*m:ℕ):ℝ)*(T:ℝ)*‖A‖ := by
  change ‖coefficient m T • transpose timeMeasure (2*m-1) A‖ ≤ _
  have hc : |coefficient m T| = ((2*m:ℕ):ℝ)*(T:ℝ) := by
    simp [coefficient, abs_mul, abs_pow, abs_of_nonneg T.coe_nonneg]
  calc
    _ ≤ ‖coefficient m T‖ * ‖transpose timeMeasure (2*m-1) A‖ :=
      ContinuousLinearMap.opNorm_smul_le (𝕜 := ℝ) (𝕜₂ := ℝ) (coefficient m T) _
    _ = (((2*m:ℕ):ℝ)*(T:ℝ)) * ‖transpose timeMeasure (2*m-1) A‖ := by
      rw [Real.norm_eq_abs, hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (transpose_bound timeMeasure (2*m-1) A) (by positivity)

end OperatorDerivativeRewrite.Foundation.HigherHeatWeakTimeAdjoint
