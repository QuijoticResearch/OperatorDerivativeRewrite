import Foundation.GaussianClockSpectralAdjoint
import Foundation.IBMClockFractionalDomain

/-! Self-adjoint fractional clock calculus, exact domain shifts/composition,
positive forms and the sharp actual reflected-clock IBM smoothing threshold.
These are ambient source-clock identities, not physical adapted Ito formulas. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockFractionalCalculus
open InfiniteGaussian GaussianClockValueOperators GaussianClockSpectralPowers
open GaussianClockSpectralAdjoint IBMClockFractionalDomain

theorem bessel_adjoint (s : ℝ) : (bessel s).adjoint = bessel s := operator_adjoint _

theorem bessel_nonneg (s : ℝ) (f : (bessel s).domain) :
    0 ≤ inner ℝ (bessel s f) (f:Field) :=
  operator_nonneg _ (fun n => Real.rpow_nonneg (by positivity) _) f

theorem bessel_projection (s : ℝ) (f : (bessel s).domain) (n : ℕ) :
    project n (bessel s f) = ((n:ℝ)+1)^(s/2) • project n f := operator_projection _ _ _

theorem bessel_shift_domain (r s : ℝ) (f : (bessel r).domain) :
    bessel r f ∈ (bessel s).domain ↔ (f:Field) ∈ (bessel (r+s)).domain := by
  rw [bessel_domain,bessel_domain]
  have he (n : ℕ) : ((n:ℝ)+1)^s*‖project n (bessel r f)‖^2 =
      ((n:ℝ)+1)^(r+s)*‖project n f‖^2 := by
    rw [bessel_projection,norm_smul,mul_pow,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)+1) _),bessel_weight_sq]
    rw [← mul_assoc,← Real.rpow_add (by positivity : (0:ℝ) < (n:ℝ)+1)]
    congr 2; ring
  simp only [he]

theorem bessel_composition (r s : ℝ) (f : (bessel r).domain)
    (h : bessel r f ∈ (bessel s).domain) :
    bessel s ⟨bessel r f,h⟩ = bessel (r+s) ⟨(f:Field),(bessel_shift_domain r s f).1 h⟩ := by
  apply eq_of_clock_projections
  intro n
  change project n (bessel s _) = project n (bessel (r+s) _)
  simp only [bessel_projection]
  rw [smul_smul,← Real.rpow_add (by positivity : (0:ℝ) < (n:ℝ)+1)]
  congr 2; ring

theorem actual_regularized_domain (r s : ℝ) (T : ℝ≥0) (hT : 0 < T) (hr : r < 1/2) :
    bessel r ⟨IBMRandomTimeHilbert.randomSourceL2 T,(actual_bessel_domain r T hT).2 hr⟩
      ∈ (bessel s).domain ↔ r+s < 1/2 := by
  rw [bessel_shift_domain]
  exact actual_bessel_domain (r+s) T hT

theorem actual_endpoint_ibp (s : ℝ) (hs : s < 1/2) (T U : ℝ≥0) (hT : 0 < T) (hU : 0 < U) :
    inner ℝ (bessel s ⟨IBMRandomTimeHilbert.randomSourceL2 T,(actual_bessel_domain s T hT).2 hs⟩)
      (IBMRandomTimeHilbert.randomSourceL2 U) =
    inner ℝ (IBMRandomTimeHilbert.randomSourceL2 T)
      (bessel s ⟨IBMRandomTimeHilbert.randomSourceL2 U,(actual_bessel_domain s U hU).2 hs⟩) :=
  operator_ibp _ ⟨_,(actual_bessel_domain s T hT).2 hs⟩ ⟨_,(actual_bessel_domain s U hU).2 hs⟩



theorem actual_smoothing_threshold (β : ℝ) (hβ : 0 ≤ β) (T : ℝ≥0) (hT : 0 < T) :
    bessel (-2*β) ⟨IBMRandomTimeHilbert.randomSourceL2 T,
      (actual_bessel_domain (-2*β) T hT).2 (by linarith)⟩ ∈ (bessel 1).domain ↔ 1/4 < β := by
  have ht := actual_regularized_domain (-2*β) 1 T hT (by linarith : -2*β < 1/2)
  exact ht.trans (by constructor <;> intro h <;> linarith)

theorem bessel_half_domain (s : ℝ) (f : (bessel s).domain) :
    (f:Field) ∈ (bessel (s/2)).domain := by
  rw [bessel_domain]
  have hs := operator_pairing_hasSum (fun n => ((n:ℝ)+1)^(s/2)) f (f:Field)
  simpa only [real_inner_self_eq_norm_sq] using hs.summable

theorem bessel_form_identity (s : ℝ) (f : (bessel s).domain) :
    inner ℝ (bessel s f) (f:Field) =
      ‖bessel (s/2) ⟨(f:Field),bessel_half_domain s f⟩‖^2 := by
  have hs := operator_pairing_hasSum (fun n => ((n:ℝ)+1)^(s/2)) f (f:Field)
  have ht := operator_energy (fun n => ((n:ℝ)+1)^((s/2)/2))
    (⟨(f:Field),bessel_half_domain s f⟩ : (bessel (s/2)).domain)
  simp only [real_inner_self_eq_norm_sq,bessel_weight_sq] at hs ht
  exact hs.unique ht

end OperatorDerivativeRewrite.Foundation.IBMClockFractionalCalculus
