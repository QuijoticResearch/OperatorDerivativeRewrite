import Foundation.PoissonLpLowerObstruction
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Explicit finite annuli in the symmetric gamma=3/2 power-law mark measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Interval ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.StableLevyAnnuli
set_option backward.isDefEq.respectTransparency false
open PoissonLpLowerObstruction PoissonDifferenceCore

def density (c z : ℝ) : ℝ := c*|z|^(-5/2 : ℝ)
def markMeasure (c : ℝ) : Measure ℝ := volume.withDensity (fun z => ENNReal.ofReal (density c z))
def base (c : ℝ) (n : ℕ) : ℝ := 1+3*(n : ℝ)^4/(2*c)
def endpoint (c : ℝ) (n : ℕ) : ℝ := base c n^(-2/3 : ℝ)
def annulus (c : ℝ) (n : ℕ) : Set ℝ := Ioc (endpoint c n) 1

theorem base_ge_one (c : ℝ) (hc : 0 < c) (n : ℕ) : 1 ≤ base c n := by
  unfold base
  have h : 0 ≤ 3*(n : ℝ)^4/(2*c) := by positivity
  linarith

theorem endpoint_pos (c : ℝ) (hc : 0 < c) (n : ℕ) : 0 < endpoint c n :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (base_ge_one c hc n)) _

theorem endpoint_le_one (c : ℝ) (hc : 0 < c) (n : ℕ) : endpoint c n ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (base_ge_one c hc n) (by norm_num)

theorem endpoint_power (c : ℝ) (hc : 0 < c) (n : ℕ) :
    endpoint c n^(-3/2 : ℝ)=base c n := by
  unfold endpoint
  rw [← Real.rpow_mul (show 0 ≤ base c n by linarith [base_ge_one c hc n])]
  norm_num

theorem positive_power_integrable (c a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    IntervalIntegrable (fun z : ℝ => c*z^(-5/2 : ℝ)) volume a 1 := by
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_const.mul (continuousOn_id.rpow_const ?_)
  intro z hz
  rw [uIcc_of_le ha1] at hz
  exact Or.inl (ne_of_gt (ha.trans_le hz.1))

theorem positive_power_integral (c a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ z in a..1, c*z^(-5/2 : ℝ))=(2*c/3)*(a^(-3/2 : ℝ)-1) := by
  have hd (z : ℝ) (hz : z ∈ uIcc a 1) :
      HasDerivAt (fun z : ℝ => -(2*c/3)*z^(-3/2 : ℝ)) (c*z^(-5/2 : ℝ)) z := by
    have hzpos : 0 < z := by rw [uIcc_of_le ha1] at hz; exact ha.trans_le hz.1
    have hh := (Real.hasDerivAt_rpow_const (p := (-3/2 : ℝ)) (Or.inl (ne_of_gt hzpos))).const_mul (-(2*c/3))
    norm_num only [show (-3/2 : ℝ)-1= -5/2 by norm_num] at hh
    convert hh using 1 <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (positive_power_integrable c a ha ha1)
  rw [Real.one_rpow] at he
  calc
    _ = -(2*c/3)*1 - -(2*c/3)*a^(-3/2 : ℝ) := he
    _ = _ := by ring

theorem markMeasure_Ioc (c : ℝ) (hc : 0 ≤ c) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    markMeasure c (Ioc a 1)=ENNReal.ofReal ((2*c/3)*(a^(-3/2 : ℝ)-1)) := by
  have hi : Integrable (fun z : ℝ => c*z^(-5/2 : ℝ)) (volume.restrict (Ioc a 1)) :=
    (positive_power_integrable c a ha ha1).1
  have he : density c =ᵐ[volume.restrict (Ioc a 1)] fun z : ℝ => c*z^(-5/2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    unfold density
    rw [abs_of_pos (ha.trans hz.1)]
  have hn : 0 ≤ᵐ[volume.restrict (Ioc a 1)] (fun z : ℝ => c*z^(-5/2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact mul_nonneg hc (Real.rpow_nonneg (ha.trans hz.1).le _)
  unfold markMeasure
  rw [withDensity_apply _ measurableSet_Ioc]
  calc
    _ = ∫⁻ z in Ioc a 1, ENNReal.ofReal (c*z^(-5/2 : ℝ)) :=
      lintegral_congr_ae (he.mono (fun z hz => congrArg ENNReal.ofReal hz))
    _ = ENNReal.ofReal (∫ z in Ioc a 1, c*z^(-5/2 : ℝ)) :=
      (ofReal_integral_eq_lintegral_ofReal hi hn).symm
    _ = _ := by rw [← intervalIntegral.integral_of_le ha1,positive_power_integral c a ha ha1]

theorem annulus_mass (c : ℝ) (hc : 0 < c) (n : ℕ) :
    markMeasure c (annulus c n)=(rate n : ℝ≥0∞) := by
  rw [annulus,markMeasure_Ioc c hc.le _ (endpoint_pos c hc n) (endpoint_le_one c hc n),
    endpoint_power c hc n]
  have he : (2*c/3)*(base c n-1)=(n : ℝ)^4 := by
    unfold base
    field_simp
    ring
  rw [he]
  norm_cast <;> simp [rate]

theorem annulus_measurable (c : ℝ) (n : ℕ) : MeasurableSet (annulus c n) := measurableSet_Ioc

theorem annulus_away_zero (c : ℝ) (hc : 0 < c) (n : ℕ) {z : ℝ} (hz : z ∈ annulus c n) : 0 < z :=
  (endpoint_pos c hc n).trans hz.1

abbrev unitTime : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
def controlMeasure (c : ℝ) : Measure (ℝ × ℝ) := unitTime.prod (markMeasure c)
def block (c : ℝ) (n : ℕ) : Set (ℝ × ℝ) := Ioc (0 : ℝ) 1 ×ˢ annulus c n

local instance (c : ℝ) : SFinite (markMeasure c) := by unfold markMeasure; infer_instance

theorem block_measurable (c : ℝ) (n : ℕ) : MeasurableSet (block c n) :=
  measurableSet_Ioc.prod (annulus_measurable c n)

theorem block_mass (c : ℝ) (hc : 0 < c) (n : ℕ) :
    controlMeasure c (block c n)=(rate n : ℝ≥0∞) := by
  rw [controlMeasure,block,Measure.prod_prod,annulus_mass c hc n]
  have ht : unitTime (Ioc (0 : ℝ) 1)=1 := by simp [unitTime]
  rw [ht,one_mul]

theorem block_memLp (c : ℝ) (hc : 0 < c) (n : ℕ) :
    MemLp ((block c n).indicator (fun _ => (1 : ℝ))) exponent (controlMeasure c) :=
  indicator_memLp (controlMeasure c) (block c n) (block_measurable c n) (rate n) (block_mass c hc n)

theorem block_norm (c : ℝ) (hc : 0 < c) (n : ℕ) :
    (eLpNorm ((block c n).indicator (fun _ => (1 : ℝ))) exponent (controlMeasure c)).toReal=(n : ℝ)^3 := by
  rw [indicator_norm (controlMeasure c) (block c n) (block_measurable c n) (rate n) (block_mass c hc n),input_norm_rate]

theorem no_stable_indicator_lower {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (c : ℝ) (hc : 0 < c) (X : ℕ → Ω → ℕ)
    (hX : ∀ n, HasLaw (X n) (poissonLaw (rate n)) μ) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ hn : 0 < n,
      C*(eLpNorm ((block c n).indicator (fun _ => (1 : ℝ))) exponent (controlMeasure c)).toReal ≤
        ‖lawOutput (X n) (rate n) (rate_pos hn) (hX n)‖ :=
  no_indicator_lower (controlMeasure c) (block c) (block_measurable c) (block_mass c hc) X hX

section CountInterface
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Only the finite-set marginal-law property is needed; this is not a construction of a PRM. -/
structure FiniteCountLaws (c : ℝ) where
  count : Set (ℝ × ℝ) → Ω → ℕ
  law : ∀ B, MeasurableSet B → controlMeasure c B ≠ ∞ →
    HasLaw (count B) (poissonLaw ((controlMeasure c B).toNNReal)) μ

variable {μ}

theorem block_count_law (c : ℝ) (hc : 0 < c) (N : FiniteCountLaws μ c) (n : ℕ) :
    HasLaw (N.count (block c n)) (poissonLaw (rate n)) μ := by
  have hf : controlMeasure c (block c n) ≠ ∞ := by
    rw [block_mass c hc n]
    exact ENNReal.coe_ne_top
  have h := N.law (block c n) (block_measurable c n) hf
  simpa only [block_mass c hc n,ENNReal.toNNReal_coe] using h

theorem no_plain_lower_from_finite_count_laws [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (N : FiniteCountLaws μ c) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ hn : 0 < n,
      C*(eLpNorm ((block c n).indicator (fun _ => (1 : ℝ))) exponent (controlMeasure c)).toReal ≤
        ‖lawOutput (N.count (block c n)) (rate n) (rate_pos hn) (block_count_law c hc N n)‖ :=
  no_stable_indicator_lower c hc (fun n => N.count (block c n)) (block_count_law c hc N)

end CountInterface
end OperatorDerivativeRewrite.Foundation.StableLevyAnnuli
