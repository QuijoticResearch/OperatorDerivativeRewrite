import Foundation.SU2WilsonConvolution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.YMResetGroundState
open BoundedExponentialTiltResponse
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (X : Ω → ℝ)

def amplitude (t : ℝ) (x : Ω) : ℝ := Real.exp ((t/2)*X x)
def transfer (t : ℝ) (f : Ω → ℝ) (x : Ω) : ℝ :=
  amplitude X t x * ∫ y, amplitude X t y * f y ∂μ

theorem amplitude_square (t : ℝ) (x : Ω) : amplitude X t x ^ 2 = Real.exp (t*X x) := by
  rw [amplitude,← Real.exp_nat_mul]
  congr 1
  ring

theorem amplitude_memLp (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1) (t : ℝ) :
    MemLp (amplitude X t) 2 μ := by
  apply MemLp.of_bound ((measurable_const.mul hX).exp.aestronglyMeasurable) (Real.exp |t/2|)
  filter_upwards with x
  change ‖Real.exp ((t/2)*X x)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    (t/2)*X x ≤ |(t/2)*X x| := le_abs_self _
    _ = |t/2| * |X x| := abs_mul _ _
    _ ≤ |t/2| * 1 := mul_le_mul_of_nonneg_left (hXb x) (abs_nonneg _)
    _ = |t/2| := mul_one _

def ground (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1) (t : ℝ) : Lp ℝ 2 μ :=
  (amplitude_memLp μ X hX hXb t).toLp (amplitude X t)

def operator (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1) (t : ℝ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  InnerProductSpace.rankOne ℝ (ground μ X hX hXb t) (ground μ X hX hXb t)

theorem ground_square (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1) (t : ℝ) :
    inner ℝ (ground μ X hX hXb t) (ground μ X hX hXb t) = partition μ X t := by
  rw [L2.inner_def]
  unfold partition weighted
  simp only [one_mul]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (amplitude_memLp μ X hX hXb t)] with x hx
  change ground μ X hX hXb t x = amplitude X t x at hx
  rw [hx]
  change amplitude X t x * amplitude X t x = _
  rw [← pow_two,amplitude_square]

theorem ground_eigen (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1) (t : ℝ) :
    operator μ X hX hXb t (ground μ X hX hXb t) =
      partition μ X t • ground μ X hX hXb t := by
  rw [operator,InnerProductSpace.rankOne_apply,ground_square]

theorem orthogonal_annihilated (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1)
    (t : ℝ) (f : Lp ℝ 2 μ) (hf : inner ℝ (ground μ X hX hXb t) f = 0) :
    operator μ X hX hXb t f = 0 := by
  simp [operator,InnerProductSpace.rankOne_apply,hf]

theorem operator_norm (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1) (t : ℝ) :
    ‖operator μ X hX hXb t‖ = partition μ X t := by
  rw [operator,InnerProductSpace.norm_rankOne,← pow_two,← real_inner_self_eq_norm_sq,ground_square]

theorem operator_integral (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1)
    (t : ℝ) (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, operator μ X hX hXb t f x = transfer μ X t f x := by
  have hp : inner ℝ (ground μ X hX hXb t) f = ∫ y, amplitude X t y * f y ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (amplitude_memLp μ X hX hXb t)] with y hy
    change ground μ X hX hXb t y = amplitude X t y at hy
    change f y * ground μ X hX hXb t y = _
    rw [hy,mul_comm]
  simp only [operator,InnerProductSpace.rankOne_apply]
  filter_upwards [Lp.coeFn_smul (inner ℝ (ground μ X hX hXb t) f) (ground μ X hX hXb t),
    MemLp.coeFn_toLp (amplitude_memLp μ X hX hXb t)] with x hx hg
  change ground μ X hX hXb t x = amplitude X t x at hg
  rw [hx]
  change _ * ground μ X hX hXb t x = _
  rw [hg,hp]
  exact mul_comm _ _

/-- Exact ground-state normalization, with the same displayed exponential law. -/
theorem ground_transform (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1)
    (t : ℝ) (f : Ω → ℝ) (x : Ω) :
    transfer μ X t (fun y => amplitude X t y * f y) x /
      (partition μ X t * amplitude X t x) = ∫ y, f y ∂tiltedMeasure μ X t := by
  have he : (fun y => amplitude X t y * (amplitude X t y*f y)) =
      (fun y => f y * Real.exp (t*X y)) := by
    funext y
    rw [← amplitude_square X t y]
    ring
  rw [transfer,he,tilted_integral μ X f hX hXb t]
  unfold expectation weighted
  have hz := (partition_pos μ X hX hXb t).ne'
  have ha : amplitude X t x ≠ 0 := Real.exp_ne_zero _
  field_simp


def normalized (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1) (t : ℝ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := (partition μ X t)⁻¹ • operator μ X hX hXb t

theorem normalized_ground (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1) (t : ℝ) :
    normalized μ X hX hXb t (ground μ X hX hXb t) = ground μ X hX hXb t := by
  simp only [normalized,ContinuousLinearMap.smul_apply,ground_eigen,smul_smul]
  rw [inv_mul_cancel₀ (partition_pos μ X hX hXb t).ne',one_smul]

theorem normalized_orthogonal_gap (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1)
    (t : ℝ) (f : Lp ℝ 2 μ) (hf : inner ℝ (ground μ X hX hXb t) f = 0) :
    inner ℝ f f - inner ℝ (normalized μ X hX hXb t f) f = inner ℝ f f := by
  simp [normalized,orthogonal_annihilated μ X hX hXb t f hf]

theorem centered_transform_zero (hX : Measurable X) (hXb : ∀ x, |X x| ≤ 1)
    (t : ℝ) (f : Ω → ℝ) (hf : (∫ y, f y ∂tiltedMeasure μ X t) = 0) (x : Ω) :
    transfer μ X t (fun y => amplitude X t y*f y) x /
      (partition μ X t*amplitude X t x) = 0 := by
  rw [ground_transform μ X hX hXb t f x,hf]

end OperatorDerivativeRewrite.Foundation.YMResetGroundState

namespace OperatorDerivativeRewrite.Foundation.YMResetGroundState
open QuaternionSU2Representation BoundedExponentialTiltResponse SU2WilsonConvolution
open scoped Topology

theorem wilson_zero_reset (f : SU2 → ℝ) (C : SU2) :
    step 0 f C = ∫ D, f D ∂law := by
  unfold step increment
  rw [SU2StapleExtremes.zero_tilt]
  exact integral_mul_left_eq_self f C

theorem transfer_is_weighted_wilson_reset (t : ℝ) (f : SU2 → ℝ) (C : SU2) :
    transfer law halfTrace t f C = amplitude halfTrace t C *
      step 0 (fun D => amplitude halfTrace t D*f D) C := by
  rw [wilson_zero_reset]
  rfl

def vacuumOverlap (t : ℝ) : ℝ := weighted law halfTrace halfTrace (t/2)

theorem vacuumOverlap_zero : vacuumOverlap 0 = 0 := by
  simp only [vacuumOverlap,zero_div,weighted_zero]
  exact (SU2TiltEnergyResponse.moment_values law).1

theorem vacuumOverlap_derivative : HasDerivAt vacuumOverlap (1/8) 0 := by
  have hd := weighted_hasDerivAt_zero law halfTrace halfTrace halfTrace_measurable
    halfTrace_measurable halfTrace_bound 1 (by norm_num) halfTrace_bound
  have hm : (∫ C, halfTrace C * halfTrace C ∂law) = (1/4:ℝ) := by
    simpa [pow_two] using (SU2TiltEnergyResponse.moment_values law).2.1
  rw [hm] at hd
  have hd' : HasDerivAt (weighted law halfTrace halfTrace) (1/4) (id (0:ℝ)/2) := by
    simpa using hd
  have hh := hd'.comp 0 ((hasDerivAt_id (0:ℝ)).div_const 2)
  norm_num at hh
  exact hh

theorem positive_overlap_near_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ 0 < vacuumOverlap t := by
  obtain ⟨t,ht,he,hv⟩ := positive_derivative_arbitrarily_small_increase vacuumOverlap
    (1/8) vacuumOverlap_derivative (by norm_num) ε hε
  rw [vacuumOverlap_zero] at hv
  exact ⟨t,ht,he,hv⟩

theorem trace_transfer_formula (t : ℝ) (C : SU2) :
    transfer law halfTrace t halfTrace C = amplitude halfTrace t C * vacuumOverlap t := by
  unfold transfer vacuumOverlap weighted amplitude
  congr 1
  apply integral_congr_ae
  filter_upwards with D
  exact mul_comm _ _

theorem centered_trace_moves (ε : ℝ) (hε : 0 < ε) :
    (∫ C, halfTrace C ∂law) = 0 ∧
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ ∀ C : SU2, 0 < transfer law halfTrace t halfTrace C := by
  refine ⟨(SU2TiltEnergyResponse.moment_values law).1, ?_⟩
  obtain ⟨t,ht,he,hv⟩ := positive_overlap_near_zero ε hε
  refine ⟨t,ht,he,fun C => ?_⟩
  rw [trace_transfer_formula]
  exact mul_pos (Real.exp_pos _) hv


theorem amplitude_ratio (t : ℝ) :
    amplitude halfTrace t (1:SU2) / amplitude halfTrace t SU2StapleExtremes.minusOne = Real.exp t := by
  simp only [amplitude,SU2OpenLinkGaugeObstruction.halfTrace_one,
    SU2OpenLinkGaugeObstruction.halfTrace_minusOne]
  rw [← Real.exp_sub]
  congr 1
  ring

theorem trace_mode_not_preserved_near_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧
      ¬∃ lam : ℝ, ∀ C : SU2, transfer law halfTrace t halfTrace C = lam*halfTrace C := by
  obtain ⟨_,t,ht,he,hp⟩ := centered_trace_moves ε hε
  refine ⟨t,ht,he,?_⟩
  rintro ⟨lam,hlam⟩
  have h₁ := hp 1
  have h₂ := hp SU2StapleExtremes.minusOne
  rw [hlam,SU2OpenLinkGaugeObstruction.halfTrace_one] at h₁
  rw [hlam,SU2OpenLinkGaugeObstruction.halfTrace_minusOne] at h₂
  nlinarith

end OperatorDerivativeRewrite.Foundation.YMResetGroundState
