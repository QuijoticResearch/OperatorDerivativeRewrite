import Foundation.IBMRandomBoundaryOccupation

/-! Exact prediction of actual centered Brownian squared increments from
the ENTIRE past plus one terminal observation. This permits anticipative
coefficients without asserting predictability or a new stochastic law. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianTerminalBracketPrediction
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeDivergence
open GaussianTimeFieldNorm GaussianTimeSpaceHermite GaussianConditionalGraph
open GaussianWickConditionalProjection SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

def observation (s T : ℝ≥0) : Option (Iic s) → CoefficientSpace
  | none => hilbertEmbedding TimeHilbert (timeVector T)
  | some r => hilbertEmbedding TimeHilbert (timeVector r.val)

def bridgeDirection (s t T : ℝ≥0) : CoefficientSpace :=
  (((t:ℝ)-s)/((T:ℝ)-s)) • incrementDirection s T

theorem increment_terminal_inner (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    inner ℝ (incrementDirection s t) (hilbertEmbedding TimeHilbert (timeVector T)) = (t:ℝ)-s := by
  unfold incrementDirection
  rw [(hilbertEmbedding TimeHilbert).inner_map_map,← timeVector_sub s t hst,
    inner_sub_left,timeVector_inner,timeVector_inner,min_eq_left (show (t:ℝ) ≤ T from htT),
    min_eq_left (show (s:ℝ) ≤ T from hst.trans htT)]

theorem bridge_covariances (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (hsT : s < T)
    (i : Option (Iic s)) :
    inner ℝ (incrementDirection s t) (observation s T i) =
      inner ℝ (bridgeDirection s t T) (observation s T i) := by
  cases i with
  | none =>
    change inner ℝ (incrementDirection s t) (hilbertEmbedding TimeHilbert (timeVector T)) = _
    rw [increment_terminal_inner s t T hst htT]
    simp only [bridgeDirection,observation,real_inner_smul_left,
      increment_terminal_inner s T T (le_of_lt hsT) le_rfl]
    exact (div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt (show (s:ℝ)<T from hsT)))).symm
  | some r =>
    simp only [observation,bridgeDirection,real_inner_smul_left]
    have h1 : inner ℝ (incrementDirection s t) (hilbertEmbedding TimeHilbert (timeVector r.val)) = 0 :=
      (real_inner_comm _ _).trans (pastDirection_inner_increment r.val s t r.property hst)
    have h2 : inner ℝ (incrementDirection s T) (hilbertEmbedding TimeHilbert (timeVector r.val)) = 0 :=
      (real_inner_comm _ _).trans (pastDirection_inner_increment r.val s T r.property hsT.le)
    rw [h1,h2,mul_zero]

theorem bridge_mem_sourceSpan (s t T : ℝ≥0) (hsT : s ≤ T) :
    bridgeDirection s t T ∈ sourceSpan (observation s T) := by
  have hT : hilbertEmbedding TimeHilbert (timeVector T) ∈ sourceSpan (observation s T) :=
    (Submodule.span ℝ (Set.range (observation s T))).le_topologicalClosure
      (Submodule.subset_span ⟨none,rfl⟩)
  have hs : hilbertEmbedding TimeHilbert (timeVector s) ∈ sourceSpan (observation s T) :=
    (Submodule.span ℝ (Set.range (observation s T))).le_topologicalClosure
      (Submodule.subset_span ⟨some ⟨s,by simp⟩,rfl⟩)
  have he : incrementDirection s T = hilbertEmbedding TimeHilbert (timeVector T)-
      hilbertEmbedding TimeHilbert (timeVector s) := by
    unfold incrementDirection
    rw [← timeVector_sub s T hsT,map_sub]
  rw [bridgeDirection,he]
  exact (sourceSpan (observation s T)).smul_mem _
    ((sourceSpan (observation s T)).sub_mem hT hs)

theorem conditional_square (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (hsT : s < T) :
    conditionalProjection (observation s T) (wick (incrementDirection s t) 2) =
      (wick (bridgeDirection s t T) 2 : GaussianL2) := by
  rw [conditional_wick_eq_of_covariances (observation s T) _ _
    (bridge_covariances s t T hst htT hsT) 2]
  exact Submodule.starProjection_eq_self_iff.mpr
    (wick_mem_generated_of_sourceSpan _ _ (bridge_mem_sourceSpan s t T hsT.le) 2)

theorem increment_wick_actual (s t : ℝ≥0) (hst : s ≤ t) :
    (wick (incrementDirection s t) 2 : GaussianL2) =ᵐ[gaussianProduct]
      fun Y => (process t Y-process s Y)^2-((t:ℝ)-s) := by
  filter_upwards [IBMQuarticSecondChaos.wickTwo_coeFn (incrementDirection s t),
    process_increment_ae s t hst] with Y hw hi
  change firstChaosEmbedding (incrementDirection s t) Y = process t Y-process s Y at hi
  rw [hw,hi,incrementDirection_norm_sq s t hst]

theorem conditional_square_actual (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (hsT : s < T) :
    conditionalProjection (observation s T) (wick (incrementDirection s t) 2) =ᵐ[gaussianProduct]
      fun Y => (((t:ℝ)-s)/((T:ℝ)-s))^2*((process T Y-process s Y)^2-((T:ℝ)-s)) := by
  rw [conditional_square s t T hst htT hsT]
  unfold bridgeDirection
  rw [IBMFirstChaosMixedStein.wick_two_smul]
  filter_upwards [Lp.coeFn_smul ((((t:ℝ)-s)/((T:ℝ)-s))^2)
    (wick (incrementDirection s T) 2 : GaussianL2),increment_wick_actual s T hsT.le] with Y hs hi
  rw [hs,Pi.smul_apply,hi,smul_eq_mul]

theorem bridge_norm_sq (s t T : ℝ≥0) (hsT : s < T) :
    ‖bridgeDirection s t T‖^2 = ((t:ℝ)-s)^2/((T:ℝ)-s) := by
  rw [bridgeDirection,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    incrementDirection_norm_sq s T hsT.le]
  have hn : (T:ℝ)-s ≠ 0 := sub_ne_zero.mpr (ne_of_gt (show (s:ℝ)<T from hsT))
  field_simp

theorem generated_pairing (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (hsT : s < T)
    (a : GaussianL2) (ha : a ∈ generated (observation s T)) :
    inner ℝ (wick (incrementDirection s t) 2 : GaussianL2) a =
      inner ℝ (wick (bridgeDirection s t T) 2 : GaussianL2) a := by
  have hp := (generated (observation s T)).starProjection_inner_eq_zero
    (wick (incrementDirection s t) 2 : GaussianL2) a ha
  rw [inner_sub_left] at hp
  change inner ℝ (wick (incrementDirection s t) 2 : GaussianL2) a-
    inner ℝ (conditionalProjection (observation s T) (wick (incrementDirection s t) 2)) a=0 at hp
  rw [conditional_square s t T hst htT hsT] at hp
  linarith

theorem generated_pairing_bound (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (hsT : s < T)
    (a : GaussianL2) (ha : a ∈ generated (observation s T)) :
    |inner ℝ (wick (incrementDirection s t) 2 : GaussianL2) a| ≤
      (2*((t:ℝ)-s)^2/((T:ℝ)-s))*‖a‖ := by
  rw [generated_pairing s t T hst htT hsT a ha]
  have hn : ‖(wick (bridgeDirection s t T) 2 : GaussianL2)‖ ≤
      2*‖bridgeDirection s t T‖^2 := by
    rw [← IBMQuarticSecondChaos.cross_self]
    simpa only [pow_two,mul_assoc] using
      IBMQuadraticSpatialCalculus.cross_norm_le (bridgeDirection s t T) (bridgeDirection s t T)
  calc
    _ ≤ ‖(wick (bridgeDirection s t T) 2 : GaussianL2)‖*‖a‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_inner_le_norm (𝕜:=ℝ) (wick (bridgeDirection s t T) 2 : GaussianL2) a
    _ ≤ (2*‖bridgeDirection s t T‖^2)*‖a‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = _ := by rw [bridge_norm_sq s t T hsT]; ring_nf

theorem actual_error_integrable (s t : ℝ≥0) (hst : s ≤ t) (a : GaussianL2) :
    Integrable (fun Y => ((process t Y-process s Y)^2-((t:ℝ)-s))*a Y) gaussianProduct := by
  apply (L2.integrable_inner (wick (incrementDirection s t) 2 : GaussianL2) a).congr
  filter_upwards [increment_wick_actual s t hst] with Y hY
  rw [hY,Real.inner_apply,mul_comm]

theorem actual_error_pairing (s t : ℝ≥0) (hst : s ≤ t) (a : GaussianL2) :
    (∫ Y, ((process t Y-process s Y)^2-((t:ℝ)-s))*a Y ∂gaussianProduct) =
      inner ℝ (wick (incrementDirection s t) 2 : GaussianL2) a := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [increment_wick_actual s t hst] with Y hY
  rw [hY,Real.inner_apply,mul_comm]

end OperatorDerivativeRewrite.Foundation.GaussianTerminalBracketPrediction
