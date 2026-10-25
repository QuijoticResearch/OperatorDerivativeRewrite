import Foundation.GaussianTerminalStrongBracket

/-! Strong convergence of the actual random-terminal capped-clock quadratic
variation. The surviving weighted bracket is first controlled in clock L2. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClippedClockStrongLimit
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMTerminalBracketWeights IBMTerminalRiemannOccupation IBMRandomBoundaryEnergy
open IBMClippedClockLimit

def weightedClass (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  GaussianTerminalStrongBracket.error φ hφ hb T N+sumClass φ hφ hb T N

theorem weightedClass_actual (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (T : ℝ≥0) (N : ℕ) :
    weightedClass φ hφ hb T N =ᵐ[gaussianProduct] weightedValue φ T N := by
  filter_upwards [Lp.coeFn_add (GaussianTerminalStrongBracket.error φ hφ hb T N)
    (sumClass φ hφ hb T N),GaussianTerminalStrongBracket.error_actual φ hφ hb T N,
    sumClass_actual φ hφ hb T N] with Y ha he hs
  change weightedClass φ hφ hb T N Y = _ at ha
  rw [ha,Pi.add_apply,he,hs]
  unfold actualSum weightedValue
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [uniformTime_step]
  ring

theorem interiorWeightedClass_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (weightedClass IBMTerminalBracketWeights.interior interior_measurable interior_bound T)
      atTop (𝓝 (interiorClass T)) := by
  change Tendsto (fun N => GaussianTerminalStrongBracket.error
    IBMTerminalBracketWeights.interior interior_measurable interior_bound T N+
      sumClass IBMTerminalBracketWeights.interior interior_measurable interior_bound T N)
    atTop (𝓝 (interiorClass T))
  have h := (GaussianTerminalStrongBracket.error_tendsto _ interior_measurable interior_bound T hT).add
    (interior_sumClass_tendsto T)
  simpa only [zero_add] using h

private def lower (u : GaussianL2) : Lp ℝ 1 gaussianProduct :=
  ((Lp.memLp u).mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2)).toLp u

private theorem lower_actual (u : GaussianL2) : lower u =ᵐ[gaussianProduct] u :=
  MemLp.coeFn_toLp _

private theorem lower_norm (u : GaussianL2) : ‖lower u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
  calc
    _ = eLpNorm u 1 gaussianProduct := eLpNorm_congr_ae (lower_actual u)
    _ ≤ eLpNorm u 2 gaussianProduct :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1:ℝ≥0∞) ≤ 2)

private theorem lower_sub (u v : GaussianL2) : lower (u-v) = lower u-lower v := by
  apply Lp.ext
  filter_upwards [lower_actual (u-v),lower_actual u,lower_actual v,
    Lp.coeFn_sub u v,Lp.coeFn_sub (lower u) (lower v)] with Y ha hu hv hs ht
  simp only [ha,ht,hs,Pi.sub_apply,hu,hv]

private theorem lower_tendsto (f : ℕ → GaussianL2) (u : GaussianL2)
    (h : Tendsto f atTop (𝓝 u)) : Tendsto (fun N => lower (f N)) atTop (𝓝 (lower u)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := (tendsto_iff_norm_sub_tendsto_zero.mp h)
  apply squeeze_zero (fun N => norm_nonneg _)
    (fun N => ?_) hn
  rw [← lower_sub]
  exact lower_norm _

def cappedClass (T : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  (cappedSum_integrable T N).toL1 _

theorem cappedClass_actual (T : ℝ≥0) (N : ℕ) :
    cappedClass T N =ᵐ[gaussianProduct] cappedSum T N := (cappedSum_integrable T N).coeFn_toL1

def occupationClass (T : ℝ≥0) : Lp ℝ 1 gaussianProduct := lower (interiorClass T)

theorem occupationClass_actual (T : ℝ≥0) :
    occupationClass T =ᵐ[gaussianProduct] interiorIntegral T :=
  (lower_actual (interiorClass T)).trans (interiorClass_actual T)

private theorem cappedClass_decomposition (T : ℝ≥0) (N : ℕ) :
    cappedClass T N = differenceClass T N+
      lower (weightedClass IBMTerminalBracketWeights.interior interior_measurable interior_bound T N) := by
  apply Lp.ext
  filter_upwards [cappedClass_actual T N,differenceClass_actual T N,
    Lp.coeFn_add (differenceClass T N)
      (lower (weightedClass IBMTerminalBracketWeights.interior interior_measurable interior_bound T N)),
    lower_actual (weightedClass IBMTerminalBracketWeights.interior interior_measurable interior_bound T N),
    weightedClass_actual _ interior_measurable interior_bound T N] with Y hc hd ha hl hw
  rw [hc,ha,Pi.add_apply,hd,hl,hw]
  ring

theorem cappedClass_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (cappedClass T) atTop (𝓝 (occupationClass T)) := by
  have h := (differenceClass_tendsto T hT).add (lower_tendsto _ _ (interiorWeightedClass_tendsto T hT))
  simp only [zero_add] at h
  exact h.congr' (Eventually.of_forall fun N => (cappedClass_decomposition T N).symm)

theorem actual_absolute_error_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => ∫ Y, |cappedSum T N Y-interiorIntegral T Y| ∂gaussianProduct) atTop (𝓝 0) := by
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp (cappedClass_tendsto T hT)
  apply hn.congr'
  exact Eventually.of_forall fun N => by
    change ‖cappedClass T N-occupationClass T‖ =
      ∫ Y, |cappedSum T N Y-interiorIntegral T Y| ∂gaussianProduct
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (cappedClass T N) (occupationClass T),
      cappedClass_actual T N,occupationClass_actual T] with Y hs hc ho
    simp only [hs,Pi.sub_apply,hc,ho,Real.norm_eq_abs]

end OperatorDerivativeRewrite.Foundation.IBMClippedClockStrongLimit
