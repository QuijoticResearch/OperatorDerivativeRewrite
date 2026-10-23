import Foundation.IBMActualPeanoRemainder

/-! A genuine C4 physical-time Taylor-chain limit for actual reflected-clock
IBM. The first three raw Taylor ranks are kept together; no individual
rank limit or classical semimartingale integral is asserted. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMActualTaylorChain
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy IBMFourthPeano
open IBMContinuousWeightedQuartic IBMUniformFifthRemainder
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

def channels (f : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), lower f (ibmValue (grid (T/(n + 1)) i) ω)
    (ibmValue (grid (T/(n + 1)) (i + 1)) ω)

def endpointDifference (f : ℝ → ℝ) (T : ℝ≥0) (ω : JointSample) : ℝ :=
  f (ibmValue T ω)-f (ibmValue 0 ω)

def limitValue (f : ℝ → ℝ) (T : ℝ≥0) (ω : JointSample) : ℝ :=
  endpointDifference f T ω - (1/8 : ℝ)*timeIntegral T (iteratedDeriv 4 f) ω

/-- Exact finite identity before any stochastic passage to a limit. -/
theorem finite_identity (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (T : ℝ≥0)
    (n : ℕ) (ω : JointSample) :
    endpointDifference f T ω = channels f T n ω +
      (1/24 : ℝ)*weighted T (iteratedDeriv 4 f) n ω + remainderSum f T n ω := by
  have hs : (∑ i ∈ Finset.range (n + 1),
      (f (ibmValue (grid (T/(n + 1)) (i + 1)) ω) -
        f (ibmValue (grid (T/(n + 1)) i) ω))) =
      channels f T n ω + (1/24 : ℝ)*weighted T (iteratedDeriv 4 f) n ω +
        remainderSum f T n ω := by
    unfold channels weighted remainderSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [mul_assoc] using increment_identity f hf
      (ibmValue (grid (T/(n + 1)) i) ω) (ibmValue (grid (T/(n + 1)) (i + 1)) ω)
  have ht := Finset.sum_range_sub (fun i => f (ibmValue (grid (T/(n + 1)) i) ω)) (n + 1)
  have hz : grid (T/(n + 1)) 0 = 0 := by simp [grid]
  have hend : grid (T/(n + 1)) (n + 1) = T := by
    unfold grid
    push_cast
    exact div_mul_cancel₀ T (by positivity)
  rw [hz, hend] at ht
  exact ht.symm.trans hs

attribute [local irreducible] IBMFourthPeano.lower

theorem channels_measurable (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (T : ℝ≥0) (n : ℕ) :
    Measurable (channels f T n) := by
  have h1 := ContDiff.continuous_iteratedDeriv 1 hf (by norm_num)
  have h2 := ContDiff.continuous_iteratedDeriv 2 hf (by norm_num)
  have h3 := ContDiff.continuous_iteratedDeriv 3 hf (by norm_num)
  have hc : Continuous (fun p : ℝ × ℝ => lower f p.1 p.2) := by
    unfold lower
    fun_prop
  have hm (r : ℝ≥0) : Measurable (ibmValue r) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  unfold channels
  apply Finset.measurable_sum
  intro i hi
  exact hc.measurable.comp
    ((hm (grid (T/(n + 1)) i)).prodMk (hm (grid (T/(n + 1)) (i + 1))))

theorem limitValue_measurable (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (T : ℝ≥0) :
    Measurable (limitValue f T) := by
  have h4 := ContDiff.continuous_iteratedDeriv 4 hf (by norm_num)
  have hm (r : ℝ≥0) : Measurable (ibmValue r) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  exact ((hf.continuous.measurable.comp (hm T)).sub
    (hf.continuous.measurable.comp (hm 0))).sub ((timeIntegral_measurable T _ h4).const_mul _)

theorem deviation_identity (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (T : ℝ≥0)
    (n : ℕ) (ω : JointSample) :
    channels f T n ω - limitValue f T ω =
      -(1/24 : ℝ)*(weighted T (iteratedDeriv 4 f) n ω -
        3*timeIntegral T (iteratedDeriv 4 f) ω) - remainderSum f T n ω := by
  have h := finite_identity f hf T n ω
  unfold limitValue
  linarith

attribute [local irreducible] channels limitValue IBMContinuousWeightedQuartic.weighted
  IBMContinuousWeightedQuartic.timeIntegral IBMUniformFifthRemainder.remainderSum

/-- The combined genuine first THREE Taylor channels converge in probability,
with the physical fourth-derivative correction 1/8, on the entire C4 domain. -/
theorem channels_tendstoInMeasure (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (channels f T) atTop (limitValue f T) := by
  have h4 := ContDiff.continuous_iteratedDeriv 4 hf (by norm_num)
  have hw := tendstoInMeasure_iff_measureReal_norm.mp (weighted_tendstoInMeasure hT _ h4)
  have hr := tendstoInMeasure_iff_measureReal_norm.mp
    (IBMActualPeanoRemainder.signed_tendstoInMeasure f hf hT)
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have hb (n : ℕ) :
      jointMeasure.real {ω | ε ≤ |channels f T n ω-limitValue f T ω|} ≤
      jointMeasure.real {ω | 12*ε ≤ |weighted T (iteratedDeriv 4 f) n ω -
        3*timeIntegral T (iteratedDeriv 4 f) ω|} +
      jointMeasure.real {ω | ε/2 ≤ |remainderSum f T n ω|} := by
    apply le_trans (measureReal_mono (μ := jointMeasure) (s₂ :=
      {ω | 12*ε ≤ |weighted T (iteratedDeriv 4 f) n ω -
        3*timeIntegral T (iteratedDeriv 4 f) ω|} ∪
      {ω | ε/2 ≤ |remainderSum f T n ω|}) ?_ (measure_ne_top _ _))
      (measureReal_union_le _ _)
    intro ω hω
    by_contra hn
    have h1 : |weighted T (iteratedDeriv 4 f) n ω -
        3*timeIntegral T (iteratedDeriv 4 f) ω| < 12*ε :=
      lt_of_not_ge fun h => hn (Or.inl h)
    have h2 : |remainderSum f T n ω| < ε/2 := lt_of_not_ge fun h => hn (Or.inr h)
    change ε ≤ |channels f T n ω-limitValue f T ω| at hω
    rw [deviation_identity f hf] at hω
    have ha := abs_sub_le
      (-(1/24 : ℝ)*(weighted T (iteratedDeriv 4 f) n ω -
        3*timeIntegral T (iteratedDeriv 4 f) ω)) 0 (remainderSum f T n ω)
    simp only [sub_zero, zero_sub, abs_neg, abs_mul] at ha
    norm_num at ha
    rw [neg_mul] at hω
    linarith
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [sub_zero, Real.norm_eq_abs, add_zero] using
    (hw (12*ε) (by positivity)).add (hr (ε/2) (by positivity))

end OperatorDerivativeRewrite.Foundation.IBMActualTaylorChain
