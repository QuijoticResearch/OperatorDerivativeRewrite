import Foundation.IBMCenteredRawGrid

/-! The remainder in the original IBM output test is an actual clock variance,
with exact folded-clock total-variation identity. No asymptotic bound is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCenteredClockVariance
open InfiniteGaussian IBMTimeAveragedObservable IBMRawStepCompensation
open IBMRawGridCompensation IBMRawGridSecondChaos IBMCenteredRawGrid
open IBMGlobalVacuum IBMCenteredSourceRepresentation IBMUniformClockGridEnergy

def actualClock (h : ℝ≥0) (n : ℕ) (p : IBMSourceLaws.JointSample) : ℝ :=
  ∑ i ∈ Finset.range n, clockFunction (grid h i) (grid h (i+1)) p

theorem clockGrid_realization (h : ℝ≥0) (n : ℕ) :
    jointRealization (clockGrid h n) =
      ∑ i ∈ Finset.range n, clockCorrection (grid h i) (grid h (i+1)) := by
  simp only [clockGrid,rawGrid,sourceGrid,map_sub,map_sum,clockCorrection,rawStep,compensatedStep]
  rw [Finset.sum_sub_distrib]

theorem actualClock_ae (h : ℝ≥0) (n : ℕ) :
    jointRealization (clockGrid h n) =ᵐ[IBMSourceLaws.jointMeasure] actualClock h n := by
  rw [clockGrid_realization]
  have ha := (Finset.eventually_all (Finset.range n)).mpr fun i _ =>
    correction_actual (grid h i) (grid h (i+1))
  filter_upwards [Lp.coeFn_finsetSum (Finset.range n)
    (fun i => clockCorrection (grid h i) (grid h (i+1))),ha] with p hs hc
  rw [hs]
  simp only [Finset.sum_apply,actualClock]
  exact Finset.sum_congr rfl fun i hi => hc i hi

theorem actualClock_memLp (h : ℝ≥0) (n : ℕ) :
    MemLp (actualClock h n) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (jointRealization (clockGrid h n))).ae_eq (actualClock_ae h n)

theorem clock_mean (h : ℝ≥0) (n : ℕ) :
    expectation (rawSum h n) = ∫ p, actualClock h n p ∂IBMSourceLaws.jointMeasure := by
  change inner ℝ (one:JointL2) (rawSum h n : JointL2) = _
  rw [rawSum_realization]
  have he : rawGrid h n = sourceGrid h n+clockGrid h n := by unfold clockGrid; abel
  rw [he,map_add,inner_add_right]
  have hz : inner ℝ (one:JointL2) (jointRealization (sourceGrid h n)) = 0 := by
    rw [← unit_realization,jointRealization.inner_map_map,real_inner_comm,source_unit_orthogonal]
  rw [hz,zero_add,one_inner_mean]
  exact integral_congr_ae (actualClock_ae h n)

theorem centeredClock_actual (h : ℝ≥0) (n : ℕ) :
    jointRealization (centeredClock h n) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => actualClock h n p-(∫ q, actualClock h n q ∂IBMSourceLaws.jointMeasure) := by
  rw [centeredClock,map_sub,map_smul,unit_realization]
  filter_upwards [Lp.coeFn_sub (jointRealization (clockGrid h n))
    (expectation (rawSum h n) • (one:JointL2)),
    Lp.coeFn_smul (expectation (rawSum h n)) (one:JointL2),actualClock_ae h n,one_coeFn]
      with p hd hm hc h1
  rw [hd,Pi.sub_apply,hm,Pi.smul_apply,hc,h1,smul_eq_mul,mul_one,clock_mean]

theorem centered_clock_variance (h : ℝ≥0) (n : ℕ) :
    ‖centeredClock h n‖^2 = ∫ p,
      (actualClock h n p-(∫ q, actualClock h n q ∂IBMSourceLaws.jointMeasure))^2
        ∂IBMSourceLaws.jointMeasure := by
  rw [← jointRealization.norm_map (centeredClock h n),← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [centeredClock_actual h n] with p hp
  rw [hp,Real.inner_apply,pow_two]

theorem centeredRaw_actual (h : ℝ≥0) (n : ℕ) :
    (centeredRaw h n : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => (∑ i ∈ Finset.range n, rawFunction (grid h i) (grid h (i+1)) p)-
        (∫ q, actualClock h n q ∂IBMSourceLaws.jointMeasure) := by
  filter_upwards [Lp.coeFn_sub (rawSum h n : JointL2)
    (expectation (rawSum h n) • (one:JointL2)),
    Lp.coeFn_smul (expectation (rawSum h n)) (one:JointL2),rawSum_actual h n,one_coeFn]
      with p hd hm hr h1
  change (centeredRaw h n : JointL2) p = _ at hd
  rw [hd,Pi.sub_apply,hm,Pi.smul_apply,hr,h1,smul_eq_mul,mul_one,clock_mean]

theorem clock_total_variation_centered (h : ℝ≥0) (n : ℕ) (p : IBMSourceLaws.JointSample) :
    2*(actualClock h n p-(∫ q, actualClock h n q ∂IBMSourceLaws.jointMeasure)) =
      |IBMConstructedSources.clockPath p.2 (grid h n)|-|IBMConstructedSources.clockPath p.2 0|-
        (∑ i ∈ Finset.range n,
          abs (|IBMConstructedSources.clockPath p.2 (grid h (i+1))|-
            |IBMConstructedSources.clockPath p.2 (grid h i)|))-
        2*(∫ q, actualClock h n q ∂IBMSourceLaws.jointMeasure) := by
  have he := clock_total_variation h n p
  change 2*actualClock h n p = _ at he
  linarith

end OperatorDerivativeRewrite.Foundation.IBMCenteredClockVariance
