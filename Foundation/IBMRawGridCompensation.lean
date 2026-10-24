import Foundation.IBMRawStepCompensation
import Foundation.IBMActualQuadraticDivergence

/-! Exact native finite-grid assembly and quantitative mean estimates for
the SAME actual clock compensation. No refinement convergence is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawGridCompensation
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMRawStepCompensation IBMUniformClockGridEnergy IBMRawTemporalKernel GaussianAbsoluteMoments
open IBMCenteredSourceRepresentation IBMGlobalVacuum
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] jointDerivative sourceDerivative clockDerivative
  LinearPMap.adjoint LinearPMap.graph IBMConstructedSources.ibmValue

def expectation : IntrinsicSpace →L[ℝ] ℝ := innerSL ℝ intrinsicOne

theorem expectation_divergence (u : jointDivergence.domain) :
    expectation (jointDivergence u) = 0 :=
  (one_inner_mean _).trans (divergence_mean_zero u)

theorem expectation_raw (s t : ℝ≥0) :
    expectation (rawObservable s t) = kernel s t - kernel s s := by
  change inner ℝ one (rawStep s t) = _
  rw [one_inner_mean]
  calc
    _ = ∫ p, rawFunction s t p ∂IBMSourceLaws.jointMeasure := integral_congr_ae (raw_actual s t)
    _ = (∫ p, IBMConstructedSources.ibmValue s p * IBMConstructedSources.ibmValue t p
          ∂IBMSourceLaws.jointMeasure) -
        ∫ p, IBMConstructedSources.ibmValue s p * IBMConstructedSources.ibmValue s p
          ∂IBMSourceLaws.jointMeasure := by
      simp only [rawFunction, mul_sub]
      exact integral_sub (actual_product_integrable s t) (actual_product_integrable s s)
    _ = _ := by rw [actual_product, actual_product]

theorem expectation_correction (s t : ℝ≥0) :
    expectation (IntrinsicSpace.orthogonalProjectionOnto (clockCorrection s t)) =
      kernel s t - kernel s s := by
  have h := congrArg expectation (stochastic_identity s t)
  rw [map_add, expectation_divergence, zero_add] at h
  exact h.symm.trans (expectation_raw s t)

def gridInput (h : ℝ≥0) (n : ℕ) : jointDivergence.domain :=
  ∑ i ∈ Finset.range n, nativeInput (grid h i) (grid h (i+1))

def rawSum (h : ℝ≥0) (n : ℕ) : IntrinsicSpace :=
  ∑ i ∈ Finset.range n, rawObservable (grid h i) (grid h (i+1))

def correctionSum (h : ℝ≥0) (n : ℕ) : IntrinsicSpace :=
  ∑ i ∈ Finset.range n, IntrinsicSpace.orthogonalProjectionOnto (clockCorrection (grid h i) (grid h (i+1)))

theorem finite_identity (h : ℝ≥0) (n : ℕ) :
    rawSum h n = jointDivergence (gridInput h n) + correctionSum h n := by
  have hd : jointDivergence (gridInput h n) =
      ∑ i ∈ Finset.range n, jointDivergence (nativeInput (grid h i) (grid h (i+1))) := by
    exact map_sum jointDivergence.toFun _ _
  rw [hd]
  change (∑ i ∈ Finset.range n, _) = (∑ i ∈ Finset.range n, _) + ∑ i ∈ Finset.range n, _
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => stochastic_identity _ _

theorem rawSum_actual (h : ℝ≥0) (n : ℕ) :
    ((rawSum h n : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => ∑ i ∈ Finset.range n, rawFunction (grid h i) (grid h (i+1)) p := by
  have he : ((rawSum h n : IntrinsicSpace) : JointL2) =
      ∑ i ∈ Finset.range n, rawStep (grid h i) (grid h (i+1)) := by
    exact map_sum IntrinsicSpace.subtype _ _
  rw [he]
  have ha := (Finset.eventually_all (Finset.range n)).mpr fun i _ => raw_actual (grid h i) (grid h (i+1))
  filter_upwards [Lp.coeFn_finsetSum (Finset.range n) (fun i => rawStep (grid h i) (grid h (i+1))), ha]
    with p hp ha
  rw [hp]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => ha i hi

theorem uniform_rawSum_actual (T : ℝ≥0) (n : ℕ) :
    ((rawSum (T/(n+1)) (n+1) : IntrinsicSpace) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure]
        fun p => (1/2:ℝ) * IBMActualQuadraticDivergence.first T n p := by
  apply (rawSum_actual _ _).trans
  apply ae_of_all
  intro p
  change (∑ i ∈ Finset.range (n+1), rawFunction (grid (T/(n+1)) i)
    (grid (T/(n+1)) (i+1)) p) = (1/2:ℝ) * IBMActualQuadraticDivergence.first T n p
  unfold IBMActualQuadraticDivergence.first rawFunction
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem min_step (a b : ℝ) : 2*(min a b-a) = b-a-|b-a| := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonneg (sub_nonneg.mpr hab)]
    ring
  · rw [min_eq_right hba, abs_of_nonpos (sub_nonpos.mpr hba)]
    ring

/-- The SAME finite clock correction is half an endpoint minus clock total variation. -/
theorem clock_total_variation (h : ℝ≥0) (n : ℕ) (p : IBMSourceLaws.JointSample) :
    2 * (∑ i ∈ Finset.range n, clockFunction (grid h i) (grid h (i+1)) p) =
      |IBMConstructedSources.clockPath p.2 (grid h n)| - |IBMConstructedSources.clockPath p.2 0| -
        ∑ i ∈ Finset.range n,
          abs (|IBMConstructedSources.clockPath p.2 (grid h (i+1))| -
            |IBMConstructedSources.clockPath p.2 (grid h i)|) := by
  rw [Finset.mul_sum]
  have hi (i : ℕ) := min_step |IBMConstructedSources.clockPath p.2 (grid h i)|
    |IBMConstructedSources.clockPath p.2 (grid h (i+1))|
  calc
    _ = ∑ i ∈ Finset.range n,
        (|IBMConstructedSources.clockPath p.2 (grid h (i+1))| -
          |IBMConstructedSources.clockPath p.2 (grid h i)| -
          abs (|IBMConstructedSources.clockPath p.2 (grid h (i+1))| -
            |IBMConstructedSources.clockPath p.2 (grid h i)|)) :=
      Finset.sum_congr rfl fun i _ => hi i
    _ = _ := by
      rw [Finset.sum_sub_distrib,
        Finset.sum_range_sub (fun i : ℕ => |IBMConstructedSources.clockPath p.2 (grid h i)|) n]
      simp only [grid, Nat.cast_zero, mul_zero]

private theorem diagonal_value (s : ℝ≥0) : kernel s s = standardMoment 1 * Real.sqrt s := by
  rw [← actual_inner, real_inner_self_eq_norm_sq, IBMPhysicalL2Obstruction.observed_norm_sq]
  ring

theorem step_mean_bound {s t : ℝ≥0} (hst : s ≤ t) :
    kernel s t - kernel s s ≤ standardMoment 1 *
      (Real.sqrt t - Real.sqrt s - Real.sqrt ((t:ℝ)-s)/2) := by
  have hst' : (s : ℝ) ≤ t := hst
  have hr := Real.sqrt_le_sqrt (show 4*(s:ℝ) ≤ (s:ℝ)+t+2*s by linarith)
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)] at hr
  norm_num only [show Real.sqrt (4:ℝ) = 2 by norm_num] at hr
  have hm := mul_le_mul_of_nonneg_left hr IBMPhysicalL2Obstruction.first_absolute_moment_pos.le
  rw [diagonal_value]
  unfold kernel
  rw [min_eq_left hst', abs_of_nonneg (sub_nonneg.mpr hst')]
  nlinarith

theorem grid_mean_bound (h : ℝ≥0) (n : ℕ) :
    expectation (correctionSum h n) ≤ standardMoment 1 *
      (Real.sqrt (grid h n) - (n:ℝ)*Real.sqrt h/2) := by
  have hs (i : ℕ) :
      expectation (IntrinsicSpace.orthogonalProjectionOnto
        (clockCorrection (grid h i) (grid h (i+1)))) ≤ standardMoment 1 *
          (Real.sqrt (grid h (i+1))-Real.sqrt (grid h i)-Real.sqrt h/2) := by
    rw [expectation_correction]
    have hi : grid h i ≤ grid h (i+1) := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ i) h.coe_nonneg
    have hd : ((grid h (i+1):ℝ≥0):ℝ) - grid h i = h := by
      unfold grid
      push_cast
      ring
    simpa only [hd] using step_mean_bound hi
  calc
    _ = ∑ i ∈ Finset.range n, expectation (IntrinsicSpace.orthogonalProjectionOnto
        (clockCorrection (grid h i) (grid h (i+1)))) := map_sum expectation _ _
    _ ≤ ∑ i ∈ Finset.range n, standardMoment 1 *
        (Real.sqrt (grid h (i+1))-Real.sqrt (grid h i)-Real.sqrt h/2) :=
      Finset.sum_le_sum fun i _ => hs i
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_range_sub (fun i : ℕ => Real.sqrt (grid h i)) n]
      simp only [grid, Nat.cast_zero, mul_zero, NNReal.coe_zero, Real.sqrt_zero, sub_zero,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

theorem one_norm : ‖intrinsicOne‖ = 1 := by
  have he : (one : JointL2) = Lp.const 2 IBMSourceLaws.jointMeasure (1 : ℝ) := by
    apply Lp.ext
    exact one_coeFn.trans (Lp.coeFn_const 2 IBMSourceLaws.jointMeasure (1 : ℝ)).symm
  change ‖(one : JointL2)‖ = 1
  rw [he]
  norm_num [Lp.norm_const]

theorem neg_expectation_le_norm (f : IntrinsicSpace) : -expectation f ≤ ‖f‖ := by
  have hi := norm_inner_le_norm (𝕜 := ℝ) intrinsicOne f
  rw [one_norm, one_mul, Real.norm_eq_abs] at hi
  exact (neg_le_abs _).trans hi

end OperatorDerivativeRewrite.Foundation.IBMRawGridCompensation
