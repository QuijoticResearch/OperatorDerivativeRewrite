import Foundation.IBMRidgeSeries

/-! Exact centered raw-grid IBM tests of the ORIGINAL compensated output.
No energy-growth or clock-variance asymptotic is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCenteredRawGrid
open InfiniteGaussian IBMTimeAveragedObservable IBMRawStepSources IBMRawStepCompensation
open IBMRawGridCompensation IBMRawGridSecondChaos IBMRawGridObservableTests
open IBMUniformClockGridEnergy IBMSourceProductBounds IBMSchwartzSourceContinuity
open IBMGlobalVacuum IBMCenteredSourceRepresentation IBMIntrinsicOperators IBMJointIntrinsicDerivative
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _ IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] jointDerivative LinearPMap.adjoint LinearPMap.graph

def rawGrid (h : ℝ≥0) (n : ℕ) : ValueSpace :=
  ∑ i ∈ Finset.range n, rawSource (grid h i) (grid h (i+1))

def clockGrid (h : ℝ≥0) (n : ℕ) : ValueSpace := rawGrid h n-sourceGrid h n

def unit : ValueSpace := Lp.const 2 gaussianProduct gaussianOne

def centeredClock (h : ℝ≥0) (n : ℕ) : ValueSpace :=
  clockGrid h n-expectation (rawSum h n) • unit

def centeredRaw (h : ℝ≥0) (n : ℕ) : IntrinsicSpace :=
  rawSum h n-expectation (rawSum h n) • intrinsicOne

def clockScalar (h : ℝ≥0) (n : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i ∈ Finset.range n, inner ℝ (increment (clockCurve h Y) i) (clockCurve h Y i)

theorem rawGrid_actual (h : ℝ≥0) (n : ℕ) : rawGrid h n =ᵐ[gaussianProduct]
    fun Y => ∑ i ∈ Finset.range n,
      rawProduct (increment (clockCurve h Y) i) (clockCurve h Y i) := by
  have ha := (Finset.eventually_all (Finset.range n)).mpr fun i _ =>
    (raw_memLp (grid h i) (grid h (i+1))).coeFn_toLp
  filter_upwards [Lp.coeFn_finsetSum (Finset.range n)
    (fun i => rawSource (grid h i) (grid h (i+1))),ha] with Y hs hr
  change (∑ i ∈ Finset.range n, rawSource (grid h i) (grid h (i+1))) Y = _
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => hr i hi

theorem clockGrid_actual (h : ℝ≥0) (n : ℕ) : clockGrid h n =ᵐ[gaussianProduct]
    fun Y => clockScalar h n Y • (gaussianOne:GaussianL2) := by
  filter_upwards [Lp.coeFn_sub (rawGrid h n) (sourceGrid h n),
    rawGrid_actual h n,sourceGrid_ae h n] with Y hd hr hs
  change clockGrid h n Y = _ at hd
  rw [hd,Pi.sub_apply,hr,hs]
  simp only [rawProduct_eq_cross,Finset.sum_add_distrib,sourceSum,clockScalar]
  rw [add_sub_cancel_left,Finset.sum_smul]

theorem source_clock_orthogonal (h : ℝ≥0) (n : ℕ) :
    inner ℝ (sourceGrid h n) (clockGrid h n) = 0 := by
  rw [L2_inner_eq_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [sourceGrid_ae h n,clockGrid_actual h n] with Y hs hc
  simp only [hs,hc,inner_smul_right,source_mean_zero,mul_zero]
  rfl

theorem source_unit_orthogonal (h : ℝ≥0) (n : ℕ) : inner ℝ (sourceGrid h n) unit = 0 := by
  rw [L2_inner_eq_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [sourceGrid_ae h n,Lp.coeFn_const 2 gaussianProduct (gaussianOne:GaussianL2)] with Y hs hu
  change unit Y = gaussianOne at hu
  rw [hs,hu,source_mean_zero]
  rfl

theorem source_centeredClock_orthogonal (h : ℝ≥0) (n : ℕ) :
    inner ℝ (sourceGrid h n) (centeredClock h n) = 0 := by
  rw [centeredClock,inner_sub_right,inner_smul_right,source_clock_orthogonal,source_unit_orthogonal]
  ring

theorem rawSum_realization (h : ℝ≥0) (n : ℕ) :
    (rawSum h n : JointL2) = jointRealization (rawGrid h n) := by
  have he : (rawSum h n : JointL2) = ∑ i ∈ Finset.range n,
      rawStep (grid h i) (grid h (i+1)) := map_sum IntrinsicSpace.subtype _ _
  rw [he,rawGrid,map_sum]
  rfl

theorem unit_realization : jointRealization unit = (one:JointL2) := by
  apply Lp.ext
  apply (jointRealization_ae_of_sections unit (fun _ => (1:ℝ)) measurable_const ?_).trans one_coeFn.symm
  filter_upwards [Lp.coeFn_const 2 gaussianProduct (gaussianOne:GaussianL2)] with Y hu
  change unit Y = gaussianOne at hu
  rw [hu]
  exact gaussianOne_coeFn

theorem centeredRaw_realization (h : ℝ≥0) (n : ℕ) :
    (centeredRaw h n : JointL2) = jointRealization (sourceGrid h n+centeredClock h n) := by
  change (rawSum h n : JointL2)-expectation (rawSum h n) • (one:JointL2) = _
  rw [rawSum_realization,← unit_realization,centeredClock,clockGrid]
  simp only [map_add,map_sub,map_smul]
  abel

theorem centeredRaw_norm_sq (h : ℝ≥0) (n : ℕ) :
    ‖centeredRaw h n‖^2 = ‖sourceGrid h n‖^2+‖centeredClock h n‖^2 := by
  change ‖(centeredRaw h n : JointL2)‖^2 = _
  rw [centeredRaw_realization,jointRealization.norm_map,norm_add_sq_real,source_centeredClock_orthogonal]
  ring

theorem native_centered_pairing (h : ℝ≥0) (n : ℕ) :
    inner ℝ (jointDivergence (gridInput h n)) (centeredRaw h n) = ‖sourceGrid h n‖^2 := by
  rw [native_grid_value]
  have hp := IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    (centeredRaw h n) (jointRealization (sourceGrid h n))
  rw [hp]
  change inner ℝ (jointRealization (sourceGrid h n)) (centeredRaw h n : JointL2) = _
  rw [centeredRaw_realization,jointRealization.inner_map_map,inner_add_right,
    source_centeredClock_orthogonal,add_zero,real_inner_self_eq_norm_sq]

theorem native_energy_lower_bound (h : ℝ≥0) (n : ℕ) :
    (‖sourceGrid h n‖^2)^2 ≤ ‖jointDivergence (gridInput h n)‖^2*
      (‖sourceGrid h n‖^2+‖centeredClock h n‖^2) := by
  have hi := norm_inner_le_norm (𝕜:=ℝ) (jointDivergence (gridInput h n)) (centeredRaw h n)
  rw [native_centered_pairing,Real.norm_of_nonneg (sq_nonneg _)] at hi
  have hs := mul_self_le_mul_self (sq_nonneg _) hi
  have hsq : (‖sourceGrid h n‖^2)^2 ≤ (‖jointDivergence (gridInput h n)‖*‖centeredRaw h n‖)^2 := by
    simpa only [pow_two] using hs
  rw [mul_pow,centeredRaw_norm_sq] at hsq
  exact hsq

end OperatorDerivativeRewrite.Foundation.IBMCenteredRawGrid
