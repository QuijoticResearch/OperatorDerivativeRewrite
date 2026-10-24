import Foundation.IBMRawGridEscape
import Foundation.IBMSecondChaosTesting

/-! Exact second-source-chaos kernels of the ACTUAL compensated native grid.
The intrinsic observable projection is retained; no projection/Fock
commutation or refinement convergence is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawGridSecondChaos
open InfiniteGaussian IBMQuarticSecondChaos IBMQuadraticSpatialCalculus
open IBMTimeAveragedObservable IBMRawStepSources IBMRawStepCompensation
open IBMIntrinsicOperators IBMJointIntrinsicDerivative IBMRawGridCompensation
open GaussianTimeSpaceHermite IBMSecondChaosTesting
open IBMUniformClockGridEnergy
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] jointDerivative LinearPMap.adjoint LinearPMap.graph

theorem cross_inner (u v a b : CoefficientSpace) :
    inner ℝ (cross u v) (cross a b) =
      inner ℝ u a * inner ℝ v b + inner ℝ u b * inner ℝ v a := by
  have he : cross a b = (1/2:ℝ) •
      ((wick (a+b) 2 : GaussianL2)-(wick a 2 : GaussianL2)-(wick b 2 : GaussianL2)) := rfl
  rw [he]
  simp only [inner_smul_right, inner_sub_right, cross_wick_pairing, inner_add_right]
  ring

def increment (u : ℕ → CoefficientSpace) (i : ℕ) : CoefficientSpace := u (i+1)-u i
def sourceSum (u : ℕ → CoefficientSpace) (n : ℕ) : GaussianL2 :=
  ∑ i ∈ Finset.range n, cross (increment u i) (u i)
def centeredQuadratic (u : ℕ → CoefficientSpace) (n : ℕ) : GaussianL2 :=
  ∑ i ∈ Finset.range n, cross (increment u i) (increment u i)

def fieldKernel (u : ℕ → CoefficientSpace) (n : ℕ) : GaussianVectorL2 :=
  ∑ i ∈ Finset.range n, scalarTensor (increment u i) (firstChaosEmbedding (u i))

theorem field_energy (u : ℕ → CoefficientSpace) (n : ℕ) :
    ‖fieldKernel u n‖^2 = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      inner ℝ (increment u i) (increment u j) * inner ℝ (u i) (u j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [fieldKernel, sum_inner, inner_sum, GaussianTimeFieldNorm.scalarTensor_pair_inner,
    firstChaosEmbedding.inner_map_map]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem source_mem_sector (u : ℕ → CoefficientSpace) (n : ℕ) :
    sourceSum u n ∈ GaussianNumberSectors.sector 2 :=
  (GaussianNumberSectors.sector 2).sum_mem fun i _ => cross_mem_sector (increment u i) (u i)

theorem source_wick_test (u : ℕ → CoefficientSpace) (n : ℕ) (k : CoefficientSpace) :
    inner ℝ (sourceSum u n) (wick k 2 : GaussianL2) =
      2 * ∑ i ∈ Finset.range n, inner ℝ (increment u i) k * inner ℝ (u i) k := by
  simp only [sourceSum, sum_inner, cross_wick_pairing, Finset.mul_sum, mul_assoc]

private theorem cross_sub_left (u v a : CoefficientSpace) : cross (u-v) a = cross u a-cross v a := by
  change crossBilinear (u-v) a = crossBilinear u a-crossBilinear v a
  rw [map_sub, sub_apply]

private theorem one_step (u v : CoefficientSpace) :
    (2:ℝ) • cross (v-u) u = cross v v-cross u u-cross (v-u) (v-u) := by
  have h := wickTwo_sub v u
  rw [← cross_self, ← cross_self, ← cross_self] at h
  rw [cross_sub_left]
  rw [h]
  module

theorem telescope (u : ℕ → CoefficientSpace) (n : ℕ) :
    (2:ℝ) • sourceSum u n = cross (u n) (u n)-cross (u 0) (u 0)-centeredQuadratic u n := by
  unfold sourceSum centeredQuadratic increment
  rw [Finset.smul_sum]
  calc
    _ = ∑ i ∈ Finset.range n,
        (cross (u (i+1)) (u (i+1))-cross (u i) (u i)-cross (u (i+1)-u i) (u (i+1)-u i)) :=
      Finset.sum_congr rfl fun i _ => one_step _ _
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => cross (u i) (u i)) n]

theorem source_energy (u : ℕ → CoefficientSpace) (n : ℕ) :
    ‖sourceSum u n‖^2 = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (inner ℝ (increment u i) (increment u j) * inner ℝ (u i) (u j) +
        inner ℝ (increment u i) (u j) * inner ℝ (u i) (increment u j)) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sourceSum, sum_inner, inner_sum, cross_inner]
  rw [Finset.sum_comm]

theorem quadratic_energy (u : ℕ → CoefficientSpace) (n : ℕ) :
    ‖centeredQuadratic u n‖^2 = 2 *
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (inner ℝ (increment u i) (increment u j))^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [centeredQuadratic, sum_inner, inner_sum, cross_inner, pow_two, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (increment u j) (increment u i)]
  ring

theorem terminal_pairing (u : ℕ → CoefficientSpace) (n : ℕ) :
    inner ℝ (cross (u n) (u n)) (centeredQuadratic u n) =
      2 * ∑ i ∈ Finset.range n, (inner ℝ (u n) (increment u i))^2 := by
  simp only [centeredQuadratic, inner_sum, cross_inner, pow_two, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem source_energy_endpoint (u : ℕ → CoefficientSpace) (n : ℕ) (h0 : u 0 = 0) :
    ‖sourceSum u n‖^2 = (1/2:ℝ) * (‖u n‖^4 -
      2 * (∑ i ∈ Finset.range n, (inner ℝ (u n) (increment u i))^2) +
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (inner ℝ (increment u i) (increment u j))^2) := by
  have ht := telescope u n
  have hz : cross (0:CoefficientSpace) 0 = 0 := by
    change crossBilinear 0 0 = 0
    simp only [map_zero]
  rw [h0, hz, sub_zero] at ht
  have he := congrArg (fun z : GaussianL2 => ‖z‖^2) ht
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2), mul_pow,
    norm_sub_sq_real, quadratic_energy, terminal_pairing] at he
  have hh : ‖cross (u n) (u n)‖^2 = 2*‖u n‖^4 := by
    rw [← real_inner_self_eq_norm_sq, cross_inner, real_inner_self_eq_norm_sq]
    ring
  rw [hh] at he
  nlinarith

def clockCurve (h : ℝ≥0) (Y : SampleSpace) (i : ℕ) : CoefficientSpace := clockDirection (grid h i) Y
def sourceGrid (h : ℝ≥0) (n : ℕ) : ValueSpace :=
  ∑ i ∈ Finset.range n, crossSource (grid h i) (grid h (i+1))

def fieldGrid (h : ℝ≥0) (n : ℕ) : FieldSpace :=
  ∑ i ∈ Finset.range n, field (grid h i) (grid h (i+1))

theorem fieldGrid_ae (h : ℝ≥0) (n : ℕ) : fieldGrid h n =ᵐ[gaussianProduct]
    fun Y => fieldKernel (clockCurve h Y) n := by
  have ha := (Finset.eventually_all (Finset.range n)).mpr fun i _ =>
    (field_memLp (grid h i) (grid h (i+1))).coeFn_toLp
  filter_upwards [Lp.coeFn_finsetSum (Finset.range n)
    (fun i => field (grid h i) (grid h (i+1))), ha] with Y hY ha
  change (∑ i ∈ Finset.range n, field (grid h i) (grid h (i+1))) Y = _
  rw [hY]
  simp only [Finset.sum_apply, fieldKernel]
  exact Finset.sum_congr rfl fun i hi => ha i hi

theorem actual_field_energy (h : ℝ≥0) (n : ℕ) :
    ‖fieldGrid h n‖^2 = ∫ Y, ‖fieldKernel (clockCurve h Y) n‖^2 ∂gaussianProduct := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [fieldGrid_ae h n] with Y hY
  rw [hY, real_inner_self_eq_norm_sq]

theorem native_grid_field (h : ℝ≥0) (n : ℕ) :
    (gridInput h n : JointFieldSpace) = pairField (fieldGrid h n) 0 := by
  have he : (gridInput h n : JointFieldSpace) =
      ∑ i ∈ Finset.range n, nativeField (grid h i) (grid h (i+1)) :=
    map_sum jointDivergence.domain.subtype _ _
  rw [he]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [nativeField, pairField, fieldGrid]

theorem native_grid_energy (h : ℝ≥0) (n : ℕ) :
    ‖(gridInput h n : JointFieldSpace)‖^2 =
      ∫ Y, ‖fieldKernel (clockCurve h Y) n‖^2 ∂gaussianProduct := by
  calc
    _ = ‖pairField (fieldGrid h n) 0‖^2 := congrArg (fun z => ‖z‖^2) (native_grid_field h n)
    _ = ‖fieldGrid h n‖^2 := by rw [IBMStochasticNativeDivergence.pair_norm_sq]; simp
    _ = _ := actual_field_energy h n

theorem clockCurve_initial (h : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct, clockCurve h Y 0 = 0 := by
  filter_upwards [GaussianTimeProcess.process_zero_ae] with Y hY
  change clockDirection (grid h 0) Y = 0
  simp only [grid, Nat.cast_zero, mul_zero]
  have hn := direction_norm_sq 0 Y
  rw [hY, abs_zero] at hn
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem sourceGrid_ae (h : ℝ≥0) (n : ℕ) : sourceGrid h n =ᵐ[gaussianProduct]
    fun Y => sourceSum (clockCurve h Y) n := by
  have ha := (Finset.eventually_all (Finset.range n)).mpr fun i _ =>
    (cross_memLp (grid h i) (grid h (i+1))).coeFn_toLp
  filter_upwards [Lp.coeFn_finsetSum (Finset.range n)
    (fun i => crossSource (grid h i) (grid h (i+1))), ha] with Y hY ha
  change (∑ i ∈ Finset.range n, crossSource (grid h i) (grid h (i+1))) Y = _
  rw [hY]
  simp only [Finset.sum_apply, sourceSum]
  exact Finset.sum_congr rfl fun i hi => ha i hi

theorem actual_source_energy (h : ℝ≥0) (n : ℕ) :
    ‖sourceGrid h n‖^2 = ∫ Y, ‖sourceSum (clockCurve h Y) n‖^2 ∂gaussianProduct := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [sourceGrid_ae h n] with Y hY
  rw [hY, real_inner_self_eq_norm_sq]

theorem native_grid_value (h : ℝ≥0) (n : ℕ) :
    jointDivergence (gridInput h n) =
      IntrinsicSpace.orthogonalProjectionOnto (jointRealization (sourceGrid h n)) := by
  have hd : jointDivergence (gridInput h n) =
      ∑ i ∈ Finset.range n, jointDivergence (nativeInput (grid h i) (grid h (i+1))) :=
    map_sum jointDivergence.toFun _ _
  rw [hd]
  change _ = IntrinsicSpace.orthogonalProjectionOnto
    (jointRealization (∑ i ∈ Finset.range n, crossSource (grid h i) (grid h (i+1))))
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => native_value _ _

def loopCurve (h : CoefficientSpace) (i : ℕ) : CoefficientSpace := if i = 1 then h else 0

theorem loop_source (h : CoefficientSpace) : sourceSum (loopCurve h) 2 = -cross h h := by
  have hz (a : CoefficientSpace) : cross 0 a = 0 := by
    change crossBilinear 0 a = 0
    simp only [map_zero, zero_apply]
  have h0 (a : CoefficientSpace) : cross a 0 = 0 := by
    change crossBilinear a 0 = 0
    exact map_zero _
  norm_num [sourceSum, increment, loopCurve, Finset.sum_range_succ, cross_sub_left, hz, h0]

theorem loop_energy (h : CoefficientSpace) : ‖sourceSum (loopCurve h) 2‖^2 = 2*‖h‖^4 := by
  rw [loop_source, norm_neg, ← real_inner_self_eq_norm_sq, cross_inner, real_inner_self_eq_norm_sq]
  ring

end OperatorDerivativeRewrite.Foundation.IBMRawGridSecondChaos
