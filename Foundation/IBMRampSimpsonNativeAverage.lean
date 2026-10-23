import Foundation.IBMBochnerTimeQuadrature
import Foundation.IBMTimeWeightedSimpson
import Foundation.IBMIntrinsicGraphDual
import Foundation.IBMRawInitialPast

/-! Actual ramp-weighted signed Simpson sums converge in observable L2 to the
OLD native IBM average, whose strong joint derivative represents the dual limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMRampSimpsonNativeAverage
open IBMSourceLaws IBMConstructedSources IBMTimeAveragedObservable
open IBMJointIntrinsicDerivative IBMContinuousQuadrature IBMUniformClockGridEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    sceneryPath_measurable clockPath_measurable).completeSpace_coe

def sums (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  IBMTimeWeightedSimpson.weighted (fun t => (T : ℝ)-t) (fun _ => 1) T n ω

theorem finite_identity (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    sums T n ω = (∑ i ∈ Finset.range (n + 1),
      ((T : ℝ)/(n + 1)) * ibmValue (grid (T / (n + 1)) (i + 1)) ω) - (T : ℝ)*ibmValue 0 ω := by
  have he : sums T n ω = ∑ i ∈ Finset.range (n + 1), ((T : ℝ)-time T (n + 1) i)*
      (ibmValue (grid (T / (n + 1)) (i + 1)) ω-ibmValue (grid (T / (n + 1)) i) ω) := by
    unfold sums IBMTimeWeightedSimpson.weighted
    apply Finset.sum_congr rfl
    intro i hi
    unfold IBMSimpsonPeano.simpson
    ring
  have hb := IBMTimeWeightQuadrature.discrete_by_parts
    (fun i => (T : ℝ)-time T (n + 1) i)
    (fun i => ibmValue (grid (T / (n + 1)) i) ω) (n + 1)
  have ht : time T (n + 1) (n + 1) = T := by unfold time; exact div_mul_cancel₀ _ (by positivity)
  have hz : time T (n + 1) 0 = 0 := by simp [time]
  have hg : grid (T / (n + 1)) 0 = 0 := by simp [grid]
  have hd (i : ℕ) : ((T : ℝ)-time T (n + 1) (i + 1))-((T : ℝ)-time T (n + 1) i) =
      -(T : ℝ)/(n + 1) := by
    have hs := time_step T (n + 1) i
    push_cast at hs
    rw [neg_div]
    linarith
  simp only [ht,hz,hg,sub_self,zero_mul,sub_zero] at hb
  simp_rw [hd] at hb
  rw [← Finset.sum_mul] at hb
  rw [he, ← Finset.mul_sum]
  linear_combination hb

def intrinsicValue (T : ℝ≥0) (n : ℕ) : IntrinsicSpace :=
  IBMBochnerTimeQuadrature.rightSum (fun t => intrinsicCurve t.toNNReal) T (n + 1)

theorem intrinsicValue_actual_ae (T : ℝ≥0) (n : ℕ) :
    (intrinsicValue T n : JointL2) =ᵐ[jointMeasure] sums T n := by
  let c : ℝ := (T : ℝ)/(n + 1)
  let u : ℕ → JointL2 := fun i => (intrinsicCurve (grid (T / (n + 1)) (i + 1)) : JointL2)
  have he : (intrinsicValue T n : JointL2) = ∑ i ∈ Finset.range (n + 1), c • u i := by
    simp only [intrinsicValue, IBMBochnerTimeQuadrature.rightSum,
      Submodule.coe_sum, Submodule.coe_smul, IBMContinuousWeightedQuartic.real_time_eq_grid,
      Real.toNNReal_coe, c, u, Nat.cast_add, Nat.cast_one]
  rw [he]
  filter_upwards [Lp.coeFn_finsetSum (Finset.range (n + 1)) (fun i => c • u i),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul c (u i)),
    ae_all_iff.mpr (fun i => joint_point_actual_ae (grid (T / (n + 1)) (i + 1))),
    IBMRawInitialPast.ibm_zero_ae] with ω hsum hsmul hpoint hzero
  rw [hsum, finite_identity, hzero, mul_zero, sub_zero]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsmul i]
  change c * (u i) ω = _
  rw [show (u i) ω = ibmValue (grid (T / (n + 1)) (i + 1)) ω from hpoint i]

theorem sums_memLp (T : ℝ≥0) (n : ℕ) : MemLp (sums T n) 2 jointMeasure :=
  (memLp_congr_ae (intrinsicValue_actual_ae T n)).mp
    (Lp.memLp (intrinsicValue T n : JointL2))

theorem intrinsicValue_first (T : ℝ≥0) : intrinsicValue T 0 = (T : ℝ) • intrinsicCurve T := by
  simp [intrinsicValue, IBMBochnerTimeQuadrature.rightSum, time]

/-- Even the first actual approximant is outside the strong joint domain at
positive horizons. Strong L2 convergence below is NOT derivative graph convergence. -/
theorem first_not_joint_domain (T : ℝ≥0) (hT : 0 < T) :
    intrinsicValue T 0 ∉ jointDerivative.domain := by
  rw [intrinsicValue_first]
  intro hm
  have hs := jointDerivative.domain.smul_mem (T : ℝ)⁻¹ hm
  have hT' : (T : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hT)
  rw [smul_smul, inv_mul_cancel₀ hT', one_smul] at hs
  exact IBMPointClockDomainObstruction.actual_point_not_joint_domain T hT hs

theorem intrinsicValue_tendsto (T : ℝ≥0) :
    Tendsto (intrinsicValue T) atTop (𝓝 (intrinsicAverage T)) := by
  have h := IBMBochnerTimeQuadrature.rightSum_tendsto
    (fun t => intrinsicCurve t.toNNReal)
    (intrinsicCurve_continuous.comp continuous_real_toNNReal) T.coe_nonneg
  have he : (∫ t in (0 : ℝ)..(T : ℝ), intrinsicCurve t.toNNReal) = intrinsicAverage T := by
    rw [intervalIntegral.integral_of_le T.coe_nonneg]
    rfl
  rw [he] at h
  exact h

theorem average_mem_joint_domain (T : ℝ≥0) : intrinsicAverage T ∈ jointDerivative.domain := by
  apply (joint_domain_iff _).mpr
  rw [← nativeAverage_eq_intrinsicAverage]
  exact IBMFiniteAverageCore.nativeAverage_mem T T.coe_nonneg

def averageGradient (T : ℝ≥0) : JointFieldSpace :=
  jointDerivative ⟨intrinsicAverage T, average_mem_joint_domain T⟩

attribute [local irreducible] intrinsicValue intrinsicAverage jointDerivative
  IBMIntrinsicGraphDual.weakDerivative IBMIntrinsicGraphDual.embed

theorem averageGradient_embed (T : ℝ≥0) :
    IBMIntrinsicGraphDual.embed (averageGradient T) =
      IBMIntrinsicGraphDual.weakDerivative (intrinsicAverage T) :=
  IBMIntrinsicGraphDual.original_graph
    (⟨intrinsicAverage T, average_mem_joint_domain T⟩ : jointDerivative.domain)

attribute [local irreducible] averageGradient

/-- The weak derivatives of ACTUAL stochastic approximants converge in the
ORIGINAL graph-dual norm to the embedded STRONG derivative of the native average.
No derivative-domain membership of the finite point quadratures is asserted. -/
theorem derivative_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMIntrinsicGraphDual.weakDerivative (intrinsicValue T n)) atTop
      (𝓝 (IBMIntrinsicGraphDual.weakDerivative (intrinsicAverage T))) :=
  (IBMIntrinsicGraphDual.weakDerivative.continuous.tendsto _).comp (intrinsicValue_tendsto T)

theorem actual_pairing_integrable (T : ℝ≥0) (n : ℕ) (v : jointDivergence.domain) :
    Integrable (fun ω => sums T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω) jointMeasure :=
  IBMIntrinsicGraphDual.actual_pairing_integrable (intrinsicValue T n) (sums T n)
    (intrinsicValue_actual_ae T n) v

/-- Actual signed stochastic sums converge against EVERY original adjoint-domain
test to the pairing of the genuine strong intrinsic derivative of the average. -/
theorem actual_pairing_tendsto (T : ℝ≥0) (v : jointDivergence.domain) :
    Tendsto (fun n => ∫ ω, sums T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂jointMeasure) atTop
      (𝓝 (inner ℝ (averageGradient T) (v : JointFieldSpace))) := by
  have he (n : ℕ) := IBMIntrinsicGraphDual.actual_pairing (intrinsicValue T n) (sums T n)
    (intrinsicValue_actual_ae T n) v
  have h := ((ContinuousLinearMap.apply ℝ ℝ (IBMIntrinsicGraphDual.testOf v)).continuous.tendsto
    (IBMIntrinsicGraphDual.weakDerivative (intrinsicAverage T))).comp (derivative_tendsto T)
  have ht : IBMIntrinsicGraphDual.embed (averageGradient T) (IBMIntrinsicGraphDual.testOf v) =
      inner ℝ (averageGradient T) (v : JointFieldSpace) := by
    unfold IBMIntrinsicGraphDual.embed IBMIntrinsicGraphDual.testOf
    rw [ClosedOperatorGraphDualDerivative.embed_apply]
    rfl
  have hw : IBMIntrinsicGraphDual.weakDerivative (intrinsicAverage T)
      (IBMIntrinsicGraphDual.testOf v) = inner ℝ (averageGradient T) (v : JointFieldSpace) :=
    (congrArg (fun L => L (IBMIntrinsicGraphDual.testOf v)) (averageGradient_embed T).symm).trans ht
  have h' : Tendsto (fun n => IBMIntrinsicGraphDual.weakDerivative (intrinsicValue T n)
      (IBMIntrinsicGraphDual.testOf v)) atTop
      (𝓝 (inner ℝ (averageGradient T) (v : JointFieldSpace))) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, hw] using h
  exact h'.congr' (Eventually.of_forall he)

end OperatorDerivativeRewrite.Foundation.IBMRampSimpsonNativeAverage
