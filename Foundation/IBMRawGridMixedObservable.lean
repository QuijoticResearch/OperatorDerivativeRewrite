import Foundation.IBMClippedClockCovariation

/-! Exact mixed actual IBM observable tests of the ORIGINAL native grid.
The observable projection is removed only inside its legitimate pairing. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawGridMixedObservable
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMRawStepSources IBMRawStepCompensation IBMRawGridCompensation IBMRawGridSecondChaos
open IBMRawGridObservableTests IBMUniformClockGridEnergy GaussianTimeSpaceHermite
open IBMQuarticSecondChaos IBMSourceProductBounds IBMSchwartzSourceContinuity
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _ IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] jointDerivative LinearPMap.adjoint LinearPMap.graph

def mixedObservation (R S : ℝ≥0) : IntrinsicSpace := rawObservable R S+squareObservation R

theorem mixedObservation_actual (R S : ℝ≥0) :
    (mixedObservation R S : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => IBMConstructedSources.ibmValue R p*IBMConstructedSources.ibmValue S p := by
  filter_upwards [Lp.coeFn_add (rawStep R S) (squareObservation R : JointL2),
    raw_actual R S,squareObservation_actual R] with p ha hr hs
  change (mixedObservation R S : JointL2) p = _ at ha
  rw [ha,Pi.add_apply,hr,hs]
  unfold rawFunction
  ring

theorem mixedObservation_memLp (R S : ℝ≥0) :
    MemLp (fun p => IBMConstructedSources.ibmValue R p*IBMConstructedSources.ibmValue S p)
      2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (mixedObservation R S : JointL2)).ae_eq (mixedObservation_actual R S)

def mixedSource (R S : ℝ≥0) : ValueSpace := rawSource R S-rawSource R 0

theorem mixedObservation_realization (R S : ℝ≥0) :
    (mixedObservation R S : JointL2) = jointRealization (mixedSource R S) := by
  change jointRealization (rawSource R S)+(-jointRealization (rawSource R 0)) = _
  rw [mixedSource,map_sub]
  abel

theorem mixedSource_actual (R S : ℝ≥0) :
    mixedSource R S =ᵐ[gaussianProduct] fun Y => rawProduct (clockDirection R Y) (clockDirection S Y) := by
  filter_upwards [Lp.coeFn_sub (rawSource R S) (rawSource R 0),
    (raw_memLp R S).coeFn_toLp,(raw_memLp R 0).coeFn_toLp,clockCurve_initial 1] with Y ha hr hz h0
  have hd0 : clockDirection 0 Y = 0 := by simpa only [clockCurve,grid,Nat.cast_zero,mul_zero] using h0
  change mixedSource R S Y = _ at ha
  rw [ha,Pi.sub_apply]
  change rawSource R S Y = rawSections R S Y at hr
  change rawSource R 0 Y = rawSections R 0 Y at hz
  rw [hr,hz]
  change rawBilinear (clockDirection S Y-clockDirection R Y) (clockDirection R Y)-
    rawBilinear (clockDirection 0 Y-clockDirection R Y) (clockDirection R Y) = _
  rw [hd0]
  simp only [map_sub,ContinuousLinearMap.sub_apply,zero_sub,map_neg,ContinuousLinearMap.neg_apply]
  simp only [rawBilinear_apply]
  rw [rawProduct_comm (clockDirection S Y) (clockDirection R Y)]
  abel

theorem mixed_telescope (a b : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ((a (i+1)-a i)*b i+(b (i+1)-b i)*a i)) =
      a n*b n-a 0*b 0-∑ i ∈ Finset.range n, (a (i+1)-a i)*(b (i+1)-b i) := by
  calc
    _ = ∑ i ∈ Finset.range n,
        (a (i+1)*b (i+1)-a i*b i-(a (i+1)-a i)*(b (i+1)-b i)) :=
      Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_range_sub (fun i => a i*b i) n]

theorem source_mixed_test (u : ℕ → CoefficientSpace) (n : ℕ) (a b : CoefficientSpace) :
    inner ℝ (sourceSum u n) (rawProduct a b) =
      inner ℝ (u n) a*inner ℝ (u n) b-inner ℝ (u 0) a*inner ℝ (u 0) b-
        ∑ i ∈ Finset.range n, (inner ℝ (u (i+1)) a-inner ℝ (u i) a)*
          (inner ℝ (u (i+1)) b-inner ℝ (u i) b) := by
  rw [rawProduct_eq_cross,inner_add_right,inner_smul_right,source_mean_zero,mul_zero,add_zero]
  simp only [sourceSum,sum_inner,cross_inner,increment,inner_sub_left]
  exact mixed_telescope (fun i => inner ℝ (u i) a) (fun i => inner ℝ (u i) b) n

def mixedSquares (h : ℝ≥0) (n : ℕ) (R S : ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∑ i ∈ Finset.range n, (overlap R Y (grid h (i+1))-overlap R Y (grid h i))*
    (overlap S Y (grid h (i+1))-overlap S Y (grid h i))

def mixedEnergy (h : ℝ≥0) (n : ℕ) (R S : ℝ≥0) (Y : SampleSpace) : ℝ :=
  overlap R Y (grid h n)*overlap S Y (grid h n)-mixedSquares h n R S Y

theorem source_mixed_pairing_ae (h : ℝ≥0) (n : ℕ) (R S : ℝ≥0) :
    (fun Y => inner ℝ (sourceGrid h n Y) (mixedSource R S Y)) =ᵐ[gaussianProduct] mixedEnergy h n R S := by
  filter_upwards [sourceGrid_ae h n,mixedSource_actual R S,clockCurve_initial h] with Y hs hm h0
  rw [hs,hm,source_mixed_test,h0,inner_zero_left,inner_zero_left,zero_mul,sub_zero]
  simp only [clockCurve,direction_overlap]
  rfl

theorem mixedEnergy_integrable (h : ℝ≥0) (n : ℕ) (R S : ℝ≥0) :
    Integrable (mixedEnergy h n R S) gaussianProduct :=
  (L2.integrable_inner (sourceGrid h n) (mixedSource R S)).congr (source_mixed_pairing_ae h n R S)

theorem observable_mixed_pairing (h : ℝ≥0) (n : ℕ) (R S : ℝ≥0) :
    inner ℝ (jointDivergence (gridInput h n)) (mixedObservation R S) =
      ∫ Y, mixedEnergy h n R S Y ∂gaussianProduct := by
  rw [native_grid_value]
  have hp := IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    (mixedObservation R S) (jointRealization (sourceGrid h n))
  rw [hp]
  change inner ℝ (jointRealization (sourceGrid h n)) (mixedObservation R S : JointL2) = _
  rw [mixedObservation_realization,jointRealization.inner_map_map,L2_inner_eq_integral]
  exact integral_congr_ae (source_mixed_pairing_ae h n R S)

end OperatorDerivativeRewrite.Foundation.IBMRawGridMixedObservable
