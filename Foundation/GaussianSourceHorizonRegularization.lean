import Foundation.GaussianHorizonChaosIntertwining
import Foundation.GaussianSourceClockIto
import Foundation.GaussianClockValueOperators

/-! Probability-chaos regularization on the ACTUAL source-valued predictable
horizon domain and its genuine stochastic-integral intertwining. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSourceHorizonRegularization
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto GaussianParameterizedIto
open GaussianSourceClockIto GaussianClockValueOperators GaussianHorizonChaosIntertwining
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
attribute [local instance] realPredictableL2_secondCountable predictableL2_secondCountable

def trimmedMap (T : ℝ≥0)
    (A : Lp ℝ 2 (predictableMeasure T) →L[ℝ] Lp ℝ 2 (predictableMeasure T)) :
    Lp GaussianL2 2 (predictableMeasure T) →L[ℝ] Lp GaussianL2 2 (predictableMeasure T) :=
  (ProductL2Curry.flip gaussianProduct (predictableMeasure T)).toContinuousLinearMap.comp
    ((A.compLpL 2 gaussianProduct).comp
      (ProductL2Curry.flip (predictableMeasure T) gaussianProduct).toContinuousLinearMap)

theorem trimmedMap_tensor (T : ℝ≥0)
    (A : Lp ℝ 2 (predictableMeasure T) →L[ℝ] Lp ℝ 2 (predictableMeasure T))
    (a : Lp ℝ 2 (predictableMeasure T)) (h : GaussianL2) :
    trimmedMap T A (BochnerClosedOperator.tensor (predictableMeasure T) a h) =
      BochnerClosedOperator.tensor (predictableMeasure T) (A a) h := by
  have hm : A.compLpL 2 gaussianProduct (BochnerClosedOperator.tensor gaussianProduct h a) =
      BochnerClosedOperator.tensor gaussianProduct h (A a) := by
    apply Lp.ext
    filter_upwards [A.coeFn_compLpL (BochnerClosedOperator.tensor gaussianProduct h a),
      BochnerClosedOperator.tensor_coeFn gaussianProduct h a,
      BochnerClosedOperator.tensor_coeFn gaussianProduct h (A a)] with ω hm ht ha
    rw [hm,ht,ha,map_smul]
  change ProductL2Curry.flip gaussianProduct (predictableMeasure T)
    (A.compLpL 2 gaussianProduct (ProductL2Curry.flip (predictableMeasure T) gaussianProduct
      (BochnerClosedOperator.tensor (predictableMeasure T) a h))) = _
  rw [ProductL2Curry.flip_tensor,hm,ProductL2Curry.flip_tensor]

/-- This acts on the predictable CLOCK class, preserving the full source
value space and the independently specified native predictable domain. -/
def mapPredictable (T : ℝ≥0)
    (A : Lp ℝ 2 (predictableMeasure T) →L[ℝ] Lp ℝ 2 (predictableMeasure T)) :
    Domain T →L[ℝ] Domain T :=
  (GaussianSourceClockIto.trimEquiv T).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((trimmedMap T A).comp (GaussianSourceClockIto.trimEquiv T).toLinearIsometry.toContinuousLinearMap)

theorem mapPredictable_tensor (T : ℝ≥0)
    (A : Lp ℝ 2 (predictableMeasure T) →L[ℝ] Lp ℝ 2 (predictableMeasure T))
    (a : Lp ℝ 2 (predictableMeasure T)) (h : GaussianL2) :
    mapPredictable T A (tensor T a h) = tensor T (A a) h := by
  apply (GaussianSourceClockIto.trimEquiv T).injective
  change GaussianSourceClockIto.trimEquiv T ((GaussianSourceClockIto.trimEquiv T).symm
    (trimmedMap T A (GaussianSourceClockIto.trimEquiv T
      ((GaussianSourceClockIto.trimEquiv T).symm _)))) =
        GaussianSourceClockIto.trimEquiv T ((GaussianSourceClockIto.trimEquiv T).symm _)
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact trimmedMap_tensor T A a h

theorem tested_tensor (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ)
    (a : Lp ℝ 2 (predictableMeasure T)) (h : GaussianL2) :
    L.compLpL 2 (predictableMeasure T) (BochnerClosedOperator.tensor (predictableMeasure T) a h) =
      L h • a := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (BochnerClosedOperator.tensor (predictableMeasure T) a h),
    BochnerClosedOperator.tensor_coeFn (predictableMeasure T) a h,Lp.coeFn_smul (L h) a]
    with z hL ht hs
  rw [hL,ht,hs,map_smul]
  exact mul_comm _ _

theorem trimmedMap_test (T : ℝ≥0)
    (A : Lp ℝ 2 (predictableMeasure T) →L[ℝ] Lp ℝ 2 (predictableMeasure T))
    (L : GaussianL2 →L[ℝ] ℝ) (u : Lp GaussianL2 2 (predictableMeasure T)) :
    L.compLpL 2 (predictableMeasure T) (trimmedMap T A u) =
      A (L.compLpL 2 (predictableMeasure T) u) := by
  have hh : ∀ v : Lp GaussianL2 2 (predictableMeasure T),
      L.compLpL 2 (predictableMeasure T) (trimmedMap T A v) =
        A (L.compLpL 2 (predictableMeasure T) v) := by
    apply Lp.induction (by simp) (fun v : Lp GaussianL2 2 (predictableMeasure T) =>
      L.compLpL 2 (predictableMeasure T) (trimmedMap T A v) =
        A (L.compLpL 2 (predictableMeasure T) v))
    · intro c s hs hfin
      change L.compLpL 2 (predictableMeasure T) (trimmedMap T A (indicatorConstLp 2 hs hfin.ne c)) =
        A (L.compLpL 2 (predictableMeasure T) (indicatorConstLp 2 hs hfin.ne c))
      have he : (indicatorConstLp 2 hs hfin.ne c : Lp GaussianL2 2 (predictableMeasure T)) =
          BochnerClosedOperator.tensor (predictableMeasure T)
            (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) c := by
        rw [indicatorConstLp_eq_toSpanSingleton_compLp]
        rfl
      simp only [he]
      rw [trimmedMap_tensor,tested_tensor,tested_tensor,map_smul]
    · intro f g hf hg hd hfc hgc
      simp only [map_add,hfc,hgc]
    · exact isClosed_eq
        ((L.compLpL 2 (predictableMeasure T)).continuous.comp (trimmedMap T A).continuous)
        (A.continuous.comp (L.compLpL 2 (predictableMeasure T)).continuous)
  exact hh u

theorem mapPredictable_test (T : ℝ≥0)
    (A : Lp ℝ 2 (predictableMeasure T) →L[ℝ] Lp ℝ 2 (predictableMeasure T))
    (L : GaussianL2 →L[ℝ] ℝ) (u : Domain T) :
    L.compLpL 2 (predictableMeasure T) (GaussianSourceClockIto.trimEquiv T (mapPredictable T A u)) =
      A (L.compLpL 2 (predictableMeasure T) (GaussianSourceClockIto.trimEquiv T u)) := by
  change L.compLpL 2 (predictableMeasure T) (GaussianSourceClockIto.trimEquiv T
    ((GaussianSourceClockIto.trimEquiv T).symm
      (trimmedMap T A (GaussianSourceClockIto.trimEquiv T u)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact trimmedMap_test T A L _

/-- Scalar intertwining lifts to the genuine source-valued stochastic
integral, on its WHOLE predictable horizon domain. -/
theorem integral_intertwining (T : ℝ≥0)
    (A : Lp ℝ 2 (predictableMeasure T) →L[ℝ] Lp ℝ 2 (predictableMeasure T))
    (B : GaussianL2 →L[ℝ] GaussianL2)
    (hAB : ∀ a, realIto T (A a) = B (realIto T a)) (u : Domain T) :
    integral T (mapPredictable T A u) = clockLift B (integral T u) := by
  have h : ∀ v : Lp GaussianL2 2 (predictableMeasure T),
      realIntegral gaussianProduct T (trimmedMap T A v) =
        clockLift B (realIntegral gaussianProduct T v) := by
    apply Lp.induction (by simp) (fun v : Lp GaussianL2 2 (predictableMeasure T) =>
      realIntegral gaussianProduct T (trimmedMap T A v) =
        clockLift B (realIntegral gaussianProduct T v))
    · intro c s hs hfin
      change realIntegral gaussianProduct T (trimmedMap T A (indicatorConstLp 2 hs hfin.ne c)) =
        clockLift B (realIntegral gaussianProduct T (indicatorConstLp 2 hs hfin.ne c))
      have he : (indicatorConstLp 2 hs hfin.ne c : Lp GaussianL2 2 (predictableMeasure T)) =
          BochnerClosedOperator.tensor (predictableMeasure T)
            (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) c := by
        rw [indicatorConstLp_eq_toSpanSingleton_compLp]
        rfl
      simp only [he]
      rw [trimmedMap_tensor,realIntegral_tensor,realIntegral_tensor,clockLift_tensor,hAB]
    · intro f g hf hg hd hfc hgc
      simp only [map_add,hfc,hgc]
    · exact isClosed_eq
        ((realIntegral gaussianProduct T).continuous.comp (trimmedMap T A).continuous)
        ((clockLift B).continuous.comp (realIntegral gaussianProduct T).continuous)
  change realIntegral gaussianProduct T (GaussianSourceClockIto.trimEquiv T
    ((GaussianSourceClockIto.trimEquiv T).symm
      (trimmedMap T A (GaussianSourceClockIto.trimEquiv T u)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact h _

def sourceProjection (n : ℕ) (T : ℝ≥0) : Domain T →L[ℝ] Domain T :=
  mapPredictable T (realProjection n T)

theorem integral_sourceProjection (n : ℕ) (T : ℝ≥0) (u : Domain T) :
    integral T (sourceProjection n T u) =
      clockLift (GaussianNumberSectors.projection (n + 1)) (integral T u) :=
  integral_intertwining T _ _ (integral_realProjection n T) u

def sourceRegularization (T : ℝ≥0) : Domain T →L[ℝ] Domain T :=
  mapPredictable T (realRegularization T)

/-- A genuine stochastic identity in full joint SOURCE/CLOCK L2. -/
theorem integral_sourceRegularization (T : ℝ≥0) (u : Domain T) :
    integral T (sourceRegularization T u) =
      clockLift GaussianInverseNumberPotential.potentialOperator (integral T u) :=
  integral_intertwining T _ _ (integral_realRegularization T) u

theorem potential_clock_projection (k : ℕ) (f : Field) :
    clockLift (GaussianNumberSectors.projection k)
      (clockLift GaussianInverseNumberPotential.potentialOperator f) =
        (k : ℝ)⁻¹ • clockLift (GaussianNumberSectors.projection k) f := by
  apply eq_of_all_tests
  intro L
  rw [clockLift_test,clockLift_test,map_smul,clockLift_test]
  exact GaussianPotentialIteration.projection_potential k _

theorem potential_clock_partial_sum (N : ℕ) (f : Field) :
    (∑ k ∈ Finset.range (N + 1), (k + 1 : ℝ)⁻¹ •
      clockLift (GaussianNumberSectors.projection (k + 1)) f) =
        clockLift (GaussianNumberSectors.truncation (N + 1))
          (clockLift GaussianInverseNumberPotential.potentialOperator f) := by
  rw [clock_truncation_eq]
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [potential_clock_projection,Nat.cast_zero,inv_zero,zero_smul,add_zero,
    Nat.cast_add,Nat.cast_one]

/-- Strong convergence in the ORIGINAL source-valued predictable horizon
domain, not merely its terminal integral or individual probability slices. -/
theorem sourceRegularization_chaos_tendsto (T : ℝ≥0) (u : Domain T) :
    Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
      (k + 1 : ℝ)⁻¹ • sourceProjection k T u) atTop (𝓝 (sourceRegularization T u)) := by
  have hs := (clock_truncation_tendsto
    (clockLift GaussianInverseNumberPotential.potentialOperator (integral T u))).comp
      (tendsto_add_atTop_nat 1)
  apply (GaussianSourceClockIto.integral T).isometry.tendsto_nhds_iff.mpr
  have he (N : ℕ) : integral T
      (∑ k ∈ Finset.range (N + 1), (k + 1 : ℝ)⁻¹ • sourceProjection k T u) =
        clockLift (GaussianNumberSectors.truncation (N + 1))
          (clockLift GaussianInverseNumberPotential.potentialOperator (integral T u)) := by
    rw [map_sum]
    simp only [map_smul,integral_sourceProjection]
    exact potential_clock_partial_sum N _
  simpa only [Function.comp_def,he,integral_sourceRegularization] using hs

theorem realIto_projection_zero (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) :
    GaussianNumberSectors.projection 0 (realIto T a) = 0 := by
  rw [GaussianNumberSectors.projection_zero,gaussianOne_inner_eq_integral]
  have hm := GaussianPredictableHorizon.itoIntegral_centered T
    ((GaussianComplexHorizonIto.trimEquiv T).symm a)
  change (∫ ω, realIto T a ω ∂gaussianProduct) = 0 at hm
  rw [hm,zero_smul]

theorem integral_clock_centered (T : ℝ≥0) (u : Domain T) :
    clockLift (GaussianNumberSectors.projection 0) (integral T u) = 0 := by
  apply eq_of_all_tests
  intro L
  rw [clockLift_test,map_zero,GaussianSourceClockIto.native_scalarization,realIto_projection_zero]

end OperatorDerivativeRewrite.Foundation.GaussianSourceHorizonRegularization
