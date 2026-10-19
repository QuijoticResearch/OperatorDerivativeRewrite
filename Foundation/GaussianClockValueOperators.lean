import Foundation.ProductL2Flip
import Foundation.GaussianDirectionalRecovery
import Foundation.GaussianPredictableChaosCore
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Clock operators on actual source-valued Gaussian L2, with precise
factor order and naturality under arbitrary continuous source tests. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianClockValueOperators
open InfiniteGaussian
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

/-- Outer factor CLOCK, value space SOURCE. The operator A acts on CLOCK. -/
abbrev Field := Lp GaussianL2 2 gaussianProduct

def clockLift (A : GaussianL2 →L[ℝ] GaussianL2) : Field →L[ℝ] Field :=
  (ProductL2Curry.flip gaussianProduct gaussianProduct).toContinuousLinearMap.comp
    ((A.compLpL 2 gaussianProduct).comp
      (ProductL2Curry.flip gaussianProduct gaussianProduct).toContinuousLinearMap)

theorem map_tensor (A : GaussianL2 →L[ℝ] GaussianL2) (a v : GaussianL2) :
    A.compLpL 2 gaussianProduct (BochnerClosedOperator.tensor gaussianProduct a v) =
      BochnerClosedOperator.tensor gaussianProduct a (A v) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (BochnerClosedOperator.tensor gaussianProduct a v),
    BochnerClosedOperator.tensor_coeFn gaussianProduct a v,
    BochnerClosedOperator.tensor_coeFn gaussianProduct a (A v)] with ω hm ht hv
  rw [hm,ht,hv,map_smul]

theorem clockLift_tensor (A : GaussianL2 →L[ℝ] GaussianL2) (a v : GaussianL2) :
    clockLift A (BochnerClosedOperator.tensor gaussianProduct a v) =
      BochnerClosedOperator.tensor gaussianProduct (A a) v := by
  change ProductL2Curry.flip gaussianProduct gaussianProduct
    (A.compLpL 2 gaussianProduct (ProductL2Curry.flip gaussianProduct gaussianProduct
      (BochnerClosedOperator.tensor gaussianProduct a v))) = _
  rw [ProductL2Curry.flip_tensor,map_tensor,ProductL2Curry.flip_tensor]

theorem test_tensor (L : GaussianL2 →L[ℝ] ℝ) (a v : GaussianL2) :
    L.compLpL 2 gaussianProduct (BochnerClosedOperator.tensor gaussianProduct a v) = L v • a := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (BochnerClosedOperator.tensor gaussianProduct a v),
    BochnerClosedOperator.tensor_coeFn gaussianProduct a v,Lp.coeFn_smul (L v) a]
    with ω hL ht hs
  rw [hL,ht,hs,map_smul]
  exact mul_comm _ _

/-- Equality on the whole Bochner L2 space, proved from actual tensor density.
No joint representative of arbitrary nested L2 classes is presumed. -/
theorem clockLift_test (A : GaussianL2 →L[ℝ] GaussianL2) (L : GaussianL2 →L[ℝ] ℝ)
    (f : Field) :
    L.compLpL 2 gaussianProduct (clockLift A f) = A (L.compLpL 2 gaussianProduct f) := by
  have h : ∀ f : Field,
      L.compLpL 2 gaussianProduct (clockLift A f) = A (L.compLpL 2 gaussianProduct f) := by
    apply Lp.induction (by simp) (fun f : Field =>
      L.compLpL 2 gaussianProduct (clockLift A f) = A (L.compLpL 2 gaussianProduct f))
    · intro v s hs hfin
      change L.compLpL 2 gaussianProduct (clockLift A (indicatorConstLp 2 hs hfin.ne v)) =
        A (L.compLpL 2 gaussianProduct (indicatorConstLp 2 hs hfin.ne v))
      have he : (indicatorConstLp 2 hs hfin.ne v : Field) =
          BochnerClosedOperator.tensor gaussianProduct (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) v := by
        rw [indicatorConstLp_eq_toSpanSingleton_compLp]
        rfl
      simp only [he]
      rw [clockLift_tensor,test_tensor,test_tensor,map_smul]
    · intro f g hf hg hd hfc hgc
      simp only [map_add,hfc,hgc]
    · exact isClosed_eq
        ((L.compLpL 2 gaussianProduct).continuous.comp (clockLift A).continuous)
        (A.continuous.comp (L.compLpL 2 gaussianProduct).continuous)
  exact h f

theorem eq_of_all_tests {f g : Field}
    (h : ∀ L : GaussianL2 →L[ℝ] ℝ,
      L.compLpL 2 gaussianProduct f = L.compLpL 2 gaussianProduct g) : f = g := by
  have hz : (fun ω => f ω - g ω) =ᵐ[gaussianProduct] 0 := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    filter_upwards [L.coeFn_compLpL f,L.coeFn_compLpL g] with ω hf hg
    change L (f ω - g ω) = 0
    rw [map_sub,← hf,← hg,h L,sub_self]
  apply Lp.ext
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

theorem eq_of_clock_projections {f g : Field}
    (h : ∀ k : ℕ, clockLift (GaussianNumberSectors.projection k) f =
      clockLift (GaussianNumberSectors.projection k) g) : f = g := by
  apply eq_of_all_tests
  intro L
  have hp (k : ℕ) : GaussianNumberSectors.projection k (L.compLpL 2 gaussianProduct f) =
      GaussianNumberSectors.projection k (L.compLpL 2 gaussianProduct g) := by
    have he := congrArg (L.compLpL 2 gaussianProduct) (h k)
    simpa only [clockLift_test] using he
  exact (GaussianNumberSectors.projection_hasSum (L.compLpL 2 gaussianProduct f)).unique
    (by simpa only [hp] using
      GaussianNumberSectors.projection_hasSum (L.compLpL 2 gaussianProduct g))

theorem clockLift_norm_le (A : GaussianL2 →L[ℝ] GaussianL2) (f : Field) :
    ‖clockLift A f‖ ≤ ‖A‖ * ‖f‖ := by
  change ‖ProductL2Curry.flip gaussianProduct gaussianProduct
    (A.compLpL 2 gaussianProduct (ProductL2Curry.flip gaussianProduct gaussianProduct f))‖ ≤ _
  rw [LinearIsometry.norm_map]
  exact (A.norm_compLp_le _).trans_eq (by rw [LinearIsometry.norm_map])

theorem clockRecovery_norm_le (v : CoefficientSpace) (f : Field) :
    ‖clockLift (GaussianDirectionalRecovery.directionalRecovery v) f‖ ≤ ‖v‖ * ‖f‖ := by
  change ‖ProductL2Curry.flip gaussianProduct gaussianProduct
    ((GaussianDirectionalRecovery.directionalRecovery v).compLpL 2 gaussianProduct
      (ProductL2Curry.flip gaussianProduct gaussianProduct f))‖ ≤ _
  rw [LinearIsometry.norm_map]
  have h : ‖(GaussianDirectionalRecovery.directionalRecovery v).compLpL 2 gaussianProduct
      (ProductL2Curry.flip gaussianProduct gaussianProduct f)‖ ≤
      ‖v‖ * ‖ProductL2Curry.flip gaussianProduct gaussianProduct f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(GaussianDirectionalRecovery.directionalRecovery v).coeFn_compLpL
      (ProductL2Curry.flip gaussianProduct gaussianProduct f)] with ω hω
    rw [hω]
    exact GaussianDirectionalRecovery.directionalRecovery_norm_le v _
  simpa only [LinearIsometry.norm_map] using h

theorem flip_involutive (f : Field) :
    ProductL2Curry.flip gaussianProduct gaussianProduct
      (ProductL2Curry.flip gaussianProduct gaussianProduct f) = f := by
  have hi : (ContinuousLinearMap.id ℝ GaussianL2).compLpL 2 gaussianProduct
      (ProductL2Curry.flip gaussianProduct gaussianProduct f) =
      ProductL2Curry.flip gaussianProduct gaussianProduct f := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.id ℝ GaussianL2).coeFn_compLpL
      (ProductL2Curry.flip gaussianProduct gaussianProduct f)] with ω hω
    exact hω
  have hh : clockLift (ContinuousLinearMap.id ℝ GaussianL2) f = f := by
    apply eq_of_all_tests
    intro L
    rw [clockLift_test]
    rfl
  change ProductL2Curry.flip gaussianProduct gaussianProduct
    ((ContinuousLinearMap.id ℝ GaussianL2).compLpL 2 gaussianProduct
      (ProductL2Curry.flip gaussianProduct gaussianProduct f)) = f at hh
  rwa [hi] at hh

/-- Strong joint-L2 chaos completeness with the source randomness retained. -/
theorem clock_truncation_tendsto (f : Field) :
    Filter.Tendsto (fun N => clockLift (GaussianNumberSectors.truncation N) f)
      Filter.atTop (𝓝 f) := by
  let F := ProductL2Curry.flip gaussianProduct gaussianProduct
  have hs : Filter.Tendsto
      (fun N => (GaussianNumberSectors.truncation N).compLpL 2 gaussianProduct (F f))
      Filter.atTop (𝓝 (F f)) := by
    apply BochnerL2Dominated.tendsto_of_ae_norm_bound
    · intro N
      filter_upwards [(GaussianNumberSectors.truncation N).coeFn_compLpL (F f)] with ω hω
      rw [hω]
      exact GaussianPredictableChaosCore.scalar_truncation_norm_le N _
    · filter_upwards [ae_all_iff.mpr (fun N =>
        (GaussianNumberSectors.truncation N).coeFn_compLpL (F f))] with ω hω
      simp only [hω]
      exact GaussianNumberSectors.truncation_tendsto _
  have hh := F.continuous.tendsto (F f) |>.comp hs
  change Filter.Tendsto (fun N => clockLift (GaussianNumberSectors.truncation N) f)
    Filter.atTop (𝓝 (F (F f))) at hh
  simpa only [F,flip_involutive] using hh

theorem clockLift_sum (s : Finset ℕ) (A : ℕ → GaussianL2 →L[ℝ] GaussianL2) (f : Field) :
    clockLift (∑ k ∈ s, A k) f = ∑ k ∈ s, clockLift (A k) f := by
  apply eq_of_all_tests
  intro L
  rw [clockLift_test,map_sum]
  simp only [ContinuousLinearMap.sum_apply,map_sum,clockLift_test]

theorem clock_truncation_eq (N : ℕ) (f : Field) :
    clockLift (GaussianNumberSectors.truncation N) f =
      ∑ k ∈ Finset.range (N + 1), clockLift (GaussianNumberSectors.projection k) f := by
  rw [GaussianNumberSectors.truncation,clockLift_sum]

end OperatorDerivativeRewrite.Foundation.GaussianClockValueOperators
