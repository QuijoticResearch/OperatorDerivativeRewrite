import Foundation.GaussianC2TimeWeighted

/-! Nonseparable finite-rank C1,2 Brownian Ito. Arbitrary C1,2 approximation
is a separate obligation; no finite-rank representation is assumed universally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianFiniteRankTimeIto
open InfiniteGaussian GaussianTimeProcess GaussianLipschitzIntegrands GaussianPredictableFull
open GaussianC2Ito GaussianTimeWeightedSmoothIto
open GaussianTimeProductL2 GaussianProductDerivative
variable {ι : Type*} [Fintype ι]

def function (a f : ι → ℝ → ℝ) (t x : ℝ) : ℝ := ∑ i, a i t*f i x

theorem time_hasDerivAt (a f : ι → ℝ → ℝ) (ha : ∀ i, ContDiff ℝ 1 (a i)) (t x : ℝ) :
    HasDerivAt (fun s => function a f s x) (∑ i, deriv (a i) t * f i x) t := by
  exact HasDerivAt.fun_sum (fun i _ => ((ha i).differentiable (by norm_num) t).hasDerivAt.mul_const _)

theorem space_hasDerivAt (a f : ι → ℝ → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (t x : ℝ) :
    HasDerivAt (function a f t) (∑ i, a i t * deriv (f i) x) x := by
  exact HasDerivAt.fun_sum (fun i _ => ((hf i).differentiable (by norm_num) x).hasDerivAt.const_mul _)

theorem second_space_hasDerivAt (a f : ι → ℝ → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (t x : ℝ) :
    HasDerivAt (deriv (function a f t)) (∑ i, a i t * deriv (deriv (f i)) x) x := by
  have he : deriv (function a f t) = fun y => ∑ i, a i t * deriv (f i) y :=
    funext fun y => (space_hasDerivAt a f hf t y).deriv
  rw [he]
  exact HasDerivAt.fun_sum (fun i _ => ((hf i).differentiable_deriv_two x).hasDerivAt.const_mul _)

variable (a f : ι → ℝ → ℝ) (ha : ∀ i, ContDiff ℝ 1 (a i)) (hf : ∀ i, ContDiff ℝ 2 (f i))
  (K0 K1 : ι → ℝ≥0) (h0 : ∀ i x, ‖deriv (f i) x‖₊ ≤ K0 i)
  (h1 : ∀ i x, ‖deriv (deriv (f i)) x‖₊ ≤ K1 i)

def value (T : ℝ≥0) : GaussianL2 :=
  ∑ i, a i T • valueL2 (functionLip (f i) (hf i) (K0 i) (h0 i)) T

def field (T : ℝ≥0) : fullPredictable :=
  ∑ i, weightedField (a i) (ha i).continuous (derivativeLip (f i) (hf i) (K1 i) (h1 i)) T

def generatorValue (t : ℝ) : GaussianL2 :=
  ∑ i, (deriv (a i) t • valueL2 (functionLip (f i) (hf i) (K0 i) (h0 i)) t.toNNReal +
    (1/2:ℝ) • (a i t • curvatureValue (f i) (hf i) (K1 i) (h1 i) t.toNNReal))

theorem value_coeFn (T : ℝ≥0) : value a f hf K0 h0 T =ᵐ[gaussianProduct]
    fun ω => function a f T (process T ω) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
    a i T • valueL2 (functionLip (f i) (hf i) (K0 i) (h0 i)) T),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i T) (valueL2 (functionLip (f i) (hf i) (K0 i) (h0 i)) T)),
    ae_all_iff.mpr (fun i => valueL2_coeFn (functionLip (f i) (hf i) (K0 i) (h0 i)) T)]
      with ω hs hm hv
  change value a f hf K0 h0 T ω = _ at hs
  rw [hs]
  simp only [function, Finset.sum_apply, hm, Pi.smul_apply, hv, smul_eq_mul]

theorem field_slices (T : ℝ≥0) : scalarCurry (field a f ha hf K1 h1 T : TimeProbabilityL2)
    =ᵐ[volume] (Ioc 0 (T:ℝ)).indicator (fun t =>
      ∑ i, a i t • valueL2 (derivativeLip (f i) (hf i) (K1 i) (h1 i)) t.toNNReal) := by
  have he : (field a f ha hf K1 h1 T : TimeProbabilityL2) =
      ∑ i, (weightedField (a i) (ha i).continuous
        (derivativeLip (f i) (hf i) (K1 i) (h1 i)) T : TimeProbabilityL2) :=
    map_sum fullPredictable.subtype _ _
  rw [he, map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => scalarCurry
    (weightedField (a i) (ha i).continuous (derivativeLip (f i) (hf i) (K1 i) (h1 i)) T)),
    ae_all_iff.mpr (fun i => weightedField_slices (a i) (ha i).continuous
      (derivativeLip (f i) (hf i) (K1 i) (h1 i)) T)] with t hs hv
  rw [hs]
  simp only [Finset.sum_apply, hv]
  by_cases ht : t ∈ Ioc 0 (T:ℝ) <;> simp [ht]

include ha in
theorem generator_coeFn (t : ℝ) : generatorValue a f hf K0 K1 h0 h1 t =ᵐ[gaussianProduct]
    fun ω => deriv (fun s => function a f s (process t.toNNReal ω)) t +
      (1/2:ℝ) * deriv (deriv (function a f t)) (process t.toNNReal ω) := by
  let V (i : ι) := valueL2 (functionLip (f i) (hf i) (K0 i) (h0 i)) t.toNNReal
  let C (i : ι) := curvatureValue (f i) (hf i) (K1 i) (h1 i) t.toNNReal
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => deriv (a i) t • V i + (1/2:ℝ) • (a i t • C i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_add (deriv (a i) t • V i) ((1/2:ℝ) • (a i t • C i))),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (deriv (a i) t) (V i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (1/2:ℝ) (a i t • C i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i t) (C i)),
    ae_all_iff.mpr (fun i => valueL2_coeFn (functionLip (f i) (hf i) (K0 i) (h0 i)) t.toNNReal),
    ae_all_iff.mpr (fun i => curvatureValue_coeFn (f i) (hf i) (K1 i) (h1 i) t.toNNReal)]
      with ω hs hadd hm hn hp hv hc
  change generatorValue a f hf K0 K1 h0 h1 t ω = _ at hs
  rw [hs, (time_hasDerivAt a f ha t (process t.toNNReal ω)).deriv,
    (second_space_hasDerivAt a f hf t (process t.toNNReal ω)).deriv]
  change ∀ i, V i ω = _ at hv
  change ∀ i, C i ω = _ at hc
  simp only [Finset.sum_apply, hadd, Pi.add_apply, hm, hn, hp, Pi.smul_apply,
    smul_eq_mul, hv, hc, Finset.sum_add_distrib, Finset.mul_sum]

include ha in
theorem generator_continuous : Continuous (generatorValue a f hf K0 K1 h0 h1) := by
  unfold generatorValue
  apply continuous_finsetSum
  intro i _
  exact (((ha i).continuous_deriv_one).smul
    ((valueL2_continuous (functionLip (f i) (hf i) (K0 i) (h0 i))).comp continuous_real_toNNReal)).add
    ((continuous_const : Continuous (fun _ : ℝ => (1/2:ℝ))).smul ((ha i).continuous.smul
      ((GaussianC2TimeWeighted.curvature_continuous (f i) (hf i) (K1 i) (h1 i)).comp continuous_real_toNNReal)))

/-- Genuine finite-rank time-dependent C1,2 Ito with actual partial derivatives,
actual J and an integrable Gaussian-L2 generator drift. -/
theorem finite_rank_ito (T : ℝ≥0) :
    value a f hf K0 h0 T - value a f hf K0 h0 0 =
      itoIntegral (field a f ha hf K1 h1 T) +
        ∫ t in 0..(T:ℝ), generatorValue a f hf K0 K1 h0 h1 t := by
  have hi (i : ι) : IntervalIntegrable (fun t : ℝ =>
      deriv (a i) t • valueL2 (functionLip (f i) (hf i) (K0 i) (h0 i)) t.toNNReal +
        (1/2:ℝ) • (a i t • curvatureValue (f i) (hf i) (K1 i) (h1 i) t.toNNReal)) volume 0 T :=
    ((((ha i).continuous_deriv_one).smul
      ((valueL2_continuous (functionLip (f i) (hf i) (K0 i) (h0 i))).comp continuous_real_toNNReal)).add
      ((continuous_const : Continuous (fun _ : ℝ => (1/2:ℝ))).smul ((ha i).continuous.smul
        ((GaussianC2TimeWeighted.curvature_continuous (f i) (hf i) (K1 i) (h1 i)).comp continuous_real_toNNReal)))).intervalIntegrable _ _
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ =>
    GaussianC2TimeWeighted.time_weighted_ito_combined (f i) (hf i) (K0 i) (K1 i)
      (h0 i) (h1 i) (a i) (ha i) T)
  simp only [value, field, generatorValue, map_sum, Finset.sum_sub_distrib, NNReal.coe_zero]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib] using h

/-- A concrete nonseparable time-space function in the finite-rank class. -/
theorem moving_sine_finite_rank (t x : ℝ) :
    function (fun i : Fin 2 => if i=0 then Real.sin else Real.cos)
      (fun i : Fin 2 => if i=0 then Real.cos else Real.sin) t x = Real.sin (t+x) := by
  simp [function, Fin.sum_univ_two, Real.sin_add]

end OperatorDerivativeRewrite.Foundation.GaussianFiniteRankTimeIto
