import Foundation.FiniteCovarianceHessian

/-! Genuine first and second derivative fields for arbitrary bounded-derivative
C2 stopped-coordinate cylinders. This constructs the terms and proves their
approximations; the stochastic change-of-variables identity is not assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianStoppedSmoothFields
open InfiniteGaussian GaussianTimeProcess GaussianStoppedComposition FiniteCovarianceHessian
open GaussianContinuousIntegrands GaussianPredictableFull GaussianTimeProductL2
open GaussianProductDerivative GaussianBrownianQuadraticVariation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 2 Φ) (K0 K1 : ℝ≥0)
  (h0 : ∀ x, ‖fderiv ℝ Φ x‖₊ ≤ K0) (h1 : ∀ x, ‖hessian Φ x‖₊ ≤ K1)
  (r : ι → ℝ≥0)

include hΦ h0 in
theorem functionLip : LipschitzWith K0 Φ :=
  lipschitzWith_of_nnnorm_fderiv_le (hΦ.differentiable (by norm_num)) h0

def gradientValue (i : ι) (t : ℝ≥0) : GaussianL2 :=
  boundedValue (partial_contDiff_one Φ hΦ i).continuous
    (partial_bound Φ (M := K0) (fun x => h0 x) i) r t

def hessianValue (i j : ι) (t : ℝ≥0) : GaussianL2 :=
  boundedValue (mixedPartial_continuous Φ hΦ i j)
    (mixedPartial_bound Φ (M := K1) (fun x => h1 x) i j) r t

theorem gradientValue_coeFn (i : ι) (t : ℝ≥0) :
    gradientValue Φ hΦ K0 h0 r i t =ᵐ[gaussianProduct]
      fun ω => partialDerivative Φ i (coordinates r t ω) := boundedValue_coeFn _ _ _ _

theorem hessianValue_coeFn (i j : ι) (t : ℝ≥0) :
    hessianValue Φ hΦ K1 h1 r i j t =ᵐ[gaussianProduct]
      fun ω => mixedPartial Φ i j (coordinates r t ω) := boundedValue_coeFn _ _ _ _

theorem gradientValue_continuous (i : ι) : Continuous (gradientValue Φ hΦ K0 h0 r i) :=
  boundedValue_continuous (partial_contDiff_one Φ hΦ i).continuous
    (partial_bound Φ (M := K0) (fun x => h0 x) i) r

theorem hessianValue_continuous (i j : ι) : Continuous (hessianValue Φ hΦ K1 h1 r i j) :=
  boundedValue_continuous (mixedPartial_continuous Φ hΦ i j)
    (mixedPartial_bound Φ (M := K1) (fun x => h1 x) i j) r

theorem gradientValue_past (i : ι) (t : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration t] (gradientValue Φ hΦ K0 h0 r i t) gaussianProduct :=
  boundedValue_past _ _ _ _

theorem hessianValue_intervalIntegrable (i j : ι) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => hessianValue Φ hΦ K1 h1 r i j t.toNNReal) volume a b :=
  ((hessianValue_continuous Φ hΦ K1 h1 r i j).comp continuous_real_toNNReal).intervalIntegrable a b

/-- Existing predictable-domain element with each coordinate's actual lifetime. -/
def gradientField (T : ℝ≥0) : fullPredictable :=
  ∑ i, predictableField (gradientValue Φ hΦ K0 h0 r i)
    (gradientValue_continuous Φ hΦ K0 h0 r i) (gradientValue_past Φ hΦ K0 h0 r i) (min T (r i))

/-- Actual integrable Hessian drift, defined before any Ito identity. -/
def hessianDrift (T : ℝ≥0) : GaussianL2 :=
  (1/2:ℝ) • ∑ i, ∑ j,
    ∫ t in 0..((min T (min (r i) (r j)) : ℝ≥0):ℝ), hessianValue Φ hΦ K1 h1 r i j t.toNNReal

theorem gradientField_slices (T : ℝ≥0) :
    scalarCurry (gradientField Φ hΦ K0 h0 r T : TimeProbabilityL2) =ᵐ[volume]
      fun t => ∑ i, (Ioc 0 ((min T (r i) : ℝ≥0):ℝ)).indicator
        (fun s => gradientValue Φ hΦ K0 h0 r i s.toNNReal) t := by
  let U (i : ι) := predictableField (gradientValue Φ hΦ K0 h0 r i)
    (gradientValue_continuous Φ hΦ K0 h0 r i) (gradientValue_past Φ hΦ K0 h0 r i) (min T (r i))
  have he : (gradientField Φ hΦ K0 h0 r T : TimeProbabilityL2) = ∑ i, (U i : TimeProbabilityL2) :=
    map_sum fullPredictable.subtype _ _
  rw [he, map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => scalarCurry (U i : TimeProbabilityL2)),
    ae_all_iff.mpr (fun i => runningField_slices (gradientValue Φ hΦ K0 h0 r i)
      (gradientValue_continuous Φ hΦ K0 h0 r i) (min T (r i)))] with t hs hi
  rw [hs]
  simp only [Finset.sum_apply, U, predictableField, hi, horizonValue]

theorem gradient_steps_tendsto (T : ℝ≥0) :
    Tendsto (fun N => ∑ i, itoIntegral (predictableStep (gradientValue Φ hΦ K0 h0 r i)
      (gradientValue_past Φ hΦ K0 h0 r i) (min T (r i)) N)) atTop
      (𝓝 (itoIntegral (gradientField Φ hΦ K0 h0 r T))) := by
  simp only [gradientField, map_sum]
  exact tendsto_finsetSum Finset.univ (fun i _ => integral_step_tendsto _
    (gradientValue_continuous Φ hΦ K0 h0 r i) _ _)

theorem hessian_steps_tendsto (T : ℝ≥0) :
    Tendsto (fun N => (1/2:ℝ) • ∑ i, ∑ j, ∑ k : Fin (N+1),
      ((uniformTime (min T (min (r i) (r j))) N k.succ : ℝ) -
        uniformTime (min T (min (r i) (r j))) N k.castSucc) •
      hessianValue Φ hΦ K1 h1 r i j (uniformTime (min T (min (r i) (r j))) N k.castSucc))
      atTop (𝓝 (hessianDrift Φ hΦ K1 h1 r T)) := by
  apply Filter.Tendsto.const_smul
  apply tendsto_finsetSum Finset.univ
  intro i _
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact drift_sum_tendsto _ (hessianValue_continuous Φ hΦ K1 h1 r i j) _

/-- Strict stopping indicators give the same field: finitely many deterministic
endpoints are null for Lebesgue measure. -/
theorem gradientField_slices_strict (T : ℝ≥0) :
    scalarCurry (gradientField Φ hΦ K0 h0 r T : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T:ℝ)).indicator (fun t => ∑ i,
        if t < (r i:ℝ) then gradientValue Φ hΦ K0 h0 r i t.toNNReal else 0) := by
  filter_upwards [gradientField_slices Φ hΦ K0 h0 r T,
    ae_all_iff.mpr (fun i => (volume : Measure ℝ).ae_ne (r i : ℝ))] with t ht hn
  rw [ht]
  by_cases hT : t ∈ Ioc 0 (T:ℝ)
  · rw [indicator_of_mem hT]
    apply Finset.sum_congr rfl
    intro i _
    have he : t ≤ (r i:ℝ) ↔ t < (r i:ℝ) :=
      ⟨fun h => lt_of_le_of_ne h (hn i), le_of_lt⟩
    by_cases hr : t < (r i:ℝ) <;>
      simp [mem_Ioc, NNReal.coe_min, le_min_iff, hT.1, hT.2, he, hr]
  · rw [indicator_of_notMem hT]
    apply Finset.sum_eq_zero
    intro i _
    apply indicator_of_notMem
    intro h
    apply hT
    exact ⟨h.1, h.2.trans (min_le_left _ _)⟩
end OperatorDerivativeRewrite.Foundation.GaussianStoppedSmoothFields
