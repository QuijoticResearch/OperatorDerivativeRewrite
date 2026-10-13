import Foundation.GaussianBoundedContinuity
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! Genuine nonlinear functions of finitely many stopped Brownian coordinates.
The vector and composition classes are defined before their continuity and
predictability are proved. No stochastic change-of-variables formula is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianStoppedComposition
open InfiniteGaussian GaussianTimeProcess GaussianLipschitzIntegrands
open GaussianContinuousIntegrands GaussianPredictableFull GaussianTimeProductL2
open GaussianProductDerivative GaussianBrownianQuadraticVariation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual stopped observations, with no covariance nondegeneracy requirement. -/
def coordinates (r : ι → ℝ≥0) (t : ℝ≥0) (ω : SampleSpace) : ι → ℝ :=
  fun i => process (min t (r i)) ω

def vector (r : ι → ℝ≥0) (t : ℝ≥0) : Lp (ι → ℝ) 2 gaussianProduct :=
  ∑ i, (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLp (wienerL2 (min t (r i)))

theorem vector_coeFn (r : ι → ℝ≥0) (t : ℝ≥0) :
    vector r t =ᵐ[gaussianProduct] coordinates r t := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
    (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLp (wienerL2 (min t (r i)))),
    ae_all_iff.mpr (fun i => (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).coeFn_compLp
      (wienerL2 (min t (r i))))] with ω hs hi
  change (vector r t) ω = _ at hs
  rw [hs]
  simp only [Finset.sum_apply, hi, ContinuousLinearMap.single_apply]
  exact Finset.univ_sum_single _

theorem vector_continuous (r : ι → ℝ≥0) : Continuous (vector r) := by
  apply continuous_finsetSum
  intro i _
  exact ((ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLpL 2 gaussianProduct).continuous.comp
    (wienerL2_continuous.comp (continuous_id.min continuous_const))

theorem coordinates_stronglyMeasurable (r : ι → ℝ≥0) (t : ℝ≥0) :
    StronglyMeasurable (coordinates r t) :=
  (Measurable.of_eval (fun i => (process_stronglyMeasurable (min t (r i))).measurable)).stronglyMeasurable

theorem coordinates_past (r : ι → ℝ≥0) (t : ℝ≥0) :
    StronglyMeasurable[naturalFiltration t] (coordinates r t) :=
  by
    letI : MeasurableSpace SampleSpace := naturalFiltration t
    apply Measurable.stronglyMeasurable
    exact Measurable.of_eval (fun i => ((process_stronglyAdapted (min t (r i))).mono
      (naturalFiltration.mono (min_le_left _ _))).measurable)

theorem coordinates_memLp (r : ι → ℝ≥0) (t : ℝ≥0) :
    MemLp (coordinates r t) 2 gaussianProduct :=
  (Lp.memLp _).ae_eq (vector_coeFn r t)

variable {Φ : (ι → ℝ) → ℝ} {K : ℝ≥0}

omit [DecidableEq ι] in
theorem centered_lipschitz (hΦ : LipschitzWith K Φ) :
    LipschitzWith K (fun x => Φ x - Φ 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hΦ.dist_le_mul x y

def value (hΦ : LipschitzWith K Φ) (r : ι → ℝ≥0) (t : ℝ≥0) : GaussianL2 :=
  (centered_lipschitz hΦ).compLp (sub_self _) (vector r t) + Φ 0 • gaussianOne

theorem value_coeFn (hΦ : LipschitzWith K Φ) (r : ι → ℝ≥0) (t : ℝ≥0) :
    value hΦ r t =ᵐ[gaussianProduct] fun ω => Φ (coordinates r t ω) := by
  filter_upwards [Lp.coeFn_add ((centered_lipschitz hΦ).compLp (sub_self _) (vector r t))
    (Φ 0 • gaussianOne), (centered_lipschitz hΦ).coeFn_compLp (sub_self _) (vector r t),
    vector_coeFn r t, Lp.coeFn_smul (Φ 0) gaussianOne, gaussianOne_coeFn] with ω ha hc hv hs ho
  change value hΦ r t ω = _ at ha
  rw [ha]
  simp only [Pi.add_apply, hc, Function.comp_apply, hv, hs, Pi.smul_apply, ho, smul_eq_mul]
  ring

theorem value_memLp (hΦ : LipschitzWith K Φ) (r : ι → ℝ≥0) (t : ℝ≥0) :
    MemLp (fun ω => Φ (coordinates r t ω)) 2 gaussianProduct :=
  (Lp.memLp _).ae_eq (value_coeFn hΦ r t)

theorem value_continuous (hΦ : LipschitzWith K Φ) (r : ι → ℝ≥0) :
    Continuous (value hΦ r) :=
  (((centered_lipschitz hΦ).continuous_compLp (sub_self _)).comp (vector_continuous r)).add continuous_const

theorem value_past (hΦ : LipschitzWith K Φ) (r : ι → ℝ≥0) (t : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration t] (value hΦ r t) gaussianProduct :=
  (hΦ.continuous.comp_stronglyMeasurable (coordinates_past r t)).aestronglyMeasurable.congr
    (value_coeFn hΦ r t).symm

/-- No Lipschitz hypothesis on the bounded continuous composition is needed. -/
def boundedValue (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ z, ‖Φ z‖ ≤ M)
    (r : ι → ℝ≥0) (t : ℝ≥0) : GaussianL2 :=
  (MemLp.of_bound (hΦ.comp_stronglyMeasurable (coordinates_stronglyMeasurable r t)).aestronglyMeasurable
    M (Eventually.of_forall (fun _ω => hM _)) : MemLp _ 2 gaussianProduct).toLp _

theorem boundedValue_coeFn (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ z, ‖Φ z‖ ≤ M)
    (r : ι → ℝ≥0) (t : ℝ≥0) :
    boundedValue hΦ hM r t =ᵐ[gaussianProduct] fun ω => Φ (coordinates r t ω) :=
  MemLp.coeFn_toLp _

theorem boundedValue_continuous (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ z, ‖Φ z‖ ≤ M)
    (r : ι → ℝ≥0) : Continuous (boundedValue hΦ hM r) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _, hm⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((vector_continuous r).continuousAt.tendsto.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (M • gaussianOne)
  · intro n
    filter_upwards [boundedValue_coeFn hΦ hM r (ns (ms n)),
      Lp.coeFn_smul M gaussianOne, gaussianOne_coeFn] with ω hv hs ho
    simp only [hv, hs, Pi.smul_apply, ho, smul_eq_mul, mul_one]
    exact (hM _).trans (le_abs_self M)
  · filter_upwards [boundedValue_coeFn hΦ hM r t,
      Lp.coeFn_smul M gaussianOne, gaussianOne_coeFn] with ω hv hs ho
    simp only [hv, hs, Pi.smul_apply, ho, smul_eq_mul, mul_one]
    exact (hM _).trans (le_abs_self M)
  · filter_upwards [hm, ae_all_iff.mpr (fun n => boundedValue_coeFn hΦ hM r (ns (ms n))),
      boundedValue_coeFn hΦ hM r t, ae_all_iff.mpr (fun n => vector_coeFn r (ns (ms n))),
      vector_coeFn r t] with ω hm hn ht hv hw
    simp only [hn, ht]
    apply hΦ.continuousAt.tendsto.comp
    simpa only [Function.comp_def, hv, hw] using hm

theorem boundedValue_past (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ z, ‖Φ z‖ ≤ M)
    (r : ι → ℝ≥0) (t : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration t] (boundedValue hΦ hM r t) gaussianProduct :=
  (hΦ.comp_stronglyMeasurable (coordinates_past r t)).aestronglyMeasurable.congr
    (boundedValue_coeFn hΦ hM r t).symm

/-- The field belongs to the pre-existing full predictable subspace. -/
def boundedField (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ z, ‖Φ z‖ ≤ M)
    (r : ι → ℝ≥0) (T : ℝ≥0) : fullPredictable :=
  predictableField _ (boundedValue_continuous hΦ hM r) (boundedValue_past hΦ hM r) T

theorem boundedField_slices (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ z, ‖Φ z‖ ≤ M)
    (r : ι → ℝ≥0) (T : ℝ≥0) :
    scalarCurry (boundedField hΦ hM r T : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T:ℝ)).indicator (fun t => boundedValue hΦ hM r t.toNNReal) :=
  runningField_slices _ (boundedValue_continuous hΦ hM r) T

theorem bounded_stochastic_sum_tendsto (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ z, ‖Φ z‖ ≤ M)
    (r : ι → ℝ≥0) (T : ℝ≥0) :
    Tendsto (fun N => itoIntegral (predictableStep (boundedValue hΦ hM r)
      (boundedValue_past hΦ hM r) T N)) atTop (𝓝 (itoIntegral (boundedField hΦ hM r T))) :=
  integral_step_tendsto _ (boundedValue_continuous hΦ hM r) _ _

theorem bounded_drift_sum_tendsto (hΦ : Continuous Φ) {M : ℝ} (hM : ∀ z, ‖Φ z‖ ≤ M)
    (r : ι → ℝ≥0) (T : ℝ≥0) :
    Tendsto (fun N => ∑ i : Fin (N+1),
      ((uniformTime T N i.succ : ℝ) - uniformTime T N i.castSucc) •
        boundedValue hΦ hM r (uniformTime T N i.castSucc)) atTop
      (𝓝 (∫ t in 0..(T:ℝ), boundedValue hΦ hM r t.toNNReal)) :=
  drift_sum_tendsto _ (boundedValue_continuous hΦ hM r) T

end OperatorDerivativeRewrite.Foundation.GaussianStoppedComposition
