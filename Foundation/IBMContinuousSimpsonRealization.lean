import Foundation.IBMUniformTimeSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual polynomial continuous-path approximants assembled from signed
IBM grid-prefix sums. Convergence is in probability in the SUPREMUM NORM.
Bernstein smoothing is explicit; it is not linear interpolation or causality. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators unitInterval
namespace OperatorDerivativeRewrite.Foundation.IBMContinuousSimpsonRealization
open IBMSourceLaws IBMConstructedSources IBMContinuousQuadrature
open IBMTimeSpaceQuadrature IBMTimeSpaceSimpson IBMUniformTimeSpace
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

theorem snapshot_continuous (F : ℝ → ℝ → ℝ)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (ω : JointSample) : Continuous (snapshot F ω) := by
  have hc := hD.comp (continuous_id.prodMk (path_continuous ω))
  exact ((hF.comp (continuous_id.prodMk (path_continuous ω))).sub continuous_const).sub
    (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0)

def curve (F : ℝ → ℝ → ℝ)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (T : ℝ≥0) (ω : JointSample) : C(I, ℝ) :=
  ⟨fun u => snapshot F ω ((T : ℝ)*(u : ℝ)),
    (snapshot_continuous F hF hD ω).comp (continuous_const.mul continuous_subtype_val)⟩

theorem curve_measurable (F : ℝ → ℝ → ℝ)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hspace : ∀ t, ContDiff ℝ 4 (F t))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (T : ℝ≥0) : Measurable (curve F hF hD T) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro u
  let r : ℝ≥0 := ⟨(T : ℝ)*(u : ℝ), mul_nonneg T.coe_nonneg u.property.1⟩
  have he : (fun ω => curve F hF hD T ω u) = target F r := by
    funext ω
    exact (target_snapshot F r ω).symm
  rw [he]
  exact target_measurable F hspace hD r

/-- Explicit degree-(n + 1) Bernstein polynomial whose coefficients are the
ACTUAL signed spatial Simpson sums at all prefixes of ONE common time grid. -/
def approximation (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : C(I, ℝ) :=
  ∑ k : Fin (n + 2), bernstein (n + 1) k *
    ContinuousMap.const I (prefixSums F T n k ω)

theorem approximation_zero (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    approximation F T n ω 0 = 0 := by
  simp [approximation, Fin.sum_univ_succ, bernstein_apply, prefixSums]

theorem approximation_one (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    approximation F T n ω 1 = sums F T n ω := by
  simp [approximation, Fin.sum_univ_castSucc, bernstein_apply,
    Nat.sub_eq_zero_iff_le, prefixSums, sums]

theorem approximation_measurable (F : ℝ → ℝ → ℝ)
    (hspace : ∀ t, ContDiff ℝ 4 (F t)) (T : ℝ≥0) (n : ℕ) :
    Measurable (approximation F T n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro u
  have he : (fun ω => approximation F T n ω u) = fun ω =>
      ∑ k : Fin (n + 2), bernstein (n + 1) k u * prefixSums F T n k ω := by
    funext ω
    simp only [approximation, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
      ContinuousMap.const_apply]
  rw [he]
  exact Finset.measurable_sum _ (fun k _ => (prefixSums_measurable F hspace T n k).const_mul _)

theorem curve_node (F : ℝ → ℝ → ℝ)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (T : ℝ≥0) (n : ℕ) (k : Fin (n + 2)) (ω : JointSample) :
    curve F hF hD T ω (bernstein.z k) = snapshot F ω (time T (n + 1) k) := by
  change snapshot F ω ((T : ℝ)*((k : ℝ)/(n + 1 : ℕ))) = _
  congr 1
  unfold time
  ring

/-- Positivity and sum-one of the Bernstein basis preserve the ACTUAL maximum
grid-node error without a factor depending on the number of cells. -/
theorem approximation_error_bound (F : ℝ → ℝ → ℝ)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    ‖approximation F T n ω - bernsteinApproximation (n + 1) (curve F hF hD T ω)‖ ≤
      maximum F T n ω := by
  apply (ContinuousMap.norm_le _ (maximum_nonneg F T n ω)).mpr
  intro u
  simp only [ContinuousMap.sub_apply, Real.norm_eq_abs, approximation,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply,
    bernsteinApproximation.apply, smul_eq_mul, curve_node]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k : Fin (n + 2), |bernstein (n + 1) k u * prefixSums F T n k ω -
        bernstein (n + 1) k u * snapshot F ω (time T (n + 1) k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin (n + 2), bernstein (n + 1) k u * |error F T n k ω| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← mul_sub, abs_mul, abs_of_nonneg bernstein_nonneg]
      rfl
    _ ≤ ∑ k : Fin (n + 2), bernstein (n + 1) k u * maximum F T n ω := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (error_le_maximum F T n k (by omega) ω) bernstein_nonneg
    _ = maximum F T n ω := by rw [← Finset.sum_mul, bernstein.probability, one_mul]

attribute [local irreducible] curve approximation IBMUniformTimeSpace.maximum

theorem approximation_sequence_tendsto (F : ℝ → ℝ → ℝ)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hD : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    (T : ℝ≥0) (ω : JointSample) (idx : ℕ → ℕ) (hidx : Tendsto idx atTop atTop)
    (hmax : Tendsto (fun j => maximum F T (idx j) ω) atTop (𝓝 0)) :
    Tendsto (fun j => approximation F T (idx j) ω) atTop (𝓝 (curve F hF hD T ω)) := by
  have hi : Tendsto (fun j => idx j + 1) atTop atTop :=
    (Filter.tendsto_add_atTop_nat 1).comp hidx
  have hb := (bernsteinApproximation_uniform (curve F hF hD T ω)).comp hi
  have he : Tendsto (fun j => approximation F T (idx j) ω -
      bernsteinApproximation (idx j + 1) (curve F hF hD T ω)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun j => approximation_error_bound F hF hD T (idx j) ω) hmax
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using he.add hb

/-- Genuine continuous-path stochastic realization: probability convergence
in C([0,1],R) SUPREMUM NORM, representing physical times t=T*u. No Lp or
adaptedness assumption/conclusion is hidden in this topology. -/
theorem approximation_tendstoInMeasure (F : ℝ → ℝ → ℝ)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hspace : ∀ t, ContDiff ℝ 4 (F t))
    (htime : ∀ x, ContDiff ℝ 1 (fun t => F t x))
    (hfour : Continuous (fun p : ℝ × ℝ => iteratedDeriv 4 (F p.1) p.2))
    (hdt : Continuous (fun p : ℝ × ℝ => timeDerivative F p.1 p.2))
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (approximation F T) atTop (curve F hF hdt T) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (approximation_measurable F hspace T n).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms,hms,he⟩ := ((maximum_tendstoInMeasure F hspace htime hfour hdt hT).comp
    hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [he] with ω hω
  exact approximation_sequence_tendsto F hF hdt T ω (ns ∘ ms)
    (hns.comp hms).tendsto_atTop hω

end OperatorDerivativeRewrite.Foundation.IBMContinuousSimpsonRealization
