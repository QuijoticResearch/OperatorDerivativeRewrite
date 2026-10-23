import Foundation.IBMCanonicalMollifiedScenery
import Foundation.IBMNonlinearFirstSource

/-! Exact original nonlinear source covariance and strong spatial continuity.
The Gaussian value/derivative correction is retained, never factored away. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearColumnContinuity
open InfiniteGaussian IBMGaussianSteinMoments IBMNonlinearClockColumn
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def covariance (w v a b : CoefficientSpace) : ℝ :=
  ((inner ℝ a b-inner ℝ (w+v) a*inner ℝ (w+v) b)*Real.exp (-‖w+v‖^2/2)+
    (inner ℝ a b-inner ℝ (w-v) a*inner ℝ (w-v) b)*Real.exp (-‖w-v‖^2/2))/2

theorem column_inner_formula (n m : ℕ) (r q : ℝ) :
    inner ℝ (column n r) (column m q) = covariance
      (tripleCoefficient n r 0) (tripleCoefficient m q 0)
      (tripleCoefficient n r 1) (tripleCoefficient m q 1) := by
  have he : inner ℝ (column n r) (column m q) =
      ∫ ω, firstChaosEmbedding (tripleCoefficient n r 1) ω *
        firstChaosEmbedding (tripleCoefficient m q 1) ω *
          Real.cos (firstChaosEmbedding (tripleCoefficient n r 0) ω) *
            Real.cos (firstChaosEmbedding (tripleCoefficient m q 0) ω) ∂gaussianProduct := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [column_firstChaos_ae n r, column_firstChaos_ae m q] with ω hn hm
    rw [hn, hm, Real.inner_apply]
    ring
  rw [he, GaussianCosineProductCovariance.product_formula]
  simp only [GaussianMixedTrigCovariance.mean, IBMNonlinearFirstSource.cosine_mean]
  rfl

theorem covariance_continuous : Continuous (fun p : (CoefficientSpace × CoefficientSpace) ×
    (CoefficientSpace × CoefficientSpace) => covariance p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold covariance
  fun_prop

theorem column_inner_continuous (n m : ℕ) :
    Continuous (fun p : ℝ × ℝ => inner ℝ (column n p.1) (column m p.2)) := by
  simp_rw [column_inner_formula]
  exact covariance_continuous.comp
    ((((IBMClockCubicTimeProjection.tripleCoefficient_continuous n 0).comp continuous_fst).prodMk
      ((IBMClockCubicTimeProjection.tripleCoefficient_continuous m 0).comp continuous_snd)).prodMk
        (((IBMClockCubicTimeProjection.tripleCoefficient_continuous n 1).comp continuous_fst).prodMk
          ((IBMClockCubicTimeProjection.tripleCoefficient_continuous m 1).comp continuous_snd)))

attribute [local irreducible] column

/-- Strong original Gaussian-L2 continuity, not merely continuity of its mean. -/
theorem column_continuous (n : ℕ) : Continuous (column n) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  have hself : Continuous (fun q => inner ℝ (column n q) (column n q)) :=
    (column_inner_continuous n n).comp (continuous_id.prodMk continuous_id)
  have hfixed : Continuous (fun q => inner ℝ (column n q) (column n r)) :=
    (column_inner_continuous n n).comp (continuous_id.prodMk continuous_const)
  have ht : Tendsto (fun q => inner ℝ (column n q) (column n q)+‖column n r‖^2-
      2*inner ℝ (column n q) (column n r)) (𝓝 r)
      (𝓝 (inner ℝ (column n r) (column n r)+‖column n r‖^2-
        2*inner ℝ (column n r) (column n r))) :=
    (hself.continuousAt.tendsto.add_const (‖column n r‖^2)).sub
      (hfixed.continuousAt.tendsto.const_mul 2)
  have he : (fun q => inner ℝ (column n q) (column n q)+‖column n r‖^2-
      2*inner ℝ (column n q) (column n r)) = fun q => ‖column n q-column n r‖^2 := by
    funext q
    rw [norm_sub_sq_real, real_inner_self_eq_norm_sq]
    ring
  have hz : inner ℝ (column n r) (column n r)+‖column n r‖^2-
      2*inner ℝ (column n r) (column n r) = 0 := by
    rw [real_inner_self_eq_norm_sq]
    ring
  rw [he, hz] at ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  have hn : Tendsto (fun q => ‖column n q-column n r‖) (𝓝 r) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end OperatorDerivativeRewrite.Foundation.IBMNonlinearColumnContinuity
