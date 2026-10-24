import Foundation.GaussianAbsoluteMoments
import Foundation.IBMPhysicalReflectedTaylor

/-! Cubic absolute increment sums of the ACTUAL Brownian clock converge in
mean. The finite expectation is derived from the existing actual Gaussian law. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockCubicVariation
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianHilbertProcess
open GaussianAbsoluteMoments SeparableHilbertEmbedding GaussianBrownianQuadraticVariation
open IBMConstructedSources
attribute [local instance] timeHilbert_secondCountable

def incrementVector (s t : ℝ≥0) : CoefficientSpace :=
  hilbertEmbedding TimeHilbert (timeVector t - timeVector s)

theorem increment_ae (s t : ℝ≥0) : firstChaosEmbedding (incrementVector s t) =ᵐ[gaussianProduct]
    fun Y => clockPath Y t - clockPath Y s := by
  change isonormal TimeHilbert (timeVector t - timeVector s) =ᵐ[gaussianProduct] _
  filter_upwards [isonormal_sub_ae (timeVector t) (timeVector s),
    clockPath_coordinate_ae t, clockPath_coordinate_ae s] with Y hi ht hs
  rw [ht, hs]
  exact hi

theorem increment_integrable (s t : ℝ≥0) :
    Integrable (fun Y => |clockPath Y t - clockPath Y s|^3) gaussianProduct :=
  (firstChaos_absolute_integrable (incrementVector s t) 3).congr
    ((increment_ae s t).mono fun Y he => congrArg (fun x : ℝ => |x|^3) he)

theorem increment_moment (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ Y, |clockPath Y t - clockPath Y s|^3 ∂gaussianProduct) =
      ((t : ℝ)-s) * Real.sqrt ((t : ℝ)-s) * standardMoment 3 := by
  have hn : ‖incrementVector s t‖^2 = (t : ℝ)-s := by
    rw [incrementVector, LinearIsometry.norm_map]
    exact timeVector_sub_norm_sq s t hst
  have he : ‖incrementVector s t‖ = Real.sqrt ((t : ℝ)-s) := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  calc
    _ = ∫ Y, |firstChaosEmbedding (incrementVector s t) Y|^3 ∂gaussianProduct :=
      integral_congr_ae ((increment_ae s t).mono fun Y h =>
        congrArg (fun x : ℝ => |x|^3) h.symm)
    _ = _ := by
      rw [firstChaos_absolute_moment, he]
      have hsq := Real.sq_sqrt (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))
      nlinarith [mul_nonneg (Real.sqrt_nonneg ((t : ℝ)-s)) (standardMoment_nonnegative 3)]

def cubic (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (n + 1), |clockPath Y (uniformTime T n i.succ) -
    clockPath Y (uniformTime T n i.castSucc)|^3

theorem cubic_nonnegative (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) : 0 ≤ cubic T n Y :=
  Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg _) 3

theorem cubic_integrable (T : ℝ≥0) (n : ℕ) : Integrable (cubic T n) gaussianProduct :=
  integrable_finset_sum _ fun i _ => increment_integrable _ _

theorem cubic_integral (T : ℝ≥0) (n : ℕ) :
    (∫ Y, cubic T n Y ∂gaussianProduct) =
      (T : ℝ) * Real.sqrt ((T : ℝ)/(n+1)) * standardMoment 3 := by
  rw [show cubic T n = fun Y => ∑ i : Fin (n+1),
    |clockPath Y (uniformTime T n i.succ) - clockPath Y (uniformTime T n i.castSucc)|^3 from rfl]
  rw [integral_finset_sum _ (fun i _ => increment_integrable _ _)]
  simp_rw [increment_moment _ _ (uniformTime_monotone T n (Fin.castSucc_le_succ _)),
    uniformTime_step]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem cubic_mean_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ∫ Y, cubic T n Y ∂gaussianProduct) atTop (nhds 0) := by
  have hm : Tendsto (fun n : ℕ => (T : ℝ)/(n+1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hm
  have h := (hs.const_mul (T : ℝ)).mul_const (standardMoment 3)
  simpa only [cubic_integral, Function.comp_def, Real.sqrt_zero, mul_zero, zero_mul] using h

theorem cubic_norm_mean_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ∫ Y, ‖cubic T n Y‖ ∂gaussianProduct) atTop (nhds 0) := by
  simpa only [Real.norm_of_nonneg (cubic_nonnegative T _ _)] using cubic_mean_tendsto T

def cubicClass (T : ℝ≥0) (n : ℕ) : Lp ℝ 1 gaussianProduct :=
  (cubic_integrable T n).toL1 (cubic T n)

theorem cubicClass_ae (T : ℝ≥0) (n : ℕ) : cubicClass T n =ᵐ[gaussianProduct] cubic T n :=
  (cubic_integrable T n).coeFn_toL1

theorem cubicClass_tendsto (T : ℝ≥0) :
    Tendsto (cubicClass T) atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, cubicClass, L1.norm_of_fun_eq_integral_norm] using
    cubic_norm_mean_tendsto T

end OperatorDerivativeRewrite.Foundation.IBMClockCubicVariation
