import Foundation.IBMPhysicalCellSlopeActual

/-! A quantitative energy bound for the ACTUAL original physical cell-error
Ito integrals, obtained from the proved clock first moment and product integration. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalCellErrorRate
open InfiniteGaussian IBMConstructedSources IBMClockCubicVariation GaussianAbsoluteMoments
open IBMPhysicalCellSlopeActual IBMPhysicalNoiseClock BrownianClockWeightedEnergy
open GaussianBrownianQuadraticVariation
attribute [local irreducible] IBMConstructedSources.clockPath
local instance : InnerProductSpace ℝ IBMPhysicalWeakWiener.Kernel :=
  InnerProductSpace.rclikeToReal ℂ _

theorem clock_first_moment (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ Y, |clockPath Y b-clockPath Y a| ∂gaussianProduct) =
      Real.sqrt ((b : ℝ)-a) * standardMoment 1 := by
  have hn : ‖incrementVector a b‖^2 = (b : ℝ)-a := by
    rw [incrementVector, LinearIsometry.norm_map]
    exact GaussianTimeHilbert.timeVector_sub_norm_sq a b hab
  have he : ‖incrementVector a b‖ = Real.sqrt ((b : ℝ)-a) := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  calc
    _ = ∫ Y, |firstChaosEmbedding (incrementVector a b) Y| ∂gaussianProduct :=
      integral_congr_ae ((increment_ae a b).mono fun Y h => congrArg abs h.symm)
    _ = _ := by
      have h := firstChaos_absolute_moment (incrementVector a b) 1
      simpa only [pow_one, he] using h

def distance (a b : ℝ≥0) (z : ℝ × SampleSpace) : ℝ :=
  (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => |sigma z-clockPath z.2 a|) z.1

theorem distance_integral_bound (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ z, distance a b z ∂(PredictableRealL2.horizonMeasure b gaussianProduct)) ≤
      ((b : ℝ)-a) * Real.sqrt ((b : ℝ)-a) * standardMoment 1 := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (b : ℝ))
  let C : ℝ := Real.sqrt ((b : ℝ)-a)*standardMoment 1
  have hf : Integrable (distance a b) (μ.prod gaussianProduct) := by
    change Integrable (fun z : ℝ × SampleSpace =>
      (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => |sigma z-clockPath z.2 a|) z.1)
        ((volume.restrict (Ioc 0 (b : ℝ))).prod gaussianProduct)
    rw [← PredictableRealL2.horizonMeasure_eq_product]
    exact actual_distance_integrable a b
  have hm : Integrable ((Ioc (a : ℝ) (b : ℝ)).indicator (fun _ : ℝ => C)) μ :=
    (integrable_const C).indicator measurableSet_Ioc
  have hp (x : ℝ) : (∫ Y, distance a b (x,Y) ∂gaussianProduct) ≤
      (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => C) x := by
    by_cases hx : x ∈ Ioc (a : ℝ) (b : ℝ)
    · have hx0 : 0 ≤ x := a.coe_nonneg.trans hx.1.le
      have htx : (x.toNNReal : ℝ) = x := Real.coe_toNNReal x hx0
      have hax : a ≤ x.toNNReal := by
        exact_mod_cast (show (a : ℝ) ≤ (x.toNNReal : ℝ) by rw [htx]; exact hx.1.le)
      simp only [distance, indicator_of_mem hx]
      change (∫ Y, |clockPath Y x.toNNReal-clockPath Y a| ∂gaussianProduct) ≤ C
      rw [clock_first_moment a x.toNNReal hax]
      dsimp only [C]
      rw [htx]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [hx.2]))
        (standardMoment_nonnegative 1)
    · simp only [distance, indicator_of_notMem hx, integral_zero]
      exact le_rfl
  rw [PredictableRealL2.horizonMeasure_eq_product, integral_prod _ hf]
  calc
    _ ≤ ∫ x, (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => C) x ∂μ :=
      integral_mono_ae hf.integral_prod_left hm (Eventually.of_forall hp)
    _ = _ := by
      rw [integral_indicator_const _ measurableSet_Ioc]
      change (volume.restrict (Ioc 0 (b : ℝ))).real (Ioc (a : ℝ) (b : ℝ)) • C = _
      rw [measureReal_restrict_apply measurableSet_Ioc, Ioc_inter_Ioc,
        max_eq_left a.coe_nonneg, min_self,
        Real.volume_real_Ioc_of_le (show (a : ℝ) ≤ b from hab)]
      dsimp only [C]
      simp only [smul_eq_mul]
      ring

theorem integral_rate (a b : ℝ≥0) (hab : a ≤ b) :
    ‖IBMPhysicalCellSlope.integral a b‖^2 ≤
      4*‖physicalDerivative‖^2 * (((b : ℝ)-a)*Real.sqrt ((b : ℝ)-a)*standardMoment 1) :=
  (integral_clock_distance_bound a b).trans
    (mul_le_mul_of_nonneg_left (distance_integral_bound a b hab) (by positivity))

theorem uniform_energy_bound (T : ℝ≥0) (n : ℕ) :
    (∑ i : Fin (n+1), ‖IBMPhysicalCellSlope.integral
      (uniformTime T n i.castSucc) (uniformTime T n i.succ)‖^2) ≤
        4*‖physicalDerivative‖^2 * ((T : ℝ)*Real.sqrt ((T : ℝ)/(n+1))*standardMoment 1) := by
  calc
    _ ≤ ∑ i : Fin (n+1), 4*‖physicalDerivative‖^2 *
        (((uniformTime T n i.succ : ℝ)-uniformTime T n i.castSucc) *
          Real.sqrt ((uniformTime T n i.succ : ℝ)-uniformTime T n i.castSucc)*standardMoment 1) :=
      Finset.sum_le_sum fun i _hi => integral_rate _ _
        (uniformTime_monotone T n (Fin.castSucc_le_succ i))
    _ = _ := by
      simp only [uniformTime_step, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      have hn : (n : ℝ)+1 ≠ 0 := by positivity
      field_simp
      <;> ring

theorem uniform_energy_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ∑ i : Fin (n+1), ‖IBMPhysicalCellSlope.integral
      (uniformTime T n i.castSucc) (uniformTime T n i.succ)‖^2) atTop (nhds 0) := by
  apply squeeze_zero (fun n => Finset.sum_nonneg fun i _hi => sq_nonneg _)
    (fun n => uniform_energy_bound T n)
  have hm : Tendsto (fun n : ℕ => (T : ℝ)/(n+1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h := ((Real.continuous_sqrt.continuousAt.tendsto.comp hm).const_mul (T : ℝ)).mul_const
    (standardMoment 1)
  simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, zero_mul] using
    h.const_mul (4*‖physicalDerivative‖^2)

def cellSquares (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (n+1), ‖IBMPhysicalCellSlope.integral
    (uniformTime T n i.castSucc) (uniformTime T n i.succ) Y‖^2

theorem cellSquares_nonnegative (T : ℝ≥0) (n : ℕ) (Y : SampleSpace) :
    0 ≤ cellSquares T n Y := Finset.sum_nonneg fun i _hi => sq_nonneg _

theorem cellSquares_integrable (T : ℝ≥0) (n : ℕ) :
    Integrable (cellSquares T n) gaussianProduct :=
  integrable_finsetSum _ fun i _hi =>
    (Lp.memLp (IBMPhysicalCellSlope.integral
      (uniformTime T n i.castSucc) (uniformTime T n i.succ))).norm.integrable_sq

theorem cellSquares_mean (T : ℝ≥0) (n : ℕ) :
    (∫ Y, cellSquares T n Y ∂gaussianProduct) =
      ∑ i : Fin (n+1), ‖IBMPhysicalCellSlope.integral
        (uniformTime T n i.castSucc) (uniformTime T n i.succ)‖^2 := by
  rw [show cellSquares T n = fun Y => ∑ i : Fin (n+1), ‖IBMPhysicalCellSlope.integral
    (uniformTime T n i.castSucc) (uniformTime T n i.succ) Y‖^2 from rfl]
  rw [integral_finsetSum _ (fun i _hi =>
    (Lp.memLp (IBMPhysicalCellSlope.integral
      (uniformTime T n i.castSucc) (uniformTime T n i.succ))).norm.integrable_sq)]
  apply Finset.sum_congr rfl
  intro i _hi
  exact (BochnerL2Dominated.norm_sq_integral _).symm

theorem cellSquares_mean_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ∫ Y, cellSquares T n Y ∂gaussianProduct) atTop (nhds 0) := by
  simpa only [cellSquares_mean] using uniform_energy_tendsto T

def cellSquaresClass (T : ℝ≥0) (n : ℕ) : Lp ℝ 1 gaussianProduct :=
  (cellSquares_integrable T n).toL1 (cellSquares T n)

theorem cellSquaresClass_ae (T : ℝ≥0) (n : ℕ) :
    cellSquaresClass T n =ᵐ[gaussianProduct] cellSquares T n :=
  (cellSquares_integrable T n).coeFn_toL1

theorem cellSquaresClass_tendsto (T : ℝ≥0) :
    Tendsto (cellSquaresClass T) atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, cellSquaresClass, L1.norm_of_fun_eq_integral_norm,
    Real.norm_of_nonneg (cellSquares_nonnegative T _ _)] using cellSquares_mean_tendsto T

end OperatorDerivativeRewrite.Foundation.IBMPhysicalCellErrorRate
