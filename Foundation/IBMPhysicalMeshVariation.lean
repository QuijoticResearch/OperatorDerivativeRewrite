import Foundation.IBMPhysicalOriginalVariation

/-! Actual corrected-residual energy bounds on arbitrary deterministic
partitions. No equal spacing or nesting assumption is imposed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalMeshVariation
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalNoiseClock
open IBMConstructedSources IBMClockCubicVariation GaussianAbsoluteMoments
open IBMPhysicalTaylorMean IBMPhysicalReflectedTaylor IBMPhysicalCorrectedVariation
open GaussianBrownianQuadraticVariation
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

theorem remainder_integrable (a b : ℝ≥0) : Integrable (remainder a b) gaussianProduct := by
  apply ((increment_integrable a b).const_mul (16*‖physicalDerivative‖^2)).mono'
    (remainder_measurable a b).aestronglyMeasurable
  exact Eventually.of_forall fun Y => by
    dsimp only [remainder, spatialRemainder]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact squared_remainder_bound _ _

theorem remainder_mean_bound (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ Y, remainder a b Y ∂gaussianProduct) ≤
      16*‖physicalDerivative‖^2 * (((b : ℝ)-a)*Real.sqrt ((b : ℝ)-a)*standardMoment 3) := by
  calc
    _ ≤ ∫ Y, 16*‖physicalDerivative‖^2 * |clockPath Y b-clockPath Y a|^3 ∂gaussianProduct :=
      integral_mono (remainder_integrable a b) ((increment_integrable a b).const_mul _)
        (fun Y => squared_remainder_bound _ _)
    _ = _ := by rw [integral_const_mul, increment_moment a b hab]

def rateConstant : ℝ := 32*‖physicalDerivative‖^2*standardMoment 3+
  8*‖physicalDerivative‖^2*standardMoment 1

theorem rateConstant_nonnegative : 0 ≤ rateConstant := by
  unfold rateConstant
  positivity [standardMoment_nonnegative 3, standardMoment_nonnegative 1]

theorem cell_integrable (a b : ℝ≥0) :
    Integrable (fun Y => ‖residual b Y-residual a Y‖^2) gaussianProduct :=
  ((residual_memLp b).sub (residual_memLp a)).norm.integrable_sq

theorem cell_rate (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ Y, ‖residual b Y-residual a Y‖^2 ∂gaussianProduct) ≤
      rateConstant * (((b : ℝ)-a)*Real.sqrt ((b : ℝ)-a)) := by
  have h : (∫ Y, ‖residual b Y-residual a Y‖^2 ∂gaussianProduct) ≤
      2*(∫ Y, remainder a b Y ∂gaussianProduct)+2*‖IBMPhysicalCellSlope.integral a b‖^2 := by
    calc
      _ ≤ ∫ Y, 2*remainder a b Y+2*‖IBMPhysicalCellSlope.integral a b Y‖^2 ∂gaussianProduct :=
        integral_mono_ae (cell_integrable a b)
          (((remainder_integrable a b).const_mul 2).add
            ((Lp.memLp (IBMPhysicalCellSlope.integral a b)).norm.integrable_sq.const_mul 2))
          (IBMPhysicalCorrectedVariation.cell_bound a b hab)
      _ = _ := by
        rw [integral_add ((remainder_integrable a b).const_mul 2)
          ((Lp.memLp (IBMPhysicalCellSlope.integral a b)).norm.integrable_sq.const_mul 2),
          integral_const_mul, integral_const_mul, ← BochnerL2Dominated.norm_sq_integral]
  have ht := remainder_mean_bound a b hab
  have hs := IBMPhysicalCellErrorRate.integral_rate a b hab
  unfold rateConstant
  nlinarith

def squares {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin n, ‖residual (τ i.succ) Y-residual (τ i.castSucc) Y‖^2

theorem squares_nonnegative {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (Y : SampleSpace) :
    0 ≤ squares τ Y := Finset.sum_nonneg fun i _hi => sq_nonneg _

theorem squares_integrable {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) :
    Integrable (squares τ) gaussianProduct :=
  integrable_finsetSum _ fun (i : Fin n) _hi => cell_integrable _ _

theorem squares_mesh_bound {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (ε : ℝ) (hmesh : ∀ i : Fin n, (τ i.succ : ℝ) - τ i.castSucc ≤ ε) :
    (∫ Y, squares τ Y ∂gaussianProduct) ≤
      rateConstant*Real.sqrt ε*((τ (Fin.last n) : ℝ) - τ 0) := by
  calc
    _ = ∑ i : Fin n, ∫ Y, ‖residual (τ i.succ) Y-residual (τ i.castSucc) Y‖^2 ∂gaussianProduct :=
      integral_finsetSum _ (fun i _hi => cell_integrable _ _)
    _ ≤ ∑ i : Fin n, (rateConstant*Real.sqrt ε)*((τ i.succ : ℝ) - τ i.castSucc) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply (cell_rate _ _ (hτ (Fin.castSucc_le_succ i))).trans
      have hd : 0 ≤ (τ i.succ : ℝ) - τ i.castSucc := sub_nonneg.mpr (hτ (Fin.castSucc_le_succ i))
      calc
        _ = (rateConstant*((τ i.succ : ℝ) - τ i.castSucc))*Real.sqrt ((τ i.succ : ℝ) - τ i.castSucc) := by ring
        _ ≤ (rateConstant*((τ i.succ : ℝ) - τ i.castSucc))*Real.sqrt ε :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hmesh i))
            (mul_nonneg rateConstant_nonnegative hd)
        _ = _ := by ring
    _ = _ := by
      rw [← Finset.mul_sum]
      exact congrArg (fun x : ℝ => rateConstant*Real.sqrt ε*x)
        (sum_fin_differences (fun i => (τ i : ℝ)))

def squaresClass {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : Lp ℝ 1 gaussianProduct :=
  (squares_integrable τ).toL1 (squares τ)

theorem squaresClass_ae {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) :
    squaresClass τ =ᵐ[gaussianProduct] squares τ := (squares_integrable τ).coeFn_toL1

theorem squares_mean_tendsto (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N + 1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0))
    (hmesh : ∀ (N : ℕ) (i : Fin (m N)), (τ N i.succ : ℝ) - τ N i.castSucc ≤ ε N)
    (L : ℝ) (hlength : ∀ N, (τ N (Fin.last (m N)) : ℝ) - τ N 0 ≤ L) :
    Tendsto (fun N => ∫ Y, squares (τ N) Y ∂gaussianProduct) atTop (nhds 0) := by
  apply squeeze_zero (fun N => integral_nonneg (squares_nonnegative (τ N)))
    (fun N => (squares_mesh_bound (τ N) (hτ N) (ε N) (hmesh N)).trans
      (mul_le_mul_of_nonneg_left (hlength N)
        (mul_nonneg rateConstant_nonnegative (Real.sqrt_nonneg _))))
  simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, zero_mul] using
    ((Real.continuous_sqrt.continuousAt.tendsto.comp hε).const_mul rateConstant).mul_const L

theorem squaresClass_tendsto (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N + 1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0))
    (hmesh : ∀ (N : ℕ) (i : Fin (m N)), (τ N i.succ : ℝ) - τ N i.castSucc ≤ ε N)
    (L : ℝ) (hlength : ∀ N, (τ N (Fin.last (m N)) : ℝ) - τ N 0 ≤ L) :
    Tendsto (fun N => squaresClass (τ N)) atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, squaresClass, L1.norm_of_fun_eq_integral_norm,
    Real.norm_of_nonneg (squares_nonnegative _ _)] using
    squares_mean_tendsto m τ hτ ε hε hmesh L hlength

end OperatorDerivativeRewrite.Foundation.IBMPhysicalMeshVariation
