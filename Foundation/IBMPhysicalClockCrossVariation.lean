import Foundation.IBMPhysicalOriginalMesh

/-! Actual physical correction--clock covariation vanishes in strong L1
along arbitrary deterministic vanishing-mesh partitions of [0,T]. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalClockCrossVariation
open InfiniteGaussian IBMPhysicalWeakWiener IBMConstructedSources GaussianTimeProcess
open GaussianBrownianQuadraticVariation
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul

theorem product_integrable (f : SampleSpace → Kernel) (g : SampleSpace → ℝ)
    (hf : MemLp f 2 gaussianProduct) (hg : MemLp g 2 gaussianProduct) :
    Integrable (fun Y => g Y • f Y) gaussianProduct := by
  apply (hg.norm.integrable_mul hf.norm).mono' (hg.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  exact Eventually.of_forall fun Y => by
    change ‖g Y • f Y‖ ≤ ‖g Y‖*‖f Y‖
    rw [norm_smul]

theorem product_norm_mean_bound (f : SampleSpace → Kernel) (g : SampleSpace → ℝ)
    (hf : MemLp f 2 gaussianProduct) (hg : MemLp g 2 gaussianProduct) :
    (∫ Y, ‖g Y • f Y‖ ∂gaussianProduct) ≤
      Real.sqrt (∫ Y, ‖g Y‖^2 ∂gaussianProduct)*Real.sqrt (∫ Y, ‖f Y‖^2 ∂gaussianProduct) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun Y => norm_nonneg (g Y))
    (Eventually.of_forall fun Y => norm_nonneg (f Y))
    (by simpa using hg.norm) (by simpa using hf.norm)
  simp only [Real.rpow_two] at h
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  simpa only [norm_smul] using h

theorem clock_increment_memLp (a b : ℝ≥0) :
    MemLp (fun Y => clockPath Y b-clockPath Y a) 2 gaussianProduct := by
  apply ((Lp.memLp (wienerL2 b)).sub (Lp.memLp (wienerL2 a))).ae_eq
  filter_upwards [clockPath_coordinate_ae a, clockPath_coordinate_ae b] with Y ha hb
  change process b Y-process a Y = _
  rw [ha, hb]

theorem clock_increment_energy (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ Y, ‖clockPath Y b-clockPath Y a‖^2 ∂gaussianProduct) = (b : ℝ)-a := by
  calc
    _ = ∫ Y, ‖(wienerL2 b-wienerL2 a) Y‖^2 ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (wienerL2 b) (wienerL2 a),
        clockPath_coordinate_ae a, clockPath_coordinate_ae b] with Y hd ha hb
      simp only [Pi.sub_apply] at hd
      rw [hd, ha, hb]
      rfl
    _ = ‖wienerL2 b-wienerL2 a‖^2 := (BochnerL2Dominated.norm_sq_integral _).symm
    _ = _ := wienerL2_sub_norm_sq a b hab

def cross {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (Y : SampleSpace) : Kernel :=
  ∑ i : Fin n, (clockPath Y (τ i.succ)-clockPath Y (τ i.castSucc)) •
    (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-
      IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y)

theorem cross_integrable {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : Integrable (cross τ) gaussianProduct :=
  integrable_finsetSum _ fun (i : Fin n) _hi => product_integrable _ _
    ((Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ))).sub
      (Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc))))
    (clock_increment_memLp _ _)

theorem cross_mean_bound {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) :
    (∫ Y, ‖cross τ Y‖ ∂gaussianProduct) ≤
      Real.sqrt ((τ (Fin.last n) : ℝ) - τ 0)*
        Real.sqrt (∫ Y, IBMPhysicalOriginalMesh.squares τ Y ∂gaussianProduct) := by
  let A (i : Fin n) := ∫ Y, ‖clockPath Y (τ i.succ)-clockPath Y (τ i.castSucc)‖^2 ∂gaussianProduct
  let B (i : Fin n) := ∫ Y, ‖IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-
    IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y‖^2 ∂gaussianProduct
  have hprod (i : Fin n) := product_integrable _ _
    ((Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ))).sub
      (Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc))))
    (clock_increment_memLp (τ i.castSucc) (τ i.succ))
  have hA : (∑ i : Fin n, A i) = (τ (Fin.last n) : ℝ) - τ 0 := by
    simp only [A, clock_increment_energy _ _ (hτ (Fin.castSucc_le_succ _))]
    exact sum_fin_differences (fun i => (τ i : ℝ))
  have hB : (∑ i : Fin n, B i) = ∫ Y, IBMPhysicalOriginalMesh.squares τ Y ∂gaussianProduct := by
    symm
    exact integral_finsetSum _ (fun i _hi =>
      ((Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ))).sub
        (Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc)))).norm.integrable_sq)
  calc
    _ ≤ ∫ Y, ∑ i : Fin n, ‖(clockPath Y (τ i.succ)-clockPath Y (τ i.castSucc)) •
        (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-
          IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y)‖ ∂gaussianProduct :=
      integral_mono (cross_integrable τ).norm (integrable_finsetSum _ fun i _hi => (hprod i).norm)
        (fun Y => norm_sum_le _ _)
    _ = ∑ i : Fin n, ∫ Y, ‖(clockPath Y (τ i.succ)-clockPath Y (τ i.castSucc)) •
        (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-
          IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y)‖ ∂gaussianProduct :=
      integral_finsetSum _ (fun i _hi => (hprod i).norm)
    _ ≤ ∑ i : Fin n, Real.sqrt (A i)*Real.sqrt (B i) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact product_norm_mean_bound _ _
        ((Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ))).sub
          (Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc))))
        (clock_increment_memLp _ _)
    _ ≤ Real.sqrt (∑ i : Fin n, A i)*Real.sqrt (∑ i : Fin n, B i) :=
      Real.sum_sqrt_mul_sqrt_le _ (fun i => integral_nonneg fun Y => sq_nonneg _)
        (fun i => integral_nonneg fun Y => sq_nonneg _)
    _ = _ := by rw [hA, hB]

def crossClass {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : Lp Kernel 1 gaussianProduct :=
  (cross_integrable τ).toL1 (cross τ)

theorem crossClass_ae {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) :
    crossClass τ =ᵐ[gaussianProduct] cross τ := (cross_integrable τ).coeFn_toL1

theorem cross_norm_mean_tendsto (T : ℝ≥0) (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N + 1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hz : ∀ N, τ N 0 = 0)
    (hend : ∀ N, τ N (Fin.last (m N)) = T) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (nhds 0))
    (hmesh : ∀ (N : ℕ) (i : Fin (m N)), (τ N i.succ : ℝ) - τ N i.castSucc ≤ ε N) :
    Tendsto (fun N => ∫ Y, ‖cross (τ N) Y‖ ∂gaussianProduct) atTop (nhds 0) := by
  apply squeeze_zero (fun N => integral_nonneg fun Y => norm_nonneg _)
    (fun N => cross_mean_bound (τ N) (hτ N))
  have hc := IBMPhysicalOriginalMesh.squares_mean_tendsto T m τ hτ hz hend ε hε hmesh
  have hs := (Real.continuous_sqrt.continuousAt.tendsto.comp hc).const_mul (Real.sqrt (T : ℝ))
  simpa only [hend, hz, NNReal.coe_zero, sub_zero, Function.comp_def, Real.sqrt_zero, mul_zero] using hs

theorem crossClass_tendsto (T : ℝ≥0) (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N + 1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hz : ∀ N, τ N 0 = 0)
    (hend : ∀ N, τ N (Fin.last (m N)) = T) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (nhds 0))
    (hmesh : ∀ (N : ℕ) (i : Fin (m N)), (τ N i.succ : ℝ) - τ N i.castSucc ≤ ε N) :
    Tendsto (fun N => crossClass (τ N)) atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, crossClass, L1.norm_of_fun_eq_integral_norm] using
    cross_norm_mean_tendsto T m τ hτ hz hend ε hε hmesh

end OperatorDerivativeRewrite.Foundation.IBMPhysicalClockCrossVariation
