import Foundation.HigherHeatInterpolatedPaths
import Foundation.SignedDensityProbabilityTransport

/-! Actual signed weights on the constructed continuous-path probability samplers. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatWeightedPaths
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatCylinderFourier
open HigherHeatProbabilitySampling HigherHeatInterpolatedPaths HigherHeatPositionVariation
open SignedDensityProbabilitySampling SignedAbsoluteIntegration

def recover (n : ℕ) (ω : Path) : Grid n := (cumulativeMeasEquiv (gridSize n)).symm (sample n ω)

theorem recover_measurable (n : ℕ) : Measurable (recover n) :=
  (cumulativeMeasEquiv (gridSize n)).symm.measurable.comp (sample_continuous n).measurable

theorem recover_incrementPath (n : ℕ) (x : Grid n) : recover n (incrementPath n x)=x := by
  rw [recover, sample_incrementPath, ← cumulativeEquiv_apply]
  exact (cumulativeMeasEquiv (gridSize n)).symm_apply_apply x

def pathWeight (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (ω : Path) : ℝ :=
  dyadicWeight m hm T hT n (recover n ω)

theorem pathWeight_measurable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    Measurable (pathWeight m hm T hT n) :=
  (weight_measurable (base (gridSize n))
    (density (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n))
    (density_measurable (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n))).comp
      (recover_measurable n)

theorem pathWeight_incrementPath (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (x : Grid n) :
    pathWeight m hm T hT n (incrementPath n x)=dyadicWeight m hm T hT n x := by
  rw [pathWeight, recover_incrementPath]

theorem pathWeight_abs (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (ω : Path) :
    |pathWeight m hm T hT n ω|=(∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n) :=
  (weight_abs (base (gridSize n))
    (density (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n))
    (density_mass_positive (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n))
    (recover n ω)).trans (dyadic_mass m hm T hT n)

theorem pathWeight_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    Integrable (pathWeight m hm T hT n) (probabilityPath m hm T hT n) := by
  letI := probabilityPath_isProbability m hm T hT n
  apply Integrable.of_bound (pathWeight_measurable m hm T hT n).aestronglyMeasurable
    ((∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n))
  exact Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, pathWeight_abs]

theorem signedPath_density (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (probabilityPath m hm T hT n).withDensityᵥ (pathWeight m hm T hT n)=signedPath m hm T hT n :=
  SignedDensityProbabilityTransport.signed_sampler_pushforward (base (gridSize n))
    (density (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n))
    (HigherHeatSignedLaws.incrementDensity_integrable m hm (fun _ : Fin (gridSize n) => duration T n)
      (fun _ => duration_pos T hT n))
    (density_measurable (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n))
    (density_mass_positive (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n))
    (incrementPath n) (incrementPath_continuous n).measurable (pathWeight m hm T hT n)
    (pathWeight_measurable m hm T hT n) (pathWeight_incrementPath m hm T hT n)

theorem signedPath_expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ)
    (g : Path → ℂ) (hg : (signedPath m hm T hT n).Integrable g) :
    (∫ᵛ ω, g ω ∂<•signedPath m hm T hT n)=
      ∫ ω, pathWeight m hm T hT n ω • g ω ∂probabilityPath m hm T hT n := by
  rw [← signedPath_density] at hg ⊢
  exact integral_density _ _ (pathWeight_integrable m hm T hT n)
    (pathWeight_measurable m hm T hT n) g
    ((signed_integrable_iff _ _ (pathWeight_integrable m hm T hT n) g).mp hg)

theorem signedPath_variation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (signedPath m hm T hT n).variation=
      ENNReal.ofReal ((∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n)) •
        probabilityPath m hm T hT n := by
  rw [← signedPath_density, variation_density _ _ (pathWeight_integrable m hm T hT n)]
  unfold absoluteDensity
  have he : (fun ω => ENNReal.ofReal |pathWeight m hm T hT n ω|)=
      fun _ => ENNReal.ofReal ((∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n)) := by
    funext ω
    rw [pathWeight_abs]
  rw [he, withDensity_const]

theorem path_domain_iff (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (g : Path → ℂ) :
    (signedPath m hm T hT n).Integrable g ↔ Integrable g (probabilityPath m hm T hT n) := by
  have hp : 0 < (∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n) := by
    rw [← dyadic_mass m hm T hT n]
    exact density_mass_positive (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n)
  rw [VectorMeasure.Integrable, signedPath_variation]
  exact integrable_smul_measure (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top

theorem path_weighted_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ)
    (g : Path → ℂ) (hg : (signedPath m hm T hT n).Integrable g) :
    Integrable (fun ω => pathWeight m hm T hT n ω • g ω) (probabilityPath m hm T hT n) := by
  have hi := (path_domain_iff m hm T hT n g).mp hg
  apply Integrable.mono'
    (hi.norm.const_mul ((∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n)))
    ((pathWeight_measurable m hm T hT n).aestronglyMeasurable.smul hi.aestronglyMeasurable)
  exact Eventually.of_forall fun ω => by
    change ‖pathWeight m hm T hT n ω • g ω‖ ≤
      (∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n) * ‖g ω‖
    rw [norm_smul, Real.norm_eq_abs, pathWeight_abs]

theorem pathWeight_mean (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ ω, pathWeight m hm T hT n ω ∂probabilityPath m hm T hT n)=1 := by
  rw [probabilityPath, integral_map (incrementPath_continuous n).measurable.aemeasurable
    (pathWeight_measurable m hm T hT n).aestronglyMeasurable]
  simpa only [pathWeight_incrementPath] using (dyadic_weight_moments m hm T hT n).1

theorem pathWeight_moments (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ ω, |pathWeight m hm T hT n ω| ∂probabilityPath m hm T hT n)=
      (∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n) ∧
    (∫ ω, (pathWeight m hm T hT n ω)^2 ∂probabilityPath m hm T hT n)=
      ((∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n))^2 := by
  letI := probabilityPath_isProbability m hm T hT n
  constructor
  · simp only [pathWeight_abs, integral_const, probReal_univ, one_smul]
  · have he : (fun ω => (pathWeight m hm T hT n ω)^2)=
        fun _ => ((∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m hm T hT x‖)^(gridSize n))^2 := by
      funext ω
      rw [← sq_abs, pathWeight_abs]
    rw [he, integral_const, probReal_univ, one_smul]

theorem pathWeight_escape (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) (B : ℝ) :
    ∃ N, ∀ n, N ≤ n → ∀ ω : Path, B < |pathWeight m (by omega) T hT n ω| := by
  let C : ℝ := ∫ x : ℝ, ‖HigherHeatSignedLaws.realKernel m (by omega : 0 < m) T hT x‖
  have hC : 1 < C := HigherHeatKernelMoments.norm_integral_gt_one m hm T hT
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt B hC
  refine ⟨N, fun n hn ω => ?_⟩
  rw [pathWeight_abs]
  exact hN.trans_le (pow_le_pow_right₀ hC.le (hn.trans (level_le_size n)))

theorem no_pathWeight_limit (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T)
    (ω : ℕ → Path) (z : ℝ) :
    ¬ Tendsto (fun n => pathWeight m (by omega) T hT n (ω n)) atTop (𝓝 z) := by
  intro h
  have ha := continuous_abs.continuousAt.tendsto.comp h
  have hhi : ∀ᶠ n in atTop, |pathWeight m (by omega) T hT n (ω n)| < |z|+1 :=
    (tendsto_order.1 ha).2 (|z|+1) (by linarith)
  obtain ⟨N,hN⟩ := pathWeight_escape m hm T hT (|z|+1)
  have hlo : ∀ᶠ n in atTop, |z|+1 < |pathWeight m (by omega) T hT n (ω n)| :=
    eventually_atTop.mpr ⟨N, fun n hn => hN n hn (ω n)⟩
  obtain ⟨n,hnlo,hnhi⟩ := (hlo.and hhi).exists
  exact (not_lt_of_ge hnhi.le) hnlo

end OperatorDerivativeRewrite.Foundation.HigherHeatWeightedPaths
