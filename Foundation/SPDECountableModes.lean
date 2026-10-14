import Foundation.SPDETemporalIncrements
import Foundation.GaussianFirstChaosRecovery
import Mathlib.MeasureTheory.Measure.Count

/-! Countable independent forcing modes and their exact actual L2 criterion. -/
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.SPDECountableModes
open GaussianTimeHilbert GaussianHilbertProcess InfiniteGaussian SPDEModulatedResponse
attribute [local instance] timeHilbert_secondCountable

abbrev ModeHilbert := Lp TimeHilbert 2 (Measure.count : Measure ℕ)

instance modeHilbert_secondCountable : SecondCountableTopology ModeHilbert := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

def modeVector (n : ℕ) (v : TimeHilbert) : ModeHilbert :=
  indicatorConstLp 2 (measurableSet_singleton n) (by simp) v

theorem modeVector_apply (n k : ℕ) (v : TimeHilbert) :
    modeVector n v k=if k=n then v else 0 := by
  have he : modeVector n v =ᵐ[Measure.count] ({n} : Set ℕ).indicator (fun _ => v) :=
    indicatorConstLp_coeFn
  simpa only [Set.indicator_apply,Set.mem_singleton_iff] using (Measure.ae_count_iff.mp he k)

def modeEmbedding (n : ℕ) : TimeHilbert →ₗᵢ[ℝ] ModeHilbert where
  toFun := modeVector n
  map_add' v w := by simp only [modeVector,indicatorConstLp_add]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul c (modeVector n v)] with k hk
    change modeVector n (c • v) k=(c • modeVector n v) k
    rw [hk]
    simp only [Pi.smul_apply,modeVector_apply]
    by_cases h : k=n <;> simp [h]
  norm_map' v := by
    change ‖modeVector n v‖=‖v‖
    rw [modeVector,norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp

theorem modeVector_inner (n m : ℕ) (v w : TimeHilbert) :
    inner ℝ (modeVector n v) (modeVector m w)=if n=m then inner ℝ v w else 0 := by
  rw [modeVector,L2.inner_indicatorConstLp_eq_setIntegral_inner]
  rw [integral_singleton]
  simp only [Measure.count_singleton,ENNReal.toReal_one,one_smul,modeVector_apply]
  by_cases h : n=m <;> simp [h]

def gaussianMode (n : ℕ) : TimeHilbert →ₗᵢ[ℝ] GaussianL2 :=
  (isonormalEmbedding ModeHilbert).comp (modeEmbedding n)

theorem gaussianModes_orthogonal :
    OrthogonalFamily ℝ (fun _ : ℕ => TimeHilbert) gaussianMode := by
  intro n m hnm v w
  change inner ℝ (isonormalEmbedding ModeHilbert (modeVector n v))
    (isonormalEmbedding ModeHilbert (modeVector m w))=0
  rw [LinearIsometry.inner_map_map,modeVector_inner,if_neg hnm]

theorem gaussianSeries_summable_iff (c : ℕ → ℝ) (v : ℕ → TimeHilbert) :
    Summable (fun n => c n • gaussianMode n (v n)) ↔
      Summable (fun n => (c n)^2*‖v n‖^2) := by
  simpa only [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] using
    gaussianModes_orthogonal.summable_iff_norm_sq_summable (fun n => c n • v n)

def infiniteResponse (c : ℕ → ℝ) (v : ℕ → TimeHilbert) : GaussianL2 :=
  ∑' n, c n • gaussianMode n (v n)

theorem infiniteResponse_hasSum (c : ℕ → ℝ) (v : ℕ → TimeHilbert)
    (hs : Summable (fun n => (c n)^2*‖v n‖^2)) :
    HasSum (fun n => c n • gaussianMode n (v n)) (infiniteResponse c v) :=
  ((gaussianSeries_summable_iff c v).mpr hs).hasSum

theorem infiniteResponse_energy (c : ℕ → ℝ) (v : ℕ → TimeHilbert)
    (hs : Summable (fun n => (c n)^2*‖v n‖^2)) :
    HasSum (fun n => (c n)^2*‖v n‖^2) (‖infiniteResponse c v‖^2) := by
  have ht := (infiniteResponse_hasSum c v hs).norm.pow 2
  change Tendsto (fun s : Finset ℕ => ‖∑ n ∈ s, c n • gaussianMode n (v n)‖^2)
    atTop (𝓝 (‖infiniteResponse c v‖^2)) at ht
  change Tendsto (fun s : Finset ℕ => ∑ n ∈ s, (c n)^2*‖v n‖^2)
    atTop (𝓝 (‖infiniteResponse c v‖^2))
  have he (s : Finset ℕ) :
      ‖∑ n ∈ s, c n • gaussianMode n (v n)‖^2=∑ n ∈ s, (c n)^2*‖v n‖^2 := by
    simpa only [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] using
      gaussianModes_orthogonal.norm_sum (fun n => c n • v n) s
  simpa only [he] using ht

theorem modulatedSeries_summable_iff (α : ℝ) (hα : 1/2 < α) (t : ℝ≥0)
    (g : ℕ → ℝ → ℝ) (hg : ∀ n, Measurable (g n)) (M : ℕ → ℝ)
    (hM : ∀ n s, |g n s| ≤ M n) (c : ℕ → ℝ) :
    Summable (fun n => c n • gaussianMode n (modulatedVector α hα t (g n) (hg n) (M n) (hM n))) ↔
      Summable (fun n => (c n)^2*∫ s, (modulatedResponse α t (g n) s)^2) := by
  rw [gaussianSeries_summable_iff]
  simp only [modulatedVector_energy]

theorem infiniteResponse_firstChaos (c : ℕ → ℝ) (v : ℕ → TimeHilbert)
    (hs : Summable (fun n => (c n)^2*‖v n‖^2)) :
    infiniteResponse c v ∈ firstChaosEmbedding.toLinearMap.range := by
  apply (HilbertRepresentation.isClosed_isometry_range firstChaosEmbedding).mem_of_tendsto
    (infiniteResponse_hasSum c v hs)
  exact Eventually.of_forall fun s => by
    apply firstChaosEmbedding.toLinearMap.range.sum_mem
    intro n _
    rw [← map_smul]
    exact ⟨SeparableHilbertEmbedding.hilbertEmbedding ModeHilbert (modeVector n (c n • v n)),rfl⟩

theorem infiniteResponse_recovery_norm (c : ℕ → ℝ) (v : ℕ → TimeHilbert)
    (hs : Summable (fun n => (c n)^2*‖v n‖^2)) :
    ‖GaussianDivergenceRecovery.recovery (infiniteResponse c v)‖=‖infiniteResponse c v‖ := by
  obtain ⟨h,hh⟩ := infiniteResponse_firstChaos c v hs
  rw [← hh]
  change ‖GaussianDivergenceRecovery.recovery (firstChaosEmbedding h)‖=‖firstChaosEmbedding h‖
  exact GaussianFirstChaosRecovery.recovery_firstChaos_norm h

theorem infiniteResponse_recovery_graph (c : ℕ → ℝ) (v : ℕ → TimeHilbert)
    (hs : Summable (fun n => (c n)^2*‖v n‖^2)) :
    (GaussianDivergenceRecovery.recovery (infiniteResponse c v),infiniteResponse c v) ∈
      hilbertDivergence.graph := by
  obtain ⟨h,hh⟩ := infiniteResponse_firstChaos c v hs
  rw [← hh]
  change (GaussianDivergenceRecovery.recovery (firstChaosEmbedding h),firstChaosEmbedding h) ∈ _
  rw [GaussianFirstChaosRecovery.recovery_firstChaos]
  exact GaussianFirstChaosRecovery.firstChaos_divergence_graph h

def brownianMode (n : ℕ) (t : ℝ≥0) (ω : SampleSpace) : ℝ :=
  isonormal ModeHilbert (modeVector n (timeVector t)) ω

theorem brownianModes_jointGaussian : ProbabilityTheory.IsGaussianProcess
    (fun p : (_ : ℕ) × ℝ≥0 => brownianMode p.1 p.2) gaussianProduct :=
  isonormal_isGaussianProcess.comp_right
    (fun p : (_ : ℕ) × ℝ≥0 => modeVector p.1 (timeVector p.2))

theorem brownianModes_independent :
    ProbabilityTheory.iIndepFun (fun n ω t => brownianMode n t ω) gaussianProduct := by
  apply ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_eq_zero
    (T := ℕ) (S := fun _ => ℝ≥0) (P := gaussianProduct)
    (X := fun n t => brownianMode n t) brownianModes_jointGaussian
  · intro n t
    exact (isonormal_measurable _).aemeasurable
  · intro n m hnm s t
    change cov[isonormal ModeHilbert (modeVector n (timeVector s)),
      isonormal ModeHilbert (modeVector m (timeVector t)); gaussianProduct]=0
    rw [isonormal_covariance,modeVector_inner]
    simp [hnm]

theorem finiteResponse_energy (c : ℕ → ℝ) (v : ℕ → TimeHilbert) (s : Finset ℕ) :
    ‖∑ n ∈ s, c n • gaussianMode n (v n)‖^2=∑ n ∈ s, (c n)^2*‖v n‖^2 := by
  simpa only [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] using
    gaussianModes_orthogonal.norm_sum (fun n => c n • v n) s

theorem brownian_unit_modes_not_summable :
    ¬ Summable (fun n => gaussianMode n (timeVector 1)) := by
  have he := gaussianSeries_summable_iff (fun _ => (1 : ℝ)) (fun _ => timeVector 1)
  intro hs
  have hc : Summable (fun _ : ℕ => (1 : ℝ)) := by
    simpa [timeVector_norm_sq] using he.mp (by simpa using hs)
  have hz : (1 : ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds hc.tendsto_atTop_zero
  norm_num at hz

theorem brownian_unit_cutoff_energy (N : ℕ) :
    ‖∑ n ∈ Finset.range N, gaussianMode n (timeVector 1)‖^2=(N : ℝ) := by
  have he := finiteResponse_energy (fun _ => (1 : ℝ)) (fun _ => timeVector 1) (Finset.range N)
  simpa [timeVector_norm_sq] using he

end OperatorDerivativeRewrite.Foundation.SPDECountableModes
