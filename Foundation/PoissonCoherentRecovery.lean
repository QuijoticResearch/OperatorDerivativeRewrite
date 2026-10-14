import Foundation.PoissonTiltSourceGauge
import Foundation.PoissonRecoveryPoincare

/-! Contractive unique source recovery and Poincare relative to the actual
coherent vacuum produced by a physical Poisson half-density gauge. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonCoherentRecovery
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators PoissonCoordinateEvaluation
open PoissonCharlierHilbertBasis PoissonWeightedScalarGeometry PoissonDivergenceRecovery
open PoissonExponentialTilt PoissonTiltHellingerGeometry PoissonTiltSourceGauge

def coherentCentered (rate : ℝ≥0) (θ : ℝ) (f : ScalarL2 rate) : ScalarL2 rate :=
  f-inner ℝ (rootClass rate θ) f • rootClass rate θ

theorem gauge_vacuum (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) :
    gauge rate θ (normalized (tiltedRate rate θ) (tiltedRate_pos rate hr θ) 0)=rootClass rate θ := by
  apply Lp.ext
  filter_upwards [gauge_coeFn rate θ (normalized (tiltedRate rate θ) (tiltedRate_pos rate hr θ) 0),
    rootClass_coeFn rate θ] with n hu hv
  rw [hu,hv,normalized,scalar_smul_apply (tiltedRate rate θ) (tiltedRate_pos rate hr θ),
    PoissonCharlierLadder.scalar_apply]
  simp [normalizer,PoissonCharlierLadder.value_zero]

theorem gauge_zero_coefficient (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (f : ScalarL2 (tiltedRate rate θ)) :
    PoissonDivergenceRecovery.coefficient (tiltedRate rate θ) (tiltedRate_pos rate hr θ) f 0=
      inner ℝ (rootClass rate θ) (gauge rate θ f) := by
  have he := (gauge rate θ).inner_map_map
    (normalized (tiltedRate rate θ) (tiltedRate_pos rate hr θ) 0) f
  rw [gauge_vacuum rate hr θ] at he
  exact he.symm

theorem gauge_centered (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (f : ScalarL2 (tiltedRate rate θ)) :
    gauge rate θ (centered (tiltedRate rate θ) (tiltedRate_pos rate hr θ) f)=
      coherentCentered rate θ (gauge rate θ f) := by
  rw [centered,map_sub,map_smul,gauge_vacuum rate hr θ,gauge_zero_coefficient rate hr θ,coherentCentered]

def coherentRecovery (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : ScalarL2 rate) : ScalarL2 rate :=
  gauge rate θ (toScalar (tiltedRate rate θ) (tiltedRate_pos rate hr θ)
    (recovery (tiltedRate rate θ) (tiltedRate_pos rate hr θ) ((gauge rate θ).symm f)))

def coherentRecoveryOperator (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) : ScalarL2 rate →L[ℝ] ScalarL2 rate :=
  (gauge rate θ).toLinearIsometry.toContinuousLinearMap.comp
    ((weightedScalarEquiv (tiltedRate rate θ) (tiltedRate_pos rate hr θ)).toLinearIsometry.toContinuousLinearMap.comp
      ((recoveryOperator (tiltedRate rate θ) (tiltedRate_pos rate hr θ)).comp
        (gauge rate θ).symm.toLinearIsometry.toContinuousLinearMap))

theorem coherentRecoveryOperator_apply (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : ScalarL2 rate) :
    coherentRecoveryOperator rate hr θ f=coherentRecovery rate hr θ f := rfl

theorem coherentRecovery_graph (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : ScalarL2 rate) :
    creationGraph rate hr (coherentRecovery rate hr θ f)
      (coherentCentered rate θ f+displacement rate θ • coherentRecovery rate hr θ f) := by
  let μ := tiltedRate rate θ
  have hμ : 0<μ := tiltedRate_pos rate hr θ
  let v := recovery μ hμ ((gauge rate θ).symm f)
  have hs : toField μ (toScalar μ hμ v)=v := (weightedScalarEquiv μ hμ).symm_apply_apply v
  have hg : creationGraph μ hμ (toScalar μ hμ v) (centered μ hμ ((gauge rate θ).symm f)) := by
    rw [creationGraph,hs]
    exact recovery_graph μ hμ ((gauge rate θ).symm f)
  have ht := (creation_gauge_iff rate hr θ _ _).mp hg
  rw [gauge_centered rate hr θ,LinearIsometryEquiv.apply_symm_apply] at ht
  exact ht

theorem coherentRecovery_norm_le (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : ScalarL2 rate) :
    ‖coherentRecovery rate hr θ f‖ ≤ ‖f‖ := by
  rw [coherentRecovery,LinearIsometryEquiv.norm_map,toScalar_norm]
  have he := recovery_norm_le (tiltedRate rate θ) (tiltedRate_pos rate hr θ) ((gauge rate θ).symm f)
  simpa only [LinearIsometryEquiv.norm_map] using he

theorem coherentRecovery_unique (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f u : ScalarL2 rate)
    (hu : creationGraph rate hr u (coherentCentered rate θ f+displacement rate θ • u)) :
    u=coherentRecovery rate hr θ f := by
  let μ := tiltedRate rate θ
  have hμ : 0<μ := tiltedRate_pos rate hr θ
  have hn : creationGraph μ hμ ((gauge rate θ).symm u) (centered μ hμ ((gauge rate θ).symm f)) := by
    apply (creation_gauge_iff rate hr θ _ _).mpr
    dsimp only [μ]
    simpa only [gauge_centered rate hr θ,LinearIsometryEquiv.apply_symm_apply] using hu
  have he := recovery_unique μ hμ ((gauge rate θ).symm f) (toField μ ((gauge rate θ).symm u)) hn
  have hs := (weightedScalarEquiv μ hμ).apply_symm_apply ((gauge rate θ).symm u)
  change toScalar μ hμ (toField μ ((gauge rate θ).symm u))=(gauge rate θ).symm u at hs
  have hh := congrArg (fun v => gauge rate θ (toScalar μ hμ v)) he
  rw [hs,LinearIsometryEquiv.apply_symm_apply] at hh
  exact hh

private theorem unshifted_creation_range (rate : ℝ≥0) (hr : 0<rate) (f : ScalarL2 rate) :
    (∃ g : ScalarL2 rate, creationGraph rate hr g f) ↔
      PoissonDivergenceRecovery.coefficient rate hr f 0=0 := by
  rw [← exists_divergence_iff_zero_mode rate hr f]
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨toField rate g,hg⟩
  · rintro ⟨g,hg⟩
    refine ⟨toScalar rate hr g, ?_⟩
    have hs : toField rate (toScalar rate hr g)=g := (weightedScalarEquiv rate hr).symm_apply_apply g
    rw [creationGraph,hs]
    exact hg

theorem coherent_creation_range (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : ScalarL2 rate) :
    (∃ u : ScalarL2 rate, creationGraph rate hr u (f+displacement rate θ • u)) ↔
      inner ℝ (rootClass rate θ) f=0 := by
  let μ := tiltedRate rate θ
  have hμ : 0<μ := tiltedRate_pos rate hr θ
  constructor
  · rintro ⟨u,hu⟩
    have hn : creationGraph μ hμ ((gauge rate θ).symm u) ((gauge rate θ).symm f) := by
      apply (creation_gauge_iff rate hr θ _ _).mpr
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hu
    have hz := (unshifted_creation_range μ hμ _).mp ⟨_,hn⟩
    change PoissonDivergenceRecovery.coefficient (tiltedRate rate θ) (tiltedRate_pos rate hr θ)
      ((gauge rate θ).symm f) 0=0 at hz
    rw [gauge_zero_coefficient rate hr θ,LinearIsometryEquiv.apply_symm_apply] at hz
    exact hz
  · intro hz
    have hn : PoissonDivergenceRecovery.coefficient μ hμ ((gauge rate θ).symm f) 0=0 := by
      change PoissonDivergenceRecovery.coefficient (tiltedRate rate θ) (tiltedRate_pos rate hr θ)
        ((gauge rate θ).symm f) 0=0
      rw [gauge_zero_coefficient rate hr θ,LinearIsometryEquiv.apply_symm_apply]
      exact hz
    obtain ⟨u,hu⟩ := (unshifted_creation_range μ hμ _).mpr hn
    refine ⟨gauge rate θ u, ?_⟩
    have ht := (creation_gauge_iff rate hr θ _ _).mp hu
    simpa only [LinearIsometryEquiv.apply_symm_apply] using ht

theorem coherent_poincare (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f g : ScalarL2 rate)
    (hf : annihilationGraph rate hr f (g+displacement rate θ • f)) :
    ‖coherentCentered rate θ f‖ ≤ ‖g‖ := by
  let μ := tiltedRate rate θ
  have hμ : 0<μ := tiltedRate_pos rate hr θ
  have hn : annihilationGraph μ hμ ((gauge rate θ).symm f) ((gauge rate θ).symm g) := by
    apply (annihilation_gauge_iff rate hr θ _ _).mpr
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hf
  have hp := PoissonRecoveryPoincare.poincare μ hμ hn
  have he : ‖coherentCentered rate θ f‖=‖centered μ hμ ((gauge rate θ).symm f)‖ := by
    rw [← (gauge rate θ).norm_map (centered μ hμ ((gauge rate θ).symm f)),
      gauge_centered rate hr θ,LinearIsometryEquiv.apply_symm_apply]
  have hg : ‖toField μ ((gauge rate θ).symm g)‖=‖g‖ := by
    have hs := (weightedScalarEquiv μ hμ).symm.norm_map ((gauge rate θ).symm g)
    change ‖toField μ ((gauge rate θ).symm g)‖=‖(gauge rate θ).symm g‖ at hs
    rw [LinearIsometryEquiv.norm_map] at hs
    exact hs
  rw [← he,hg] at hp
  exact hp

theorem coherentRecovery_norm_le_centered (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : ScalarL2 rate) :
    ‖coherentRecovery rate hr θ f‖ ≤ ‖coherentCentered rate θ f‖ := by
  rw [coherentRecovery,LinearIsometryEquiv.norm_map,toScalar_norm]
  have hb := PoissonRecoveryPoincare.recovery_norm_le_centered
    (tiltedRate rate θ) (tiltedRate_pos rate hr θ) ((gauge rate θ).symm f)
  have he := gauge_centered rate hr θ ((gauge rate θ).symm f)
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  have hn := congrArg norm he
  rw [LinearIsometryEquiv.norm_map] at hn
  rwa [hn] at hb

theorem coherent_vacuum_annihilation (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) :
    annihilationGraph rate hr (rootClass rate θ) (displacement rate θ • rootClass rate θ) := by
  have hz : toField (tiltedRate rate θ) (0 : ScalarL2 (tiltedRate rate θ))=0 :=
    (weightedScalarEquiv (tiltedRate rate θ) (tiltedRate_pos rate hr θ)).symm.map_zero
  have hg : annihilationGraph (tiltedRate rate θ) (tiltedRate_pos rate hr θ)
      (normalized (tiltedRate rate θ) (tiltedRate_pos rate hr θ) 0) 0 := by
    rw [annihilationGraph,hz]
    exact zero_mode_difference_graph (tiltedRate rate θ) (tiltedRate_pos rate hr θ)
  have ht := (annihilation_gauge_iff rate hr θ _ _).mp hg
  simpa only [map_zero,gauge_vacuum rate hr θ,zero_add] using ht

theorem shifted_annihilation_kernel (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : ScalarL2 rate) :
    annihilationGraph rate hr f (displacement rate θ • f) ↔
      f=inner ℝ (rootClass rate θ) f • rootClass rate θ := by
  constructor
  · intro hf
    have hh : annihilationGraph rate hr f (0+displacement rate θ • f) := by simpa using hf
    have hp := coherent_poincare rate hr θ f 0 hh
    rw [norm_zero] at hp
    have hz : coherentCentered rate θ f=0 := norm_eq_zero.mp (le_antisymm hp (norm_nonneg _))
    exact sub_eq_zero.mp hz
  · intro hf
    let c := inner ℝ (rootClass rate θ) f
    rw [hf]
    have hg := coherent_vacuum_annihilation rate hr θ
    rw [annihilationGraph] at hg ⊢
    have he : toField rate (displacement rate θ • (c • rootClass rate θ))=
        c • toField rate (displacement rate θ • rootClass rate θ) := by
      have hs := (weightedScalarEquiv rate hr).symm.map_smul c (displacement rate θ • rootClass rate θ)
      change toField rate (c • (displacement rate θ • rootClass rate θ))=
        c • toField rate (displacement rate θ • rootClass rate θ) at hs
      simpa only [smul_smul,mul_comm] using hs
    rw [he]
    exact (maximalDifference rate hr).graph.smul_mem c hg

end OperatorDerivativeRewrite.Foundation.PoissonCoherentRecovery
