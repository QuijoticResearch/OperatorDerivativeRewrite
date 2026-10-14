import Foundation.PoissonTiltSourceGauge
import Foundation.PoissonSpectralGraphs

/-! Actual scalar Gaussian coherent graph displacements reconstructed from
the physical Poisson half-density gauge and complete closed-graph transfer. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianDisplacementFromPoisson
open PoissonDifferenceOperators PoissonWeightedScalarGeometry PoissonCharlierHilbertBasis PoissonSpectralGraphs
open PoissonExponentialTilt PoissonTiltHellingerGeometry PoissonTiltSourceGauge

theorem annihilation_scalar_transfer (rate : ℝ≥0) (hr : 0<rate) (f g : ScalarL2 rate) :
    annihilationGraph rate hr f g ↔
      (gaussianTransfer rate hr f,gaussianTransfer rate hr g)∈GaussianCore.closedDerivative.graph := by
  rw [annihilationGraph,difference_transfer_iff,fieldGaussianTransfer,LinearIsometryEquiv.trans_apply]
  have hs : weightedScalarEquiv rate hr (toField rate g)=g := (weightedScalarEquiv rate hr).apply_symm_apply g
  rw [hs]

theorem creation_scalar_transfer (rate : ℝ≥0) (hr : 0<rate) (f g : ScalarL2 rate) :
    creationGraph rate hr f g ↔
      (gaussianTransfer rate hr f,gaussianTransfer rate hr g)∈GaussianCore.closedDivergence.graph := by
  rw [creationGraph,divergence_transfer_iff,fieldGaussianTransfer,LinearIsometryEquiv.trans_apply]
  have hs : weightedScalarEquiv rate hr (toField rate f)=f := (weightedScalarEquiv rate hr).apply_symm_apply f
  rw [hs]

def gaussianDisplacement (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) :
    GaussianCore.GaussianL2 ≃ₗᵢ[ℝ] GaussianCore.GaussianL2 :=
  ((gaussianTransfer (tiltedRate rate θ) (tiltedRate_pos rate hr θ)).symm.trans (gauge rate θ)).trans
    (gaussianTransfer rate hr)

theorem displacement_derivative_graph (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (f g : GaussianCore.GaussianL2) :
    (f,g)∈GaussianCore.closedDerivative.graph ↔
      (gaussianDisplacement rate hr θ f,
        gaussianDisplacement rate hr θ g+displacement rate θ • gaussianDisplacement rate hr θ f)
        ∈GaussianCore.closedDerivative.graph := by
  let Q := gaussianTransfer (tiltedRate rate θ) (tiltedRate_pos rate hr θ)
  have ht := annihilation_gauge_iff rate hr θ (Q.symm f) (Q.symm g)
  rw [annihilation_scalar_transfer,annihilation_scalar_transfer] at ht
  simp only [Q,LinearIsometryEquiv.apply_symm_apply,map_add,map_smul] at ht
  exact ht

theorem displacement_divergence_graph (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (f g : GaussianCore.GaussianL2) :
    (f,g)∈GaussianCore.closedDivergence.graph ↔
      (gaussianDisplacement rate hr θ f,
        gaussianDisplacement rate hr θ g+displacement rate θ • gaussianDisplacement rate hr θ f)
        ∈GaussianCore.closedDivergence.graph := by
  let Q := gaussianTransfer (tiltedRate rate θ) (tiltedRate_pos rate hr θ)
  have ht := creation_gauge_iff rate hr θ (Q.symm f) (Q.symm g)
  rw [creation_scalar_transfer,creation_scalar_transfer] at ht
  simp only [Q,LinearIsometryEquiv.apply_symm_apply,map_add,map_smul] at ht
  exact ht

theorem exists_positive_reference_displacement (d : ℝ) :
    ∃ rate : ℝ≥0, ∃ hr : 0<rate, ∃ θ : ℝ, displacement rate θ=d := by
  let b := |d|+1
  have hb : 0<b := by dsimp [b]; positivity
  have ha : 0<b+d := by dsimp [b]; nlinarith [neg_abs_le d]
  let rate : ℝ≥0 := ⟨b^2,sq_nonneg b⟩
  have hr : 0<rate := by change (0 : ℝ)<b^2; positivity
  let s := (b+d)/b
  have hs : 0<s := div_pos ha hb
  let θ := 2*Real.log s
  refine ⟨rate,hr,θ, ?_⟩
  have hroot : Real.sqrt (rate : ℝ)=b := by
    change Real.sqrt (b^2)=b
    rw [Real.sqrt_sq_eq_abs,abs_of_pos hb]
  have he : Real.exp (θ/2)=s := by
    rw [show θ/2=Real.log s by dsimp [θ]; ring,Real.exp_log hs]
  rw [displacement,← sqrtRate_eq_sqrt_tilted,sqrtRate,hroot,he]
  change b*((b+d)/b)-b=d
  field_simp
  ring

theorem exists_gaussian_graph_displacement (d : ℝ) :
    ∃ U : GaussianCore.GaussianL2 ≃ₗᵢ[ℝ] GaussianCore.GaussianL2,
      (∀ f g : GaussianCore.GaussianL2, (f,g)∈GaussianCore.closedDerivative.graph ↔
        (U f,U g+d • U f)∈GaussianCore.closedDerivative.graph) ∧
      (∀ f g : GaussianCore.GaussianL2, (f,g)∈GaussianCore.closedDivergence.graph ↔
        (U f,U g+d • U f)∈GaussianCore.closedDivergence.graph) := by
  obtain ⟨rate,hr,θ,hd⟩ := exists_positive_reference_displacement d
  refine ⟨gaussianDisplacement rate hr θ, ?_, ?_⟩
  · intro f g
    simpa only [hd] using displacement_derivative_graph rate hr θ f g
  · intro f g
    simpa only [hd] using displacement_divergence_graph rate hr θ f g

end OperatorDerivativeRewrite.Foundation.GaussianDisplacementFromPoisson
