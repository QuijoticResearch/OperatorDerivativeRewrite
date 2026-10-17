import Foundation.HelicalRadialGaussianBridge
import Foundation.GaussianQuadraticMatrixContraction

/-! Exact pressure-candidate pairing, with Gaussian sector and derivative domains explicit. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.HelicalPressureProjection
set_option backward.isDefEq.respectTransparency false
open InfiniteGaussian GaussianNumberSectors GaussianQuadraticSourceHodge
open GaussianDivergenceRecovery HelicalRadialGaussianBridge

theorem radial_mem_two : radialTarget ∈ sector 2 :=
  (sector 2).smul_mem (1/2 : ℝ)
    (GaussianQuadraticMatrixContraction.quadraticTarget_mem_two directions
      (1 : Matrix (Fin 2) (Fin 2) ℝ))

theorem radial_projection_fix : projection 2 radialTarget=radialTarget :=
  projection_fix 2 ⟨_, radial_mem_two⟩

theorem radial_norm : ‖radialTarget‖=1 := by
  nlinarith [radialTarget_energy, norm_nonneg radialTarget]

def response (p : GaussianL2) : ℝ := inner ℝ radialTarget p
def responseCLM : GaussianL2 →L[ℝ] ℝ := innerSL ℝ radialTarget

theorem responseCLM_apply (p : GaussianL2) : responseCLM p=response p := rfl

theorem responseCLM_norm : ‖responseCLM‖=1 := by
  rw [responseCLM, innerSL_apply_norm, radial_norm]

theorem response_projection (p : GaussianL2) : response p=response (projection 2 p) := by
  have hi := (sector 2).inner_starProjection_left_eq_right radialTarget p
  change inner ℝ (projection 2 radialTarget) p=inner ℝ radialTarget (projection 2 p) at hi
  rw [radial_projection_fix] at hi
  exact hi

theorem response_bound (p : GaussianL2) : |response p| ≤ ‖projection 2 p‖ := by
  rw [response_projection, response]
  simpa only [radial_norm, one_mul] using abs_real_inner_le_norm radialTarget (projection 2 p)

theorem response_bound_full (p : GaussianL2) : |response p| ≤ ‖p‖ :=
  (response_bound p).trans (projection_norm_le 2 p)

theorem response_self : response radialTarget=1 := by
  rw [response, real_inner_self_eq_norm_sq, radialTarget_energy]

theorem response_neg_self : response (-radialTarget)=-1 := by
  rw [response, inner_neg_right]
  exact congrArg Neg.neg response_self

theorem opposite_unit_responses :
    ∃ p q : GaussianL2, ‖p‖=1 ∧ ‖q‖=1 ∧ response p=1 ∧ response q=-1 :=
  ⟨radialTarget, -radialTarget, radial_norm, by simpa using radial_norm, response_self, response_neg_self⟩

theorem response_other_sector (n : ℕ) (hn : n ≠ 2) (p : GaussianL2) (hp : p ∈ sector n) :
    response p=0 := by
  have hi := sectors_orthogonal hn ⟨p, hp⟩ ⟨radialTarget, radial_mem_two⟩
  simpa only [response, real_inner_comm] using hi

theorem response_constant (c : ℝ) : response (c • gaussianOne)=0 := by
  have hm : inner ℝ gaussianOne radialTarget=0 := by
    rw [gaussianOne_inner_eq_integral]
    exact radialTarget_mean_zero
  rw [response, inner_smul_right, ← real_inner_comm radialTarget gaussianOne, hm, mul_zero]

def radialComponent (p : GaussianL2) : GaussianL2 := response p • radialTarget

theorem residual_response_zero (p : GaussianL2) : response (p-radialComponent p)=0 := by
  simp only [response, radialComponent, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, radialTarget_energy, mul_one, sub_self]

theorem radial_pythagoras (p : GaussianL2) :
    ‖p‖^2=(response p)^2+‖p-radialComponent p‖^2 := by
  rw [radialComponent, norm_sub_sq_real, norm_smul, mul_pow, radialTarget_energy]
  simp only [Real.norm_eq_abs, sq_abs, inner_smul_right, real_inner_comm radialTarget p]
  change ‖p‖^2=(response p)^2+(‖p‖^2-2*(response p*response p)+(response p)^2*1)
  ring

theorem radial_divergence_graph : (recovery radialTarget,radialTarget) ∈ hilbertDivergence.graph := by
  have hi : inner ℝ gaussianOne radialTarget=0 := by
    rw [gaussianOne_inner_eq_integral]
    exact radialTarget_mean_zero
  have hg := recovery_graph radialTarget
  rw [projection_zero, hi, zero_smul, sub_zero] at hg
  exact hg

/-- Derivative duality is asserted only for the actual closed derivative graph. -/
theorem response_derivative_duality {p : GaussianL2} {g : GaussianVectorL2}
    (hp : (p,g) ∈ closedCylindricalDerivative.graph) :
    response p=inner ℝ g (recovery radialTarget) := by
  have hi := graph_duality hp radial_divergence_graph
  simpa only [response, real_inner_comm radialTarget p] using hi.symm

theorem response_derivative_bound {p : GaussianL2} {g : GaussianVectorL2}
    (hp : (p,g) ∈ closedCylindricalDerivative.graph) : (response p)^2 ≤ ‖g‖^2/2 := by
  rw [response_derivative_duality hp]
  have hi := abs_real_inner_le_norm g (recovery radialTarget)
  have hs := (sq_le_sq₀ (abs_nonneg (inner ℝ g (recovery radialTarget))) (by positivity)).mpr hi
  rw [sq_abs, mul_pow, radial_recovery_energy] at hs
  nlinarith

def radialGradient : GaussianVectorL2 := linearField directions (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem radial_derivative_graph : (radialTarget,radialGradient) ∈ closedCylindricalDerivative.graph := by
  have hg := quadraticTarget_derivative_graph directions (1 : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.transpose_one] at hg
  have hs := closedCylindricalDerivative.graph.smul_mem (1/2 : ℝ) hg
  change ((1/2 : ℝ) • quadraticTarget directions (1 : Matrix (Fin 2) (Fin 2) ℝ),
    (1/2 : ℝ) • (radialGradient+radialGradient)) ∈ closedCylindricalDerivative.graph at hs
  have he : (1/2 : ℝ) • (radialGradient+radialGradient)=radialGradient := by module
  simpa only [he, radialTarget] using hs

theorem radialGradient_energy : ‖radialGradient‖^2=2 := by
  have he := linearField_energy directions directions_orthonormal (1 : Matrix (Fin 2) (Fin 2) ℝ)
  norm_num [Fin.sum_univ_two] at he
  exact he

theorem derivative_bound_attained : (response radialTarget)^2=‖radialGradient‖^2/2 := by
  rw [response_self, radialGradient_energy]
  norm_num

abbrev PhysicalL2 := Lp ℝ 2 physicalGaussian

def coordinates (ω : SampleSpace) : ℝ × ℝ :=
  (firstChaosEmbedding (directions 0) ω/2, firstChaosEmbedding (directions 1) ω/2)

theorem coordinates_preserving : MeasurePreserving coordinates gaussianProduct physicalGaussian :=
  ⟨by unfold coordinates; fun_prop, scaled_pair_law.map_eq⟩

def physicalPullback : PhysicalL2 →ₗᵢ[ℝ] GaussianL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ coordinates coordinates_preserving

theorem physical_radial_memLp : MemLp (fun p : ℝ × ℝ => radial p.1 p.2) 2 physicalGaussian := by
  have hi : MemLp (fun ω => radial (firstChaosEmbedding (directions 0) ω/2)
      (firstChaosEmbedding (directions 1) ω/2)) 2 gaussianProduct :=
    (memLp_congr_ae radialTarget_ae).mp (Lp.memLp radialTarget)
  rw [← coordinates_preserving.map_eq]
  exact (memLp_map_measure_iff (by unfold radial; fun_prop) coordinates_preserving.measurable.aemeasurable).mpr hi

def physicalRadial : PhysicalL2 := physical_radial_memLp.toLp (fun p => radial p.1 p.2)

theorem physicalRadial_ae : physicalRadial =ᵐ[physicalGaussian] fun p => radial p.1 p.2 :=
  physical_radial_memLp.coeFn_toLp

theorem pullback_radial : physicalPullback physicalRadial=radialTarget := by
  apply Lp.ext
  have ha := coordinates_preserving.quasiMeasurePreserving.ae_eq_comp physicalRadial_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving physicalRadial coordinates_preserving,
    ha, radialTarget_ae] with ω hc hp hr
  change Lp.compMeasurePreserving coordinates coordinates_preserving physicalRadial ω=radialTarget ω
  rw [hc, hp]
  exact hr.symm

def physicalResponse (p : PhysicalL2) : ℝ := inner ℝ physicalRadial p

theorem physicalResponse_transport (p : PhysicalL2) : physicalResponse p=response (physicalPullback p) := by
  have hi := physicalPullback.inner_map_map physicalRadial p
  rw [pullback_radial] at hi
  exact hi.symm

theorem physical_product_integrable (p : PhysicalL2) :
    Integrable (fun x : ℝ × ℝ => radial x.1 x.2*p x) physicalGaussian :=
  physical_radial_memLp.integrable_mul (Lp.memLp p)

theorem physicalResponse_integral (p : PhysicalL2) :
    physicalResponse p=∫ x : ℝ × ℝ, radial x.1 x.2*p x ∂physicalGaussian := by
  rw [physicalResponse, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [physicalRadial_ae] with x hx
  rw [hx]
  exact Real.inner_apply _ _

theorem physicalResponse_bound (p : PhysicalL2) : |physicalResponse p| ≤ ‖p‖ := by
  rw [physicalResponse_transport]
  simpa only [physicalPullback.norm_map] using response_bound_full (physicalPullback p)

theorem physicalResponse_self : physicalResponse physicalRadial=1 := by
  rw [physicalResponse_transport, pullback_radial, response_self]

theorem physicalResponse_neg_self : physicalResponse (-physicalRadial)=-1 := by
  rw [physicalResponse_transport, map_neg, pullback_radial, response_neg_self]

theorem physicalRadial_norm : ‖physicalRadial‖=1 := by
  have hi := physicalPullback.norm_map physicalRadial
  rw [pullback_radial, radial_norm] at hi
  exact hi.symm

theorem physicalResponse_derivative_duality (p : PhysicalL2) {g : GaussianVectorL2}
    (hp : (physicalPullback p,g) ∈ closedCylindricalDerivative.graph) :
    physicalResponse p=inner ℝ g (recovery radialTarget) := by
  rw [physicalResponse_transport]
  exact response_derivative_duality hp

theorem weighted_pressure_integrable (p : PhysicalL2) :
    Integrable (fun x : ℝ × ℝ => (HelicalVorticityDiagnostics.profile x.1 x.2)^2*
      (radial x.1 x.2*p x)) (volume.prod volume) := by
  let F : ℝ × ℝ → ℝ := fun x => radial x.1 x.2*p x
  have hi : Integrable F physicalGaussian := physical_product_integrable p
  rw [physicalGaussian_density] at hi
  have hw := (integrable_withDensity_iff_integrable_smul'
    (by unfold HelicalVorticityDiagnostics.profile; fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
  have hn (x : ℝ × ℝ) : 0 ≤ (2/Real.pi)*(HelicalVorticityDiagnostics.profile x.1 x.2)^2 := by positivity
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul] at hw
  change Integrable (fun x : ℝ × ℝ => (HelicalVorticityDiagnostics.profile x.1 x.2)^2*F x) (volume.prod volume)
  apply (hw.const_mul (Real.pi/2)).congr
  exact Filter.Eventually.of_forall fun x => by field_simp [Real.pi_ne_zero] <;> ring

theorem weighted_pressure_integral (p : PhysicalL2) :
    (∫ x : ℝ × ℝ, (HelicalVorticityDiagnostics.profile x.1 x.2)^2*(radial x.1 x.2*p x)
      ∂volume.prod volume)=(Real.pi/2)*physicalResponse p := by
  let F : ℝ × ℝ → ℝ := fun x => radial x.1 x.2*p x
  have hi : physicalResponse p=∫ x, F x ∂physicalGaussian := physicalResponse_integral p
  rw [physicalGaussian_density, integral_withDensity_eq_integral_toReal_smul
    (by unfold HelicalVorticityDiagnostics.profile; fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hi
  have hn (x : ℝ × ℝ) : 0 ≤ (2/Real.pi)*(HelicalVorticityDiagnostics.profile x.1 x.2)^2 := by positivity
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul, mul_assoc] at hi
  rw [integral_const_mul] at hi
  change (∫ x : ℝ × ℝ, (HelicalVorticityDiagnostics.profile x.1 x.2)^2*F x ∂volume.prod volume)=_
  rw [hi]
  field_simp [Real.pi_ne_zero]

def leadingPressure (ε : ℝ) (p : PhysicalL2) : ℝ :=
  ∫ x : ℝ × ℝ, p x*(8*Real.pi*ε^2*(HelicalVorticityDiagnostics.profile x.1 x.2)^2*radial x.1 x.2)
    ∂volume.prod volume

theorem leadingPressure_integrable (ε : ℝ) (p : PhysicalL2) :
    Integrable (fun x : ℝ × ℝ =>
      p x*(8*Real.pi*ε^2*(HelicalVorticityDiagnostics.profile x.1 x.2)^2*radial x.1 x.2))
        (volume.prod volume) := by
  apply ((weighted_pressure_integrable p).const_mul (8*Real.pi*ε^2)).congr
  exact Filter.Eventually.of_forall fun x => by ring

theorem leadingPressure_period_trace (ε : ℝ) (p : PhysicalL2) :
    leadingPressure ε p=∫ x : ℝ × ℝ, p x*(∫ z in (0:ℝ)..(2*Real.pi),
      Matrix.trace (correctedJacobian ε x.1 x.2 z*correctedJacobian ε x.1 x.2 z)) ∂volume.prod volume := by
  simp_rw [corrected_period_integral]
  rfl

theorem leadingPressure_formula (ε : ℝ) (p : PhysicalL2) :
    leadingPressure ε p=4*Real.pi^2*ε^2*physicalResponse p := by
  have he (x : ℝ × ℝ) : p x*(8*Real.pi*ε^2*(HelicalVorticityDiagnostics.profile x.1 x.2)^2*radial x.1 x.2)=
      (8*Real.pi*ε^2)*((HelicalVorticityDiagnostics.profile x.1 x.2)^2*(radial x.1 x.2*p x)) := by ring
  unfold leadingPressure
  simp_rw [he]
  rw [integral_const_mul, weighted_pressure_integral]
  ring

theorem leadingPressure_self (ε : ℝ) : leadingPressure ε physicalRadial=4*Real.pi^2*ε^2 := by
  rw [leadingPressure_formula, physicalResponse_self, mul_one]

theorem leadingPressure_neg_self (ε : ℝ) : leadingPressure ε (-physicalRadial)=-(4*Real.pi^2*ε^2) := by
  rw [leadingPressure_formula, physicalResponse_neg_self]
  ring

end OperatorDerivativeRewrite.Foundation.HelicalPressureProjection
