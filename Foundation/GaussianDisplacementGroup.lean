import Foundation.GaussianCoherentIdentification

/-! Reference independence and real group law for the actual scalar Gaussian displacements. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianDisplacementGroup
open GaussianCore GaussianCoherentIdentification GaussianDisplacementFromPoisson
open PoissonTiltSourceGauge PoissonTiltHellingerGeometry

theorem creation_shift_unique (U V : GaussianL2 ≃ₗᵢ[ℝ] GaussianL2) (d : ℝ)
    (hU : ∀ f g, (f,g)∈closedDivergence.graph → (U f,U g+d • U f)∈closedDivergence.graph)
    (hV : ∀ f g, (f,g)∈closedDivergence.graph → (V f,V g+d • V f)∈closedDivergence.graph)
    (hv : U (normalizedHermite 0)=V (normalizedHermite 0)) : U=V := by
  have hb (n : ℕ) : U (normalizedHermite n)=V (normalizedHermite n) := by
    induction n with
    | zero => exact hv
    | succ n ih =>
      have hg := LinearPMap.le_graph_of_le polynomialDivergence.le_closure (normalizedHermite_divergence_graph n)
      have hu := hU _ _ hg
      have hh := hV _ _ hg
      have he := closedDivergence.mem_graph_snd_inj hu hh ih
      simp only [map_smul,ih] at he
      have hc := add_right_cancel he
      have hs := congrArg (fun f : GaussianL2 => (Real.sqrt (n+1 : ℝ))⁻¹ • f) hc
      have hn : Real.sqrt (n+1 : ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
      simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using hs
  let L := U.toLinearIsometry.toContinuousLinearMap-V.toLinearIsometry.toContinuousLinearMap
  have hs : Submodule.span ℝ (Set.range normalizedHermite)≤L.ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨n,rfl⟩
    change U (normalizedHermite n)-V (normalizedHermite n)=0
    rw [hb,sub_self]
  have hc := (Submodule.span ℝ (Set.range normalizedHermite)).topologicalClosure_minimal hs L.isClosed_ker
  have ht := Submodule.dense_iff_topologicalClosure_eq_top.mp normalizedHermite_dense_span
  rw [ht] at hc
  apply LinearIsometryEquiv.ext
  intro f
  have he := hc (show f∈(⊤ : Submodule ℝ GaussianL2) from trivial)
  change U f-V f=0 at he
  exact sub_eq_zero.mp he

theorem reference_independent (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (rate' : ℝ≥0) (hr' : 0<rate') (θ' : ℝ) (hd : displacement rate θ=displacement rate' θ') :
    gaussianDisplacement rate hr θ=gaussianDisplacement rate' hr' θ' := by
  apply creation_shift_unique _ _ (displacement rate θ)
  · intro f g hg
    exact (displacement_divergence_graph rate hr θ f g).mp hg
  · intro f g hg
    rw [hd]
    exact (displacement_divergence_graph rate' hr' θ' f g).mp hg
  · rw [displacement_vacuum_physical,displacement_vacuum_physical,hd]

theorem eigenvector_of_vacuum_pairing (d : ℝ) (f : GaussianL2)
    (hg : (f,d • f)∈closedDerivative.graph)
    (hm : inner ℝ (normalizedHermite 0) f=Real.exp (-d^2/2)) : f=gaussianRoot d := by
  have he := (gaussian_eigenvector_iff d f).mp hg
  have hi := congrArg (fun g : GaussianL2 => inner ℝ (normalizedHermite 0) g) he
  rw [hm,real_inner_smul_right,gaussianRoot_vacuum_pairing] at hi
  have hc : inner ℝ (gaussianRoot d) f=1 := by nlinarith [Real.exp_pos (-d^2/2)]
  rwa [hc,one_smul] at he

theorem inverse_vacuum_physical (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) :
    (gaussianDisplacement rate hr θ).symm (normalizedHermite 0)=gaussianRoot (-displacement rate θ) := by
  let U := gaussianDisplacement rate hr θ
  let d := displacement rate θ
  have hz : (normalizedHermite 0,(0 : GaussianL2))∈closedDerivative.graph :=
    LinearPMap.le_graph_of_le polynomialDerivative.le_closure normalizedHermite_derivative_zero_graph
  have hg : (U.symm (normalizedHermite 0),(-d) • U.symm (normalizedHermite 0))∈closedDerivative.graph := by
    apply (displacement_derivative_graph rate hr θ _ _).mpr
    simpa only [U,d,map_smul,map_neg,LinearIsometryEquiv.apply_symm_apply,neg_smul,neg_add_cancel] using hz
  apply eigenvector_of_vacuum_pairing (-d) _ hg
  have hi := U.inner_map_map (normalizedHermite 0) (U.symm (normalizedHermite 0))
  rw [LinearIsometryEquiv.apply_symm_apply] at hi
  change inner ℝ (gaussianDisplacement rate hr θ (normalizedHermite 0)) (normalizedHermite 0)=_ at hi
  rw [displacement_vacuum_physical,real_inner_comm,gaussianRoot_vacuum_pairing] at hi
  simpa only [d,neg_sq] using hi.symm

theorem composed_vacuum_physical (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (rate' : ℝ≥0) (hr' : 0<rate') (θ' : ℝ) :
    gaussianDisplacement rate hr θ (gaussianDisplacement rate' hr' θ' (normalizedHermite 0))=
      gaussianRoot (displacement rate θ+displacement rate' θ') := by
  let U := gaussianDisplacement rate hr θ
  let V := gaussianDisplacement rate' hr' θ'
  let d := displacement rate θ
  let e := displacement rate' θ'
  have hv : (V (normalizedHermite 0),e • V (normalizedHermite 0))∈closedDerivative.graph := by
    rw [show V (normalizedHermite 0)=gaussianRoot e from displacement_vacuum_physical rate' hr' θ']
    exact gaussianRoot_derivative_graph e
  have hh := (displacement_derivative_graph rate hr θ _ _).mp hv
  have hg : (U (V (normalizedHermite 0)),(d+e) • U (V (normalizedHermite 0)))∈closedDerivative.graph := by
    simpa only [U,d,map_smul,add_smul,add_comm] using hh
  apply eigenvector_of_vacuum_pairing (d+e) _ hg
  have hi := U.inner_map_map (U.symm (normalizedHermite 0)) (V (normalizedHermite 0))
  rw [LinearIsometryEquiv.apply_symm_apply] at hi
  change inner ℝ (normalizedHermite 0) (U (V (normalizedHermite 0)))=_ at hi
  rw [inverse_vacuum_physical,displacement_vacuum_physical,gaussianRoot_inner] at hi
  rw [show V (normalizedHermite 0)=gaussianRoot e from displacement_vacuum_physical rate' hr' θ']
  rw [hi]
  congr 1
  dsimp [d,e]
  ring

theorem displacement_group_law (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (rate' : ℝ≥0) (hr' : 0<rate') (θ' : ℝ)
    (rate'' : ℝ≥0) (hr'' : 0<rate'') (θ'' : ℝ)
    (hd : displacement rate'' θ''=displacement rate θ+displacement rate' θ') :
    (gaussianDisplacement rate' hr' θ').trans (gaussianDisplacement rate hr θ)=
      gaussianDisplacement rate'' hr'' θ'' := by
  let U := gaussianDisplacement rate hr θ
  let V := gaussianDisplacement rate' hr' θ'
  let d := displacement rate θ
  let e := displacement rate' θ'
  apply creation_shift_unique _ _ (d+e)
  · intro f g hg
    have hv := (displacement_divergence_graph rate' hr' θ' f g).mp hg
    have hu := (displacement_divergence_graph rate hr θ _ _).mp hv
    change (U (V f),U (V g+e • V f)+d • U (V f))∈closedDivergence.graph at hu
    rw [map_add,map_smul] at hu
    have he : U (V g)+e • U (V f)+d • U (V f)=U (V g)+(d+e) • U (V f) := by module
    rw [he] at hu
    exact hu
  · intro f g hg
    rw [show d+e=displacement rate'' θ'' from hd.symm]
    exact (displacement_divergence_graph rate'' hr'' θ'' f g).mp hg
  · change U (V (normalizedHermite 0))=gaussianDisplacement rate'' hr'' θ'' (normalizedHermite 0)
    rw [composed_vacuum_physical,displacement_vacuum_physical,hd]

theorem zero_displacement_identity (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (hd : displacement rate θ=0) :
    gaussianDisplacement rate hr θ=LinearIsometryEquiv.refl ℝ GaussianL2 := by
  apply creation_shift_unique _ _ 0
  · intro f g hg
    have hh := (displacement_divergence_graph rate hr θ f g).mp hg
    simpa only [hd,zero_smul,add_zero] using hh
  · intro f g hg
    change (f,g+(0 : ℝ) • f)∈closedDivergence.graph
    simpa only [zero_smul,add_zero] using hg
  · rw [displacement_vacuum_physical,hd,← gaussian_vacuum_root]
    rfl

end OperatorDerivativeRewrite.Foundation.GaussianDisplacementGroup
