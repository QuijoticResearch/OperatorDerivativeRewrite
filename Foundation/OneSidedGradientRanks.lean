import Foundation.OneSidedCapPoincare

/-! Connectedness by ordered paths, constant gradient kernel and full ranks. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedGradientRanks
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedCapComplex
  CubePathPoincare OneSidedCapPoincare
set_option maxRecDepth 65536
set_option maxHeartbeats 128000000
set_option backward.isDefEq.respectTransparency false

def cubeGradient : (Vertex → ℝ) →ₗ[ℝ] EdgeField where
  toFun phi e := phi (shifted e.1 e.2)-phi e.1
  map_add' f g := by funext e; simp only [Pi.add_apply]; ring
  map_smul' c f := by
    funext e
    change c*f (shifted e.1 e.2)-c*f e.1=c*(f (shifted e.1 e.2)-f e.1)
    ring

def centered : (Vertex → ℝ) →ₗ[ℝ] (Vertex → ℝ) where
  toFun phi v := phi v-phi origin
  map_add' f g := by funext v; simp only [Pi.add_apply]; ring
  map_smul' c f := by
    funext v
    change c*f v-c*f origin=c*(f v-f origin)
    ring

def vertexDelta (q v : Vertex) : ℤ := if q=v then 1 else 0

def intGradient (phi : Vertex → ℤ) (e : EdgeData) : ℤ := phi (shifted e.1 e.2)-phi e.1

theorem integer_path_gradient : ∀ q v : Vertex,
    intPath (intGradient (vertexDelta q)) v=vertexDelta q v-vertexDelta q origin := by decide +kernel

theorem gradient_integer (phi : Vertex → ℤ) :
    cubeGradient (fun v => (phi v : ℝ))=(fun e => (intGradient phi e : ℝ)) := by
  funext e
  simp [cubeGradient,intGradient]

theorem path_gradient : pathMap.comp cubeGradient=centered := by
  apply (Pi.basisFun ℝ Vertex).ext
  intro q
  rw [Pi.basisFun_apply]
  have he : (Pi.single q (1 : ℝ) : Vertex → ℝ)=(fun v => (vertexDelta q v : ℝ)) := by
    funext v
    by_cases h : q=v <;> simp [Pi.single_apply,vertexDelta,h,eq_comm]
  rw [he]
  funext v
  change pathMap (cubeGradient (fun x => (vertexDelta q x : ℝ))) v=
    (vertexDelta q v : ℝ)-(vertexDelta q origin : ℝ)
  rw [gradient_integer,pathMap_integer]
  exact_mod_cast integer_path_gradient q v

theorem path_gradient_apply (phi : Vertex → ℝ) (v : Vertex) :
    pathMap (cubeGradient phi) v=phi v-phi origin := by
  have h := congrArg (fun L : (Vertex → ℝ) →ₗ[ℝ] (Vertex → ℝ) => L phi v) path_gradient
  exact h

theorem path_edge_mem : ∀ v : Vertex, ∀ i : Fin 4, (pathPrefix v i,i)∈edges := by decide

theorem gradient_kernel_constant (phi : Potential) (hphi : d0 phi=0) :
    phi=(fun _ => phi (.inl origin)) := by
  let psi : Vertex → ℝ := fun v => phi (.inl v)
  have hg : ∀ e∈edges, cubeGradient psi e=0 := by
    intro e he
    have h := congrFun hphi (.inl ⟨e,he⟩)
    exact h
  have hz (v : Vertex) : pathMap (cubeGradient psi) v=0 := by
    rw [pathMap_apply]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs
    · exact hg _ (path_edge_mem v i)
    · rfl
  have hi (v : Vertex) : phi (.inl v)=phi (.inl origin) := by
    have h := path_gradient_apply psi v
    rw [hz] at h
    dsimp [psi] at h
    linarith
  funext q
  cases q with
  | inl v => exact hi v
  | inr c =>
    have h := congrFun hphi (.inr (.inl c))
    change phi (.inr c)-phi (.inl c.val.1)=0 at h
    rw [sub_eq_zero.mp h,hi c.val.1]

def constantMap : ℝ →ₗ[ℝ] Potential where
  toFun c _ := c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem constantMap_injective : Function.Injective constantMap := by
  intro a b h
  exact congrFun h (.inl origin)

theorem kernel_d0 : LinearMap.ker d0=LinearMap.range constantMap := by
  ext phi
  constructor
  · intro h
    exact ⟨phi (.inl origin),(gradient_kernel_constant phi h).symm⟩
  · rintro ⟨c,rfl⟩
    change d0 (constantMap c)=0
    funext e
    simp [d0,constantMap]

theorem constants_finrank : Module.finrank ℝ (LinearMap.range constantMap)=1 := by
  simpa only [Module.finrank_self] using
    LinearMap.finrank_range_of_inj constantMap_injective

theorem gradient_kernel_finrank : Module.finrank ℝ (LinearMap.ker d0)=1 := by
  rw [kernel_d0,constants_finrank]

theorem potential_finrank : Module.finrank ℝ Potential=48 := by
  rw [Module.finrank_pi,fullVertex_card]

theorem fullField_finrank : Module.finrank ℝ FullField=112 := by
  rw [Module.finrank_pi,fullEdge_card]

theorem gradient_rank : Module.finrank ℝ (LinearMap.range d0)=47 := by
  have h := LinearMap.finrank_range_add_finrank_ker d0
  rw [gradient_kernel_finrank,potential_finrank] at h
  omega

theorem curl_kernel_finrank : Module.finrank ℝ (LinearMap.ker d1)=47 := by
  rw [kernel_eq_range,gradient_rank]

theorem curl_rank : Module.finrank ℝ (LinearMap.range d1)=65 := by
  have h := LinearMap.finrank_range_add_finrank_ker d1
  rw [curl_kernel_finrank,fullField_finrank] at h
  omega

end OperatorDerivativeRewrite.Foundation.OneSidedGradientRanks
