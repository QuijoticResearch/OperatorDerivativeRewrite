import Foundation.OneSidedSourceRows
import Foundation.OneSidedGradientRanks

/-! The complete boundary-gradient gauge space and its physical quotient. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedBoundaryGauge
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedCapComplex
  OneSidedCapPoincare OneSidedGradientRanks
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

abbrev BoundaryField := Boundary → ℝ

def boundaryPart : FullField →ₗ[ℝ] BoundaryField where
  toFun f b := f (.inr b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def boundaryGradient : Potential →ₗ[ℝ] BoundaryField := boundaryPart.comp d0

def originPotential : Potential := Sum.elim gaugePotential (fun _ => 0)

theorem cap_nonorigin : ∀ c : Cap, c.val.1≠origin := by decide

theorem origin_gradient : d0 originPotential=injectInterior gauge := by
  funext e
  cases e with
  | inl e =>
    change latticeGradient gaugePotential e.val=originField e.val
    exact gauge_is_gradient e e.property
  | inr b =>
    cases b with
    | inl c =>
      change 0-gaugePotential c.val.1=0
      simp [gaugePotential,cap_nonorigin c]
    | inr p => simp [d0,originPotential,source,target,injectInterior]

theorem constant_gradient_zero (c : ℝ) : d0 (constantMap c)=0 := by
  funext e
  simp [d0,constantMap]

theorem boundary_constant_zero (c : ℝ) : boundaryGradient (constantMap c)=0 := by
  change boundaryPart (d0 (constantMap c))=0
  rw [constant_gradient_zero,map_zero]

theorem boundary_origin_zero : boundaryGradient originPotential=0 := by
  change boundaryPart (d0 originPotential)=0
  rw [origin_gradient]
  rfl

theorem boundary_support (phi : Potential) (h : boundaryGradient phi=0) :
    d0 phi=injectInterior (interiorPart (d0 phi)) := by
  funext e
  cases e with
  | inl e => rfl
  | inr b => exact congrFun h b

def planeMap : (ℝ × ℝ) →ₗ[ℝ] Potential where
  toFun a := constantMap a.1+a.2 • originPotential
  map_add' a b := by
    funext q
    change (a.1+b.1)+(a.2+b.2)*originPotential q=
      (a.1+a.2*originPotential q)+(b.1+b.2*originPotential q)
    ring
  map_smul' c a := by
    funext q
    change c*a.1+(c*a.2)*originPotential q=c*(a.1+a.2*originPotential q)
    ring

def anchor : FullVertex := .inr ⟨(![1,0,0,0],0),by decide⟩

theorem planeMap_injective : Function.Injective planeMap := by
  intro a b h
  have ha := congrFun h anchor
  have hb := congrFun h (.inl origin)
  norm_num [planeMap,constantMap,originPotential,anchor,gaugePotential,origin,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul] at ha hb
  apply Prod.ext
  · exact ha
  · linarith

theorem boundary_kernel : LinearMap.ker boundaryGradient=LinearMap.range planeMap := by
  ext phi
  constructor
  · intro hb
    let u : Field := interiorPart (d0 phi)
    have hfull : d0 phi=injectInterior u := boundary_support phi hb
    have hi : incidence u=0 := by
      rw [← d1_interior,← hfull,d1_d0]
    have he : realEnergy (extend u)=0 := (incidence_zero_iff u).mp hi
    let c : ℝ := extend u (origin,0)
    have hu : u=c • gauge := by
      funext e
      have h := kernel_classification (extend u) he e e.property
      simpa only [extend_on,c,OneSidedBlockRank.gauge,Pi.smul_apply,smul_eq_mul] using h
    have hd : d0 phi=c • d0 originPotential := by
      rw [origin_gradient,hfull,hu]
      funext e
      cases e <;> simp [injectInterior]
    have hz : d0 (phi-c • originPotential)=0 := by
      rw [map_sub,map_smul,hd,sub_self]
    let k : ℝ := (phi-c • originPotential) (.inl origin)
    have hc : phi-c • originPotential=constantMap k :=
      gradient_kernel_constant (phi-c • originPotential) hz
    refine ⟨(k,c),?_⟩
    change constantMap k+c • originPotential=phi
    rw [← hc]
    module
  · rintro ⟨a,rfl⟩
    change boundaryGradient (constantMap a.1+a.2 • originPotential)=0
    rw [map_add,map_smul,boundary_constant_zero,boundary_origin_zero]
    simp

theorem plane_finrank : Module.finrank ℝ (LinearMap.range planeMap)=2 := by
  rw [LinearMap.finrank_range_of_inj planeMap_injective]
  simp [Module.finrank_prod]

theorem boundary_kernel_finrank : Module.finrank ℝ (LinearMap.ker boundaryGradient)=2 := by
  rw [boundary_kernel,plane_finrank]

theorem boundary_gradient_rank : Module.finrank ℝ (LinearMap.range boundaryGradient)=46 := by
  have h := LinearMap.finrank_range_add_finrank_ker boundaryGradient
  rw [boundary_kernel_finrank,potential_finrank] at h
  omega

theorem boundaryField_finrank : Module.finrank ℝ BoundaryField=80 := by
  rw [Module.finrank_pi,boundary_card]

theorem boundary_quotient_finrank :
    Module.finrank ℝ (BoundaryField ⧸ LinearMap.range boundaryGradient)=34 := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range boundaryGradient)
  rw [boundary_gradient_rank,boundaryField_finrank] at h
  omega

end OperatorDerivativeRewrite.Foundation.OneSidedBoundaryGauge
