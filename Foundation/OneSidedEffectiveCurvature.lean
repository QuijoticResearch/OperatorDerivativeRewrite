import Foundation.OneSidedBoundaryGauge

/-! Effective boundary curvature modulo the interior curvature range.
Its kernel is exactly the boundary-gradient gauge range. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedEffectiveCurvature
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedCapComplex
  OneSidedCapPoincare OneSidedBoundaryGauge
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def injectBoundary : BoundaryField →ₗ[ℝ] FullField where
  toFun eta := Sum.elim (fun _ => 0) eta
  map_add' f g := by
    funext e
    cases e <;> simp
  map_smul' c f := by
    funext e
    cases e <;> simp

def boundaryCurl : BoundaryField →ₗ[ℝ] Curvature := d1.comp injectBoundary

def effectiveCurvature : BoundaryField →ₗ[ℝ] (Curvature ⧸ LinearMap.range incidence) :=
  (LinearMap.range incidence).mkQ.comp boundaryCurl

theorem split_field (f : FullField) :
    injectInterior (interiorPart f)+injectBoundary (boundaryPart f)=f := by
  funext e
  cases e <;> simp [injectInterior,injectBoundary,interiorPart,boundaryPart]

theorem d1_split (f : FullField) : d1 f=
    incidence (interiorPart f)+boundaryCurl (boundaryPart f) := by
  calc
    d1 f=d1 (injectInterior (interiorPart f)+injectBoundary (boundaryPart f)) :=
      congrArg d1 (split_field f).symm
    _ = incidence (interiorPart f)+boundaryCurl (boundaryPart f) := by
      rw [map_add,d1_interior]
      rfl

theorem kernel_effective : LinearMap.ker effectiveCurvature=LinearMap.range boundaryGradient := by
  ext eta
  constructor
  · intro h
    change (LinearMap.range incidence).mkQ (boundaryCurl eta)=0 at h
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨u,hu⟩ := h
    let f : FullField := injectInterior (-u)+injectBoundary eta
    have hf : d1 f=0 := by
      dsimp [f]
      rw [map_add,d1_interior,map_neg,hu]
      change -boundaryCurl eta+boundaryCurl eta=0
      simp
    obtain ⟨phi,hphi⟩ := (closed_iff_gradient f).mp hf
    refine ⟨phi,?_⟩
    change boundaryPart (d0 phi)=eta
    rw [hphi]
    funext b
    change 0+eta b=eta b
    simp
  · rintro ⟨phi,rfl⟩
    change (LinearMap.range incidence).mkQ (boundaryCurl (boundaryGradient phi))=0
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    refine ⟨-interiorPart (d0 phi),?_⟩
    rw [map_neg]
    have hz : incidence (interiorPart (d0 phi))+boundaryCurl (boundaryGradient phi)=0 :=
      (d1_split (d0 phi)).symm.trans (d1_d0 phi)
    calc
      -incidence (interiorPart (d0 phi))=
          -incidence (interiorPart (d0 phi))+
            (incidence (interiorPart (d0 phi))+boundaryCurl (boundaryGradient phi)) := by
        rw [hz,add_zero]
      _ = boundaryCurl (boundaryGradient phi) := by abel

theorem effective_kernel_finrank : Module.finrank ℝ (LinearMap.ker effectiveCurvature)=46 := by
  rw [kernel_effective,boundary_gradient_rank]

theorem effective_rank : Module.finrank ℝ (LinearMap.range effectiveCurvature)=34 := by
  have h := LinearMap.finrank_range_add_finrank_ker effectiveCurvature
  rw [effective_kernel_finrank,boundaryField_finrank] at h
  omega

theorem curvature_quotient_finrank :
    Module.finrank ℝ (Curvature ⧸ LinearMap.range incidence)=41 := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range incidence)
  rw [incidence_rank,curvature_finrank] at h
  omega

theorem effective_cokernel_finrank :
    Module.finrank ℝ ((Curvature ⧸ LinearMap.range incidence) ⧸
      LinearMap.range effectiveCurvature)=7 := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range effectiveCurvature)
  rw [effective_rank,curvature_quotient_finrank] at h
  omega

end OperatorDerivativeRewrite.Foundation.OneSidedEffectiveCurvature
