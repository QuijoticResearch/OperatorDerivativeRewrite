import Foundation.CubePathPoincare

/-! Constructive exactness: every curl-free field on the cap complex is a gradient. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedCapPoincare
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedCapComplex
  CubePathPoincare
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def recover (f : FullField) : Potential := Sum.elim
  (fun v => pathMap (extend (interiorPart f)) v)
  (fun c => pathMap (extend (interiorPart f)) c.val.1+f (.inr (.inl c)))

theorem inner_closed (f : FullField) (hf : d1 f=0) :
    ∀ p∈innerFaces, realCurl (extend (interiorPart f)) p=0 := by
  intro p hp
  have h := congrArg (fun q : Curvature => q.1 ⟨p,hp⟩) hf
  exact h

theorem recover_interior (f : FullField) (hf : d1 f=0) (e : Interior) :
    d0 (recover f) (.inl e)=f (.inl e) := by
  change pathMap (extend (interiorPart f)) (shifted e.val.1 e.val.2)-
    pathMap (extend (interiorPart f)) e.val.1=f (.inl e)
  have h := cube_poincare (extend (interiorPart f)) (inner_closed f hf) e
  simpa [extend_on,interiorPart] using h

theorem recover_outward (f : FullField) (c : Cap) :
    d0 (recover f) (.inr (.inl c))=f (.inr (.inl c)) := by
  simp [d0,recover,source,target]

theorem recover_tangent (f : FullField) (hf : d1 f=0) (p : Upper) :
    d0 (recover f) (.inr (.inr p))=f (.inr (.inr p)) := by
  have hi := recover_interior f hf (ribbonInterior p)
  change pathMap (extend (interiorPart f)) (shifted p.val.1.1 p.val.1.2)-
    pathMap (extend (interiorPart f)) p.val.1.1=f (.inl (ribbonInterior p)) at hi
  have hr := congrArg (fun q : Curvature => q.2 p) hf
  change f (.inl (ribbonInterior p))+f (.inr (.inl (capHigh p)))-
    f (.inr (.inr p))-f (.inr (.inl (capLow p)))=0 at hr
  change (pathMap (extend (interiorPart f)) (shifted p.val.1.1 p.val.1.2)+
      f (.inr (.inl (capHigh p))))-
    (pathMap (extend (interiorPart f)) p.val.1.1+f (.inr (.inl (capLow p))))=
      f (.inr (.inr p))
  linarith

theorem d0_recover (f : FullField) (hf : d1 f=0) : d0 (recover f)=f := by
  funext e
  cases e with
  | inl e => exact recover_interior f hf e
  | inr b =>
    cases b with
    | inl c => exact recover_outward f c
    | inr p => exact recover_tangent f hf p

theorem closed_iff_gradient (f : FullField) : d1 f=0 ↔ ∃ phi : Potential, d0 phi=f := by
  constructor
  · intro h
    exact ⟨recover f,d0_recover f h⟩
  · rintro ⟨phi,rfl⟩
    exact d1_d0 phi

theorem kernel_eq_range : LinearMap.ker d1=LinearMap.range d0 := by
  ext f
  simp only [LinearMap.mem_ker,LinearMap.mem_range]
  exact closed_iff_gradient f

theorem recover_origin (f : FullField) : recover f (.inl origin)=0 :=
  path_origin (extend (interiorPart f))

end OperatorDerivativeRewrite.Foundation.OneSidedCapPoincare
