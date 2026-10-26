import Foundation.ScaledGraphResolvent

/-! Strong ORIGINAL graph approximation on the native domain. The actual
resolvent commutes with the derivative through the ORIGINAL adjoint resolvent.
No native derivative domain is extended by these identities. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ScaledGraphResolventDomain
open ScaledGraphResolvent
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
attribute [local irreducible] LinearPMap.adjoint

theorem regularize_eq_of_weak (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E)
    (w : A.domain)
    (hw : ∀ u : A.domain, inner ℝ (w:E) (u:E)+(scale n)^2*inner ℝ (A w) (A u) =
      inner ℝ x (u:E)) : (w:E) = regularize A hA n x := by
  let r : A.domain := ⟨regularize A hA n x,regularize_mem A hA n x⟩
  let d : A.domain := w-r
  have hr : inner ℝ (r:E) (d:E)+(scale n)^2*inner ℝ (A r) (A d)=inner ℝ x (d:E) :=
    native_weak_identity A hA n x d
  have hd : A d=A w-A r := A.map_sub _ _
  have hz : ‖(w:E)-(r:E)‖^2+(scale n)^2*‖A w-A r‖^2=0 := by
    calc
      _ = inner ℝ ((w:E)-(r:E)) (d:E)+(scale n)^2*inner ℝ (A w-A r) (A d) := by
        rw [hd]
        simp only [d,Submodule.coe_sub,real_inner_self_eq_norm_sq]
      _ = (inner ℝ (w:E) (d:E)+(scale n)^2*inner ℝ (A w) (A d)) -
          (inner ℝ (r:E) (d:E)+(scale n)^2*inner ℝ (A r) (A d)) := by
        simp only [inner_sub_left]
        ring
      _ = 0 := by rw [hw d,hr]; ring
  have hn : ‖(w:E)-(r:E)‖=0 := by
    nlinarith [mul_nonneg (sq_nonneg (scale n)) (sq_nonneg ‖A w-A r‖)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem nativeGradient_mem_adjoint (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E) :
    nativeGradient A hA n x ∈ A.adjoint.domain := by
  have h := A.adjoint.domain.smul_mem ((scale n)^2)⁻¹ (weighted_gradient_mem_adjoint A hA n x)
  simpa only [smul_smul,inv_mul_cancel₀ (pow_ne_zero 2 (scale_pos n).ne'),one_smul] using h

theorem native_adjoint_unweighted (A : E →ₗ.[ℝ] F) (hA : A.IsClosed)
    (hd : Dense (A.domain : Set E)) (n : ℕ) (x : E) :
    (scale n)^2 • A.adjoint ⟨nativeGradient A hA n x,nativeGradient_mem_adjoint A hA n x⟩ =
      x-regularize A hA n x := by
  have h := native_adjoint_identity A hA hd n x
  have he : (⟨(scale n)^2 • nativeGradient A hA n x,weighted_gradient_mem_adjoint A hA n x⟩ :
      A.adjoint.domain) = (scale n)^2 •
        (⟨nativeGradient A hA n x,nativeGradient_mem_adjoint A hA n x⟩ : A.adjoint.domain) :=
    Subtype.ext rfl
  rw [he,A.adjoint.map_smul] at h
  exact h

theorem nativeGradient_dual_regularize (A : E →ₗ.[ℝ] F) (hA : A.IsClosed)
    (hd : Dense (A.domain : Set E)) (n : ℕ) (x : A.domain) :
    nativeGradient A hA n x = regularize A.adjoint (A.adjoint_isClosed hd) n (A x) := by
  apply regularize_eq_of_weak A.adjoint (A.adjoint_isClosed hd) n (A x)
    ⟨nativeGradient A hA n x,nativeGradient_mem_adjoint A hA n x⟩
  intro v
  let r : A.domain := ⟨regularize A hA n x,regularize_mem A hA n x⟩
  have hx : inner ℝ (A x) (v:F)=inner ℝ (x:E) (A.adjoint v) := by
    calc
      _ = inner ℝ (v:F) (A x) := real_inner_comm _ _
      _ = inner ℝ (A.adjoint v) (x:E) := (A.adjoint_isFormalAdjoint hd v x).symm
      _ = _ := real_inner_comm _ _
  have hr : inner ℝ (nativeGradient A hA n x) (v:F)=inner ℝ (r:E) (A.adjoint v) := by
    calc
      _ = inner ℝ (v:F) (A r) := real_inner_comm _ _
      _ = inner ℝ (A.adjoint v) (r:E) := (A.adjoint_isFormalAdjoint hd v r).symm
      _ = _ := real_inner_comm _ _
  have he := congrArg (fun z : E => inner ℝ z (A.adjoint v))
    (native_adjoint_unweighted A hA hd n (x:E))
  rw [real_inner_smul_left,inner_sub_left] at he
  rw [hr,hx]
  linarith

theorem nativeGradient_norm_le (A : E →ₗ.[ℝ] F) (hA : A.IsClosed)
    (hd : Dense (A.domain : Set E)) (n : ℕ) (x : A.domain) :
    ‖nativeGradient A hA n x‖ ≤ ‖A x‖ := by
  rw [nativeGradient_dual_regularize A hA hd]
  exact regularize_contraction A.adjoint (A.adjoint_isClosed hd) n (A x)

theorem nativeGradient_tendsto (A : E →ₗ.[ℝ] F) (hA : A.IsClosed)
    (hd : Dense (A.domain : Set E)) (x : A.domain) :
    Tendsto (fun n => nativeGradient A hA n x) atTop (𝓝 (A x)) := by
  simpa only [nativeGradient_dual_regularize A hA hd] using
    regularize_tendsto A.adjoint (A.adjoint_isClosed hd)
      (HilbertAdjointDomainDensity.closed_adjoint_dense A hA hd) (A x)

theorem original_graph_tendsto (A : E →ₗ.[ℝ] F) (hA : A.IsClosed)
    (hd : Dense (A.domain : Set E)) (x : A.domain) :
    Tendsto (fun n => (regularize A hA n x,nativeGradient A hA n x)) atTop (𝓝 ((x:E),A x)) :=
  (regularize_tendsto A hA hd (x:E)).prodMk_nhds (nativeGradient_tendsto A hA hd x)

end OperatorDerivativeRewrite.Foundation.ScaledGraphResolventDomain
