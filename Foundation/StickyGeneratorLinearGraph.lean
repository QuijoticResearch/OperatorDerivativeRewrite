import Foundation.StickyGeneratorRelation
import Foundation.StickyVanishingGeneratorPair

/-! The differential boundary relation is linear. Norm estimates give uniqueness
and stability for resolvent solutions, without asserting their existence. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ZeroAtInfty
namespace OperatorDerivativeRewrite.Foundation.StickyGeneratorLinearGraph
open StickyGeneratorRelation
set_option backward.isDefEq.respectTransparency false

theorem add {κ : ℝ≥0} {F G H K : C₀(ℝ, ℝ)}
    (h : Admissible κ F G) (h' : Admissible κ H K) :
    Admissible κ (F+H) (G+K) := by
  have he (x : ℝ) (hx : x ≠ 0) :
      deriv ((F+H : C₀(ℝ, ℝ)) : ℝ → ℝ) =ᶠ[𝓝 x]
        (fun y => deriv (F : ℝ → ℝ) y+deriv (H : ℝ → ℝ) y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact deriv_add (h.differentiable y hy) (h'.differentiable y hy)
  refine ⟨fun x hx => (h.differentiable x hx).add (h'.differentiable x hx), ?_, ?_, ?_⟩
  · intro x hx
    exact (he x hx).differentiableAt_iff.mpr
      ((h.twice_differentiable x hx).add (h'.twice_differentiable x hx))
  · intro x hx
    change G x+K x = (1/2 : ℝ)*deriv (deriv ((F+H : C₀(ℝ, ℝ)) : ℝ → ℝ)) x
    rw [(he x hx).deriv_eq,
      deriv_fun_add (h.twice_differentiable x hx) (h'.twice_differentiable x hx),
      h.off_zero x hx,h'.off_zero x hx]
    ring
  · obtain ⟨r,l,hr,hl,hj⟩ := h.boundary
    obtain ⟨r',l',hr',hl',hj'⟩ := h'.boundary
    refine ⟨r+r',l+l',hr.add hr',hl.add hl',?_⟩
    change r+r'-(l+l') = 2*(κ : ℝ)*(G 0+K 0)
    linarith

theorem smul {κ : ℝ≥0} {F G : C₀(ℝ, ℝ)}
    (h : Admissible κ F G) (c : ℝ) : Admissible κ (c • F) (c • G) := by
  have he : deriv ((c • F : C₀(ℝ, ℝ)) : ℝ → ℝ) =
      (fun y => c*deriv (F : ℝ → ℝ) y) := by
    funext x
    exact deriv_const_mul_field c
  refine ⟨fun x hx => (h.differentiable x hx).const_mul c, ?_, ?_, ?_⟩
  · intro x hx
    rw [he]
    exact (h.twice_differentiable x hx).const_mul c
  · intro x hx
    change c*G x = (1/2 : ℝ)*deriv (deriv ((c • F : C₀(ℝ, ℝ)) : ℝ → ℝ)) x
    rw [he,deriv_const_mul_field,h.off_zero x hx]
    ring
  · obtain ⟨r,l,hr,hl,hj⟩ := h.boundary
    refine ⟨c*r,c*l,hr.const_mul c,hl.const_mul c,?_⟩
    change c*r-c*l = 2*(κ : ℝ)*(c*G 0)
    nlinarith [congrArg (fun z : ℝ => c*z) hj]

theorem sub {κ : ℝ≥0} {F G H K : C₀(ℝ, ℝ)}
    (h : Admissible κ F G) (h' : Admissible κ H K) :
    Admissible κ (F-H) (G-K) := by
  simpa only [sub_eq_add_neg] using add h h'.neg

theorem resolvent_stability {κ : ℝ≥0} (hκ : 0 < κ) {F G H K : C₀(ℝ, ℝ)}
    (h : Admissible κ F G) (h' : Admissible κ H K) {q : ℝ} (hq : 0 < q) :
    q*‖F-H‖ ≤ ‖(q • F-G)-(q • H-K)‖ := by
  have he : q • (F-H)-(G-K) = (q • F-G)-(q • H-K) := by
    simp only [smul_sub]
    abel
  simpa only [he] using resolvent_norm_bound hκ (sub h h') hq

theorem resolvent_injective {κ : ℝ≥0} (hκ : 0 < κ) {F G H K : C₀(ℝ, ℝ)}
    (h : Admissible κ F G) (h' : Admissible κ H K) {q : ℝ} (hq : 0 < q)
    (he : q • F - G = q • H - K) : F = H := by
  have hb := resolvent_stability hκ h h' hq
  rw [he,sub_self,norm_zero] at hb
  have hn : ‖F-H‖ = 0 := by
    have hnon := norm_nonneg (F-H)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem single_valued {κ : ℝ≥0} {F G K : C₀(ℝ, ℝ)}
    (h : Admissible κ F G) (h' : Admissible κ F K) : G = K := by
  apply DFunLike.coe_injective
  apply Continuous.ext_on (f := (G : ℝ → ℝ)) (g := (K : ℝ → ℝ))
    (dense_compl_singleton (0 : ℝ)) G.continuous K.continuous
  intro x hx
  have hn : x ≠ 0 := hx
  rw [h.off_zero x hn,h'.off_zero x hn]

theorem of_boundary_test (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (κ : ℝ≥0)
    (F G : C₀(ℝ, ℝ))
    (hF : (F : ℝ → ℝ) = StickyC2MartingaleProblem.boundaryTest f κ)
    (hG : (G : ℝ → ℝ) = StickyBoundaryGeneratorCore.candidateGenerator f) :
    Admissible κ F G := by
  have hd : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have he (x : ℝ) (hx : x ≠ 0) :
      DifferentiableAt ℝ (deriv (F : ℝ → ℝ)) x := by
    rw [hF]
    rcases lt_or_gt_of_ne hx with hn | hp
    · have hh : deriv (StickyC2MartingaleProblem.boundaryTest f κ) =ᶠ[𝓝 x]
          (fun y => deriv f y-StickyC2MartingaleProblem.coefficient f κ) :=
        (eventually_lt_nhds hn).mono (fun y hy =>
          StickyBoundaryGeneratorCore.derivative_neg f hf κ y hy)
      exact hh.differentiableAt_iff.mpr ((hd x).sub_const _)
    · have hh : deriv (StickyC2MartingaleProblem.boundaryTest f κ) =ᶠ[𝓝 x]
          (fun y => deriv f y+StickyC2MartingaleProblem.coefficient f κ) :=
        (eventually_gt_nhds hp).mono (fun y hy =>
          StickyBoundaryGeneratorCore.derivative_pos f hf κ y hy)
      exact hh.differentiableAt_iff.mpr ((hd x).add_const _)
  refine ⟨?_,he,?_,?_⟩
  · intro x hx
    rw [hF]
    exact (hf.differentiable (by norm_num) x).add
      ((differentiableAt_abs hx).const_mul _)
  · intro x hx
    rw [hF]
    rw [hG]
    exact StickyBoundaryGeneratorCore.generator_off_zero f hf κ x hx
  · rw [hF]
    refine ⟨deriv f 0+StickyC2MartingaleProblem.coefficient f κ,
      deriv f 0-StickyC2MartingaleProblem.coefficient f κ,
      StickyC2MartingaleProblem.right_derivative f hf κ,
      StickyC2MartingaleProblem.left_derivative f hf κ,?_⟩
    rw [hG]
    exact StickyBoundaryGeneratorCore.generator_boundary_jump f κ

theorem concrete_pair (κ : ℝ≥0) :
    Admissible κ (StickyVanishingBoundaryTest.testC0 κ)
      (StickyVanishingGeneratorPair.generatorC0 κ) := by
  exact of_boundary_test (StickyVanishingBoundaryTest.base κ)
    (StickyVanishingBoundaryTest.base_smooth κ) κ _ _ rfl rfl

end OperatorDerivativeRewrite.Foundation.StickyGeneratorLinearGraph
