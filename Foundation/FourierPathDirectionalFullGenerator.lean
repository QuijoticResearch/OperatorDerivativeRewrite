import Foundation.FourierPathDirectionalResolvent

/-! Exact closed directional differentiation of actual completed Fourier path observables. -/
noncomputable section
open Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDirectionalFullGenerator
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierTranslationContinuity FourierPathDirectionalOperator
open FourierPathDirectionalResolvent

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem resolvent_left_inverse (h : Path) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ h) : z.1=resolvent levels ξ h (z.1-z.2) := by
  have hg := (graph levels ξ h).sub_mem hz (resolvent_graph levels ξ h (z.1-z.2))
  have hb := graph_bound levels ξ h 1 (by norm_num) _ hg
  change 1*‖z.1-resolvent levels ξ h (z.1-z.2)‖ ≤
    ‖(1:ℝ) • (z.1-resolvent levels ξ h (z.1-z.2))-
      (z.2-(resolvent levels ξ h (z.1-z.2)-(z.1-z.2)))‖ at hb
  simp only [one_mul, one_smul] at hb
  have he : (z.1-resolvent levels ξ h (z.1-z.2))-
      (z.2-(resolvent levels ξ h (z.1-z.2)-(z.1-z.2)))=0 := by abel
  rw [he, norm_zero, norm_le_zero_iff] at hb
  exact sub_eq_zero.mp hb

theorem graph_iff_resolvent (h : Path) (x v : TestSpace levels ξ) :
    (x,v) ∈ graph levels ξ h ↔ x=resolvent levels ξ h (x-v) := by
  constructor
  · exact resolvent_left_inverse levels ξ h (x,v)
  · intro hx
    have hg := resolvent_graph levels ξ h (x-v)
    rw [← hx] at hg
    simpa only [sub_sub_cancel] using hg

theorem graph_closed (h : Path) :
    IsClosed (graph levels ξ h : Set (TestSpace levels ξ × TestSpace levels ξ)) := by
  have he : (graph levels ξ h : Set (TestSpace levels ξ × TestSpace levels ξ))=
      {z | z.1=resolvent levels ξ h (z.1-z.2)} := by
    ext z
    exact graph_iff_resolvent levels ξ h z.1 z.2
  rw [he]
  exact isClosed_eq continuous_fst
    ((resolvent levels ξ h).continuous.comp (continuous_fst.sub continuous_snd))

theorem operator_closed (h : Path) : (operator levels ξ h).IsClosed := by
  change IsClosed ((operator levels ξ h).graph : Set (TestSpace levels ξ × TestSpace levels ξ))
  rw [operator_graph]
  exact graph_closed levels ξ h

theorem deriv_implies_graph (h : Path) (f g : TestSpace levels ξ)
    (hderiv : HasDerivAt (fun t => along levels ξ h t f) g 0) : (f,g) ∈ graph levels ξ h := by
  let x := resolvent levels ξ h (f-g)
  let v := x-(f-g)
  have hg : (x,v) ∈ graph levels ξ h := resolvent_graph levels ξ h (f-g)
  have hd : HasDerivAt (fun t => along levels ξ h t (f-x)) (g-v) 0 := by
    convert hderiv.sub (graph_deriv levels ξ h (x,v) hg) using 1
    funext t
    rw [map_sub]
    rfl
  have ht := hd.tendsto_slope_zero_right
  simp only [zero_add, along_zero] at ht
  have hb := ContractionTangentDissipativity.norm_resolvent_bound
    (fun t => along levels ξ h t (f-x)) (f-x) (g-v)
    (fun t _ => (along_norm levels ξ h t (f-x)).le) ht 1 (by norm_num)
  have he : (f-x)-(g-v)=0 := by dsimp [v]; abel
  simp only [one_mul,one_smul,he,norm_zero,norm_le_zero_iff] at hb
  exact (graph_iff_resolvent levels ξ h f g).mpr (sub_eq_zero.mp hb)

theorem deriv_iff_graph (h : Path) (f g : TestSpace levels ξ) :
    HasDerivAt (fun t => along levels ξ h t f) g 0 ↔ (f,g) ∈ (operator levels ξ h).graph := by
  rw [operator_graph]
  exact ⟨deriv_implies_graph levels ξ h f g, graph_deriv levels ξ h (f,g)⟩

theorem domain_iff_derivative (h : Path) (f : TestSpace levels ξ) :
    f ∈ (operator levels ξ h).domain ↔ ∃ g,
      HasDerivAt (fun t => along levels ξ h t f) g 0 := by
  rw [LinearPMap.mem_domain_iff]
  simp only [deriv_iff_graph]

end OperatorDerivativeRewrite.Foundation.FourierPathDirectionalFullGenerator
