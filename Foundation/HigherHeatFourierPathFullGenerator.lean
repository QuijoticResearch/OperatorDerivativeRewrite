import Foundation.HigherHeatFourierPathResolvent

/-! Exact full infinitesimal generator of the genuine Fourier path heat C0 semigroup. -/
noncomputable section
open Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathFullGenerator
open HigherHeatDyadicLaws HigherHeatFourierBanach HigherHeatFourierPathSemigroup
open HigherHeatFourierPathGenerator HigherHeatFourierPathClosure HigherHeatFourierPathResolvent

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem resolvent_left_inverse (m : ℕ) (hm : 0 < m)
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ m) :
    z.1 = resolvent levels ξ m hm (z.1-z.2) := by
  have hg := (graph levels ξ m).sub_mem hz (resolvent_graph levels ξ m hm (z.1-z.2))
  have hb := graph_bound levels ξ m hm 1 (by norm_num) _ hg
  change 1*‖z.1-resolvent levels ξ m hm (z.1-z.2)‖ ≤
    ‖(1:ℝ) • (z.1-resolvent levels ξ m hm (z.1-z.2))-
      (z.2-(resolvent levels ξ m hm (z.1-z.2)-(z.1-z.2)))‖ at hb
  simp only [one_mul, one_smul] at hb
  have he : (z.1-resolvent levels ξ m hm (z.1-z.2))-
      (z.2-(resolvent levels ξ m hm (z.1-z.2)-(z.1-z.2)))=0 := by abel
  rw [he, norm_zero, norm_le_zero_iff] at hb
  exact sub_eq_zero.mp hb

theorem graph_iff_resolvent (m : ℕ) (hm : 0 < m) (x v : TestSpace levels ξ) :
    (x,v) ∈ graph levels ξ m ↔ x=resolvent levels ξ m hm (x-v) := by
  constructor
  · exact resolvent_left_inverse levels ξ m hm (x,v)
  · intro hx
    have hg := resolvent_graph levels ξ m hm (x-v)
    rw [← hx] at hg
    simpa only [sub_sub_cancel] using hg

theorem graph_closed (m : ℕ) (hm : 0 < m) :
    IsClosed (graph levels ξ m : Set (TestSpace levels ξ × TestSpace levels ξ)) := by
  have he : (graph levels ξ m : Set (TestSpace levels ξ × TestSpace levels ξ))=
      {z | z.1=resolvent levels ξ m hm (z.1-z.2)} := by
    ext z
    exact graph_iff_resolvent levels ξ m hm z.1 z.2
  rw [he]
  exact isClosed_eq continuous_fst
    ((resolvent levels ξ m hm).continuous.comp (continuous_fst.sub continuous_snd))

theorem operator_closed (m : ℕ) (hm : 0 < m) : (operator levels ξ m).IsClosed := by
  change IsClosed ((operator levels ξ m).graph :
    Set (TestSpace levels ξ × TestSpace levels ξ))
  rw [operator_graph levels ξ m hm]
  exact graph_closed levels ξ m hm

theorem limit_implies_graph (m : ℕ) (hm : 0 < m) (f g : TestSpace levels ξ)
    (hlim : Tendsto (fun t : ℝ => t⁻¹ • (evolution levels ξ m hm t.toNNReal f-f))
      (𝓝[Set.Ioi 0] 0) (𝓝 g)) : (f,g) ∈ graph levels ξ m := by
  let x := resolvent levels ξ m hm (f-g)
  let v := x-(f-g)
  have hg : (x,v) ∈ graph levels ξ m := resolvent_graph levels ξ m hm (f-g)
  have hl := graph_limit levels ξ m hm (x,v) hg
  have hd : Tendsto (fun t : ℝ => t⁻¹ •
      (evolution levels ξ m hm t.toNNReal (f-x)-(f-x)))
      (𝓝[Set.Ioi 0] 0) (𝓝 (g-v)) := by
    convert hlim.sub hl using 1
    funext t
    rw [map_sub, ← smul_sub]
    congr 1
    abel
  have hb := ContractionTangentDissipativity.norm_resolvent_bound
    (fun t => evolution levels ξ m hm t.toNNReal (f-x)) (f-x) (g-v)
    (fun t _ => evolution_bound levels ξ m hm t.toNNReal (f-x)) hd 1 (by norm_num)
  have he : (f-x)-(g-v)=0 := by dsimp [v]; abel
  simp only [one_mul,one_smul,he,norm_zero,norm_le_zero_iff] at hb
  have hfx : f=x := sub_eq_zero.mp hb
  apply (graph_iff_resolvent levels ξ m hm f g).mpr
  exact hfx

theorem limit_iff_graph (m : ℕ) (hm : 0 < m) (f g : TestSpace levels ξ) :
    Tendsto (fun t : ℝ => t⁻¹ • (evolution levels ξ m hm t.toNNReal f-f))
      (𝓝[Set.Ioi 0] 0) (𝓝 g) ↔ (f,g) ∈ (operator levels ξ m).graph := by
  rw [operator_graph levels ξ m hm]
  exact ⟨limit_implies_graph levels ξ m hm f g, graph_limit levels ξ m hm (f,g)⟩

theorem domain_iff_limit (m : ℕ) (hm : 0 < m) (f : TestSpace levels ξ) :
    f ∈ (operator levels ξ m).domain ↔ ∃ g,
      Tendsto (fun t : ℝ => t⁻¹ • (evolution levels ξ m hm t.toNNReal f-f))
        (𝓝[Set.Ioi 0] 0) (𝓝 g) := by
  rw [LinearPMap.mem_domain_iff]
  simp only [limit_iff_graph]

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathFullGenerator
