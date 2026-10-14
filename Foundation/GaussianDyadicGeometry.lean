import Foundation.IBMDyadicExtension

/-! The same deterministic extension at a variable geometric rate, allowing
the weaker fourth-moment regularity of the original Brownian sources. -/
noncomputable section
open Filter
open scoped Topology

namespace OperatorDerivativeRewrite.Foundation.GaussianDyadicGeometry
open IBMDyadicExtension

theorem rounded_cauchy {G : ℝ → ℝ} {a θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) - G (grid a l k.val)| ≤ θ^l)
    (x : UnitInterval) : CauchySeq (fun l => rounded G a l x) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hs : Summable (fun l => dist (rounded G a l x) (rounded G a (l+1) x)) := by
    rw [← summable_nat_add_iff N]
    apply Summable.of_nonneg_of_le (fun _ => dist_nonneg)
      (fun l => rounded_step_le (pow_nonneg hθ0 _) (hN (l+N+1) (by omega)) x)
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (N+1)).mpr (summable_geometric_of_lt_one hθ0 hθ1)
  exact cauchySeq_of_summable_dist hs

theorem extension_tendsto {G : ℝ → ℝ} {a θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) - G (grid a l k.val)| ≤ θ^l)
    (x : UnitInterval) : Tendsto (fun l => rounded G a l x) atTop (𝓝 (extension G a x)) := by
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (rounded_cauchy hθ0 hθ1 h x)
  simpa only [extension, hy.limsup_eq] using hy

theorem extension_tail {G : ℝ → ℝ} {a θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {N l : ℕ}
    (h : ∀ m ≥ N, ∀ k : Fin (2^m),
      |G (grid a m (k.val+1)) - G (grid a m k.val)| ≤ θ^m)
    (hl : N ≤ l) (x : UnitInterval) :
    dist (rounded G a l x) (extension G a x) ≤ (θ / (1-θ)) * θ^l := by
  have he := eventually_atTop.mpr ⟨N, h⟩
  have ht : Tendsto (fun m => rounded G a (l+m) x) atTop (𝓝 (extension G a x)) := by
    simpa only [Function.comp_def, Nat.add_comm] using
      (extension_tendsto hθ0 hθ1 he x).comp (tendsto_add_atTop_nat l)
  have hb := dist_le_tsum_of_dist_le_of_tendsto₀ (fun m : ℕ => θ^(l+m+1))
    (fun m => rounded_step_le (pow_nonneg hθ0 _) (h (l+m+1) (by omega)) x)
    (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff (l+1)).mpr (summable_geometric_of_lt_one hθ0 hθ1)) ht
  simp only [Nat.add_zero] at hb
  have hs : (∑' m : ℕ, θ^(l+m+1)) = (θ/(1-θ))*θ^l := by
    simp_rw [pow_succ, pow_add, mul_assoc]
    rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hθ0 hθ1]
    ring
  exact hb.trans_eq hs

theorem extension_continuous {G : ℝ → ℝ} {a θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) - G (grid a l k.val)| ≤ θ^l) :
    Continuous (extension G a) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  apply Metric.continuous_iff.mpr
  intro x ε hε
  have hz : Tendsto (fun l : ℕ => (2*θ/(1-θ)+1)*θ^l) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul (2*θ/(1-θ)+1)
  obtain ⟨l, hlN, hl⟩ := ((eventually_ge_atTop N).and
    (hz.eventually (eventually_lt_nhds hε))).exists
  refine ⟨1 / (2 : ℝ)^l, by positivity, ?_⟩
  intro y hy
  have hx := extension_tail hθ0 hθ1 hN hlN x
  have hy' := extension_tail hθ0 hθ1 hN hlN y
  have hc := rounded_close (pow_nonneg hθ0 _) (hN l hlN) y x hy
  calc
    dist (extension G a y) (extension G a x) ≤
        dist (extension G a y) (rounded G a l y) +
        dist (rounded G a l y) (rounded G a l x) +
        dist (rounded G a l x) (extension G a x) := dist_triangle4 _ _ _ _
    _ ≤ (2*θ/(1-θ)+1)*θ^l := by
      rw [dist_comm (extension G a y)]
      calc
        _ ≤ (θ/(1-θ))*θ^l + θ^l + (θ/(1-θ))*θ^l := add_le_add (add_le_add hy' hc) hx
        _ = _ := by ring
    _ < ε := hl

end OperatorDerivativeRewrite.Foundation.GaussianDyadicGeometry
