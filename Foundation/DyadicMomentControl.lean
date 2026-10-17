import Foundation.IBMBrownianDyadicControl

/-! A variable-moment dyadic continuity criterion. The moment exponent and
geometric rates are explicit, so small-H fractional processes are admissible. -/
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.DyadicMomentControl
open InfiniteGaussian IBMDyadicExtension

theorem dyadic_control (G : ℝ → SampleSpace → ℝ) (p : ℕ) (C β θ : ℝ)
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (hθ : 0 < θ)
    (hrate : 2*β/θ^p < 1)
    (hint : ∀ s t, Integrable (fun ω => |G t ω-G s ω|^p) gaussianProduct)
    (hbound : ∀ (a : ℝ) (l : ℕ) (k : Fin (2^l)),
      (∫ ω, |G (grid a l (k.val+1)) ω-G (grid a l k.val) ω|^p ∂gaussianProduct) ≤ C*β^l)
    (a : ℝ) :
    ∀ᵐ ω ∂gaussianProduct, ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) ω-G (grid a l k.val) ω| < θ^l := by
  classical
  let bad : ℕ → Set SampleSpace := fun l => ⋃ k : Fin (2^l),
    {ω | (θ^l)^p ≤ |G (grid a l (k.val+1)) ω-G (grid a l k.val) ω|^p}
  have htail (l : ℕ) (k : Fin (2^l)) :
      gaussianProduct.real {ω | (θ^l)^p ≤
        |G (grid a l (k.val+1)) ω-G (grid a l k.val) ω|^p} ≤ C*β^l/(θ^l)^p := by
    apply (le_div_iff₀ (pow_pos (pow_pos hθ l) p)).mpr
    rw [mul_comm]
    exact (mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) p)
      (hint _ _) ((θ^l)^p)).trans (hbound a l k)
  have hmajor (l : ℕ) : gaussianProduct.real (bad l) ≤ C*(2*β/θ^p)^l := by
    calc
      _ ≤ ∑ k : Fin (2^l), gaussianProduct.real {ω | (θ^l)^p ≤
          |G (grid a l (k.val+1)) ω-G (grid a l k.val) ω|^p} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _k : Fin (2^l), C*β^l/(θ^l)^p := Finset.sum_le_sum (fun k _ => htail l k)
      _ = C*(2*β/θ^p)^l := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [← pow_mul, Nat.mul_comm l p, pow_mul, div_pow, mul_pow]
        ring
  have hs : Summable (fun l => gaussianProduct.real (bad l)) :=
    Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) hmajor
      ((summable_geometric_of_lt_one (by positivity : 0 ≤ 2*β/θ^p) hrate).mul_left C)
  have hfinite : (∑' l, gaussianProduct (bad l)) ≠ ⊤ := by
    convert hs.tsum_ofReal_ne_top using 1
    congr 1; funext l
    exact (ENNReal.ofReal_toReal (measure_ne_top gaussianProduct (bad l))).symm
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω] with l hl k
  by_contra! hge
  apply hl
  apply Set.mem_iUnion.mpr
  exact ⟨k, pow_le_pow_left₀ (by positivity) hge p⟩

end OperatorDerivativeRewrite.Foundation.DyadicMomentControl
