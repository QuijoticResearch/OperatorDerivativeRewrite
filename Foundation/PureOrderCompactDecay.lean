import Foundation.HigherHeatPolynomialPathDomain
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Data.Nat.Choose.Basic

/-! Normalized pure-order moments decay locally uniformly despite unit signed mean. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PureOrderCompactDecay

def normalizer (p : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((p*n).factorial : ℝ) / a^n

theorem factorial_square_le (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    n.factorial * n.factorial ≤ (p*n).factorial := by
  have h1 : n.factorial * n.factorial ≤ (n+n).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n n)
  exact h1.trans (Nat.factorial_le (by nlinarith))

theorem factorial_ratio_le (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (n.factorial : ℝ) / ((p*n).factorial : ℝ) ≤ 1 / (n.factorial : ℝ) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have he := factorial_square_le p hp n
  simp only [one_mul]
  exact_mod_cast he

theorem normalizer_moment (p : ℕ) (hp : 0 < p) (a : ℝ) (ha : a ≠ 0) (n : ℕ) :
    normalizer p a n * PseudoPolynomialStein.moment p a (p*n) = 1 := by
  rw [PseudoPolynomialStein.moment_multiple p hp a n]
  unfold normalizer
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hpn : ((p*n).factorial : ℝ) ≠ 0 := by positivity
  have han : a^n ≠ 0 := pow_ne_zero _ ha
  field_simp

theorem normalizer_abs (p : ℕ) (a : ℝ) (n : ℕ) :
    |normalizer p a n| = (n.factorial : ℝ) / ((p*n).factorial : ℝ) / |a|^n := by
  simp [normalizer, abs_div, abs_pow]

theorem monomial_bound (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : a ≠ 0)
    (R : ℝ) (_hR : 0 ≤ R) (x : ℝ) (hx : |x| ≤ R) (n : ℕ) :
    |normalizer p a n * x^(p*n)| ≤ (R^p/|a|)^n / (n.factorial : ℝ) := by
  rw [abs_mul, normalizer_abs, abs_pow]
  have hfac := factorial_ratio_le p hp n
  have hpow : |x|^(p*n) ≤ R^(p*n) := pow_le_pow_left₀ (abs_nonneg x) hx _
  calc
    _ ≤ ((1/(n.factorial : ℝ))/|a|^n) * R^(p*n) :=
      mul_le_mul (div_le_div_of_nonneg_right hfac (by positivity)) hpow (by positivity) (by positivity)
    _ = _ := by rw [div_pow, pow_mul]; ring

def family {α : Type*} [TopologicalSpace α] (p : ℕ) (a : ℝ) (u : C(α,ℝ)) (n : ℕ) : C(α,ℝ) :=
  normalizer p a n • u^(p*n)

theorem family_compact_decay {α : Type*} [TopologicalSpace α] (p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : a ≠ 0) (u : C(α,ℝ)) :
    Tendsto (family p a u) atTop (𝓝 0) := by
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro K hK
  obtain ⟨M, hM⟩ := hK.bddAbove_image u.continuous.norm.continuousOn
  let R : ℝ := |M|+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hb (x : α) (hx : x ∈ K) : |u x| ≤ R := by
    have hh : ‖u x‖ ≤ M := hM (Set.mem_image_of_mem _ hx)
    rw [Real.norm_eq_abs] at hh
    exact hh.trans ((le_abs_self M).trans (by dsimp [R]; linarith))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop (R^p/|a|)
  have he : ∀ᶠ n in atTop, (R^p/|a|)^n / (n.factorial : ℝ) < ε :=
    ht.eventually (gt_mem_nhds hε)
  filter_upwards [he] with n hn x hx
  have hh := monomial_bound p hp a ha R hR (u x) (hb x hx) n
  simpa [family, Real.dist_eq, abs_neg] using hh.trans_lt hn

end OperatorDerivativeRewrite.Foundation.PureOrderCompactDecay
