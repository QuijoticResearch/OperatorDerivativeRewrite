import Foundation.PoissonCoherentVectors
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Totality of the actual Poisson exponential observation family, proved
by atomwise induction and dominated convergence rather than assumed chaos density. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.PoissonExponentialTotal
open PoissonDifferenceCore PoissonDifferenceOperators PoissonCoherentVectors

private def probe (f : ℕ → ℝ) (r j k : ℕ) : ℝ :=
  f k*Real.exp (-(j : ℝ)*((k : ℝ)-r))

private theorem atom_zero (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (r : ℕ)
    (hprev : ∀ k<r, f k=0) (horth : ∀ θ : ℝ, inner ℝ f (scalar rate θ)=0) : f r=0 := by
  have ho (θ : ℝ) : (∫ k, f k*exponential θ k ∂poissonLaw rate)=0 := by
    have h := horth θ
    rw [L2_inner_eq_integral] at h
    have he : (fun k => inner ℝ (f k) (scalar rate θ k)) =
        fun k => f k*exponential θ k := by
      funext k
      rw [scalar_apply rate hr]
      simp [Real.inner_apply,mul_comm]
    rwa [he] at h
  have hz (j : ℕ) : (∫ k, probe f r j k ∂poissonLaw rate)=0 := by
    have he : probe f r j = fun k => Real.exp ((j : ℝ)*r)*(f k*exponential (-(j : ℝ)) k) := by
      funext k
      have hp : -(j : ℝ)*((k : ℝ)-r)=(j : ℝ)*r+(-(j : ℝ))*(k : ℝ) := by ring
      rw [probe,exponential,hp,Real.exp_add]
      ring
    rw [he,integral_const_mul,ho,mul_zero]
  have hb (j : ℕ) : ∀ᵐ k ∂poissonLaw rate, ‖probe f r j k‖ ≤ ‖f k‖ := by
    apply Filter.Eventually.of_forall
    intro k
    by_cases hk : k<r
    · simp [probe,hprev k hk]
    · have hkr : (r : ℝ) ≤ k := by exact_mod_cast le_of_not_gt hk
      have hp : -(j : ℝ)*((k : ℝ)-r) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg j)) (sub_nonneg.mpr hkr)
      have he := Real.exp_le_one_iff.mpr hp
      simp only [probe,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      nlinarith [abs_nonneg (f k)]
  have hl : ∀ᵐ k ∂poissonLaw rate,
      Tendsto (fun j => probe f r j k) atTop (𝓝 (if k=r then f r else 0)) := by
    apply Filter.Eventually.of_forall
    intro k
    by_cases hk : k=r
    · subst k
      simp only [probe,sub_self,mul_zero,Real.exp_zero,mul_one,if_pos rfl]
      exact tendsto_const_nhds
    · by_cases hkr : k<r
      · simp only [probe,hprev k hkr,zero_mul,if_neg hk]
        exact tendsto_const_nhds
      · have hlt : (r : ℝ) < k := by exact_mod_cast lt_of_le_of_ne (le_of_not_gt hkr) (Ne.symm hk)
        have he0 : 0 ≤ Real.exp (-((k : ℝ)-r)) := (Real.exp_pos _).le
        have he1 : Real.exp (-((k : ℝ)-r)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one he0 he1).const_mul (f k)
        have he (j : ℕ) : probe f r j k = f k*(Real.exp (-((k : ℝ)-r)))^j := by
          rw [probe,← Real.exp_nat_mul]
          congr 2
          ring
        simpa only [he,if_neg hk,mul_zero] using ht
  have hd := tendsto_integral_of_dominated_convergence (fun k => ‖f k‖)
    (fun j => by fun_prop : ∀ j, AEStronglyMeasurable (probe f r j) (poissonLaw rate))
    ((Lp.memLp f).integrable (by norm_num)).norm hb hl
  have hz' : Tendsto (fun j => ∫ k, probe f r j k ∂poissonLaw rate) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hi : (∫ k, (if k=r then f r else 0) ∂poissonLaw rate)=
      poissonWeight rate r*f r := by
    have he : (fun k : ℕ => if k=r then f r else 0) = Set.indicator {r} (fun _ : ℕ => f r) := by
      funext k
      simp [Set.indicator]
    rw [he,integral_indicator (measurableSet_singleton r),integral_singleton]
    rfl
  have hm := tendsto_nhds_unique hz' hd
  rw [hi] at hm
  exact (mul_eq_zero.mp hm.symm).resolve_left (ne_of_gt (poisson_weight_pos rate hr r))

theorem exponential_orthogonal_zero (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate)
    (horth : ∀ θ : ℝ, inner ℝ f (scalar rate θ)=0) : f=0 := by
  have he (r : ℕ) : f r=0 := by
    induction r using Nat.strong_induction_on with
    | h r ih => exact atom_zero rate hr f r ih horth
  apply Lp.ext
  filter_upwards [Lp.coeFn_zero ℝ 2 (poissonLaw rate)] with k hk
  simp only [Pi.zero_apply] at hk
  rw [hk,he]

def exponentialSpan (rate : ℝ≥0) : Submodule ℝ (ScalarL2 rate) :=
  Submodule.span ℝ (Set.range (scalar rate))

theorem exponentialSpan_closure (rate : ℝ≥0) (hr : 0 < rate) :
    (exponentialSpan rate).topologicalClosure=⊤ := by
  have hb : (exponentialSpan rate)ᗮ=⊥ := by
    apply le_antisymm
    · intro f hf
      change f=0
      apply exponential_orthogonal_zero rate hr f
      intro θ
      have hi := ((exponentialSpan rate).mem_orthogonal f).mp hf (scalar rate θ)
        (Submodule.subset_span ⟨θ,rfl⟩)
      simpa only [real_inner_comm] using hi
    · exact bot_le
  rw [← Submodule.orthogonal_orthogonal_eq_closure,hb,Submodule.bot_orthogonal_eq_top]

end OperatorDerivativeRewrite.Foundation.PoissonExponentialTotal
