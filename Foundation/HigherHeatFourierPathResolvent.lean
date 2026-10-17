import Foundation.HigherHeatFourierPathClosure

/-! The actual bounded unit resolvent of the Fourier path heat operator. -/
noncomputable section
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathResolvent
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatFourierBanach
open HigherHeatFourierPathDerivative HigherHeatFourierPathGenerator HigherHeatFourierPathClosure

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def weight (m : ℕ) (i : ℕ) : ℂ := ((1 + rate levels ξ m i)⁻¹ : ℝ)

theorem weight_bound (m : ℕ) (i : ℕ) : ‖weight levels ξ m i‖ ≤ 1 := by
  have hr := rate_nonneg levels ξ m i
  rw [weight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (inv_le_one₀ (by positivity : 0 < 1 + rate levels ξ m i)).mpr (by linarith)

theorem weight_relation (m : ℕ) (i : ℕ) :
    weight levels ξ m i - 1 = weight levels ξ m i * ((-rate levels ξ m i : ℝ) : ℂ) := by
  have hr := rate_nonneg levels ξ m i
  have he : (1 + rate levels ξ m i)⁻¹ - 1 =
      (1 + rate levels ξ m i)⁻¹ * (-rate levels ξ m i) := by
    field_simp
    <;> ring
  unfold weight
  exact_mod_cast he

def coefficientResolvent (m : ℕ) : Coeff →L[ℂ] Coeff :=
  lp.mapCLM 1 (term (weight levels ξ m)) zero_le_one
    (term_norm_le _ (weight_bound levels ξ m))

theorem coefficientResolvent_apply (m : ℕ) (a : Coeff) (i : ℕ) :
    coefficientResolvent levels ξ m a i = a i * weight levels ξ m i := rfl

theorem coefficientResolvent_bound (m : ℕ) (a : Coeff) :
    ‖coefficientResolvent levels ξ m a‖ ≤ ‖a‖ := by
  have hn : ‖coefficientResolvent levels ξ m‖ ≤ 1 := lp.norm_mapCLM_le 1 _ _ _
  simpa only [one_mul] using (coefficientResolvent levels ξ m).le_of_opNorm_le hn a

theorem coefficientResolvent_graph (m : ℕ) (a : Coeff) :
    (coefficientResolvent levels ξ m a, coefficientResolvent levels ξ m a - a) ∈
      coefficientGraph levels ξ m := by
  intro i
  change a i * weight levels ξ m i - a i =
    (a i * weight levels ξ m i) * ((-rate levels ξ m i : ℝ) : ℂ)
  calc
    _ = a i * (weight levels ξ m i - 1) := by ring
    _ = _ := by rw [weight_relation]; ring

theorem coefficientResolvent_preserves_kernel (m : ℕ) (hm : 0 < m)
    (a : Coeff) (ha : a ∈ kernel levels ξ) :
    coefficientResolvent levels ξ m a ∈ kernel levels ξ := by
  have hqa : (kernel levels ξ).mkQ a = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ha
  have hg : ((kernel levels ξ).mkQ (coefficientResolvent levels ξ m a),
      (kernel levels ξ).mkQ (coefficientResolvent levels ξ m a - a)) ∈ graph levels ξ m :=
    ⟨_, coefficientResolvent_graph levels ξ m a, rfl⟩
  rw [map_sub, hqa, sub_zero] at hg
  have hb := graph_bound levels ξ m hm 1 (by norm_num) _ hg
  simp only [one_mul, one_smul, sub_self, norm_zero, norm_le_zero_iff] at hb
  exact (Submodule.Quotient.mk_eq_zero _).mp hb

theorem resolvent_kernel (m : ℕ) (hm : 0 < m) :
    kernel levels ξ ≤ (((kernel levels ξ).mkQL).comp (coefficientResolvent levels ξ m)).ker := by
  intro a ha
  change (kernel levels ξ).mkQ (coefficientResolvent levels ξ m a) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (coefficientResolvent_preserves_kernel levels ξ m hm a ha)

def resolvent (m : ℕ) (hm : 0 < m) : TestSpace levels ξ →L[ℂ] TestSpace levels ξ :=
  (kernel levels ξ).liftQL (((kernel levels ξ).mkQL).comp (coefficientResolvent levels ξ m))
    (resolvent_kernel levels ξ m hm)

theorem resolvent_mk (m : ℕ) (hm : 0 < m) (a : Coeff) :
    resolvent levels ξ m hm ((kernel levels ξ).mkQ a) =
      (kernel levels ξ).mkQ (coefficientResolvent levels ξ m a) := rfl

theorem resolvent_graph (m : ℕ) (hm : 0 < m) (f : TestSpace levels ξ) :
    (resolvent levels ξ m hm f, resolvent levels ξ m hm f - f) ∈ graph levels ξ m := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective f
  rw [resolvent_mk, ← map_sub]
  exact ⟨_, coefficientResolvent_graph levels ξ m a, rfl⟩

theorem resolvent_bound (m : ℕ) (hm : 0 < m) (f : TestSpace levels ξ) :
    ‖resolvent levels ξ m hm f‖ ≤ ‖f‖ := by
  have hb := graph_bound levels ξ m hm 1 (by norm_num) _ (resolvent_graph levels ξ m hm f)
  simpa only [one_mul, one_smul, sub_sub_cancel] using hb

theorem unit_minus_surjective (m : ℕ) (hm : 0 < m) (f : TestSpace levels ξ) :
    ∃ x v, (x,v) ∈ graph levels ξ m ∧ x-v=f := by
  exact ⟨_, _, resolvent_graph levels ξ m hm f, sub_sub_cancel _ _⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathResolvent
