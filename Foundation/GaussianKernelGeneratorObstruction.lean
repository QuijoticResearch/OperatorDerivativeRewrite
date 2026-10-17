import Foundation.GaussianAcceleratedKernelLimit
import Foundation.ProjectionJumpSemigroup

/-! The actual limiting Gaussian kernel acts on bounded continuous observables
by an instantaneous mean projection. Its right generator domain is exactly the
constant observables and is not dense in the uniform norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.GaussianKernelGeneratorObstruction
open GaussianMehler GaussianAcceleratedKernelLimit ProjectionJumpSemigroup

def equilibrium : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.const ℝ (∫ y, f y ∂γ)
      map_add' := by
        intro f g
        ext x
        exact integral_add (f.integrable γ) (g.integrable γ)
      map_smul' := by
        intro c f
        ext x
        exact integral_smul c f }
    1 (fun f => by
      change ‖BoundedContinuousFunction.const ℝ (∫ y, f y ∂γ)‖ ≤ 1 * ‖f‖
      simpa only [BoundedContinuousFunction.norm_const_eq, one_mul] using
        f.norm_integral_le_norm γ)

theorem equilibrium_apply (f : ℝ →ᵇ ℝ) (x : ℝ) :
    equilibrium f x = ∫ y, f y ∂γ := rfl

theorem equilibrium_contractive (f : ℝ →ᵇ ℝ) : ‖equilibrium f‖ ≤ ‖f‖ := by
  change ‖BoundedContinuousFunction.const ℝ (∫ y, f y ∂γ)‖ ≤ ‖f‖
  rw [BoundedContinuousFunction.norm_const_eq]
  exact f.norm_integral_le_norm γ

theorem equilibrium_idempotent : equilibrium.comp equilibrium = equilibrium := by
  ext f x
  simp [equilibrium_apply]

def evolution (t : ℝ) : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) := jump equilibrium t

theorem evolution_integral (t : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    evolution t f x = ∫ y, f y ∂limitKernel t x := by
  rw [limit_integral]
  by_cases ht : t = 0 <;> simp [evolution, jump, ht, equilibrium_apply]

theorem evolution_zero : evolution 0 = ContinuousLinearMap.id ℝ (ℝ →ᵇ ℝ) := jump_zero _

theorem evolution_compose (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    evolution (s+t) = (evolution t).comp (evolution s) :=
  compose equilibrium equilibrium_idempotent s t hs ht

theorem evolution_contractive (t : ℝ) (f : ℝ →ᵇ ℝ) : ‖evolution t f‖ ≤ ‖f‖ :=
  contractive equilibrium equilibrium_contractive t f

theorem fixed_iff_constant (f : ℝ →ᵇ ℝ) :
    equilibrium f = f ↔ ∃ c : ℝ, f = BoundedContinuousFunction.const ℝ c := by
  constructor
  · intro hf
    exact ⟨∫ y, f y ∂γ, hf.symm⟩
  · rintro ⟨c, rfl⟩
    ext x
    simp [equilibrium_apply]

theorem continuous_iff_constant (f : ℝ →ᵇ ℝ) :
    ContinuousWithinAt (fun t => evolution t f) (Ici 0) 0 ↔
      ∃ c : ℝ, f = BoundedContinuousFunction.const ℝ c :=
  (continuous_iff_fixed equilibrium f).trans (fixed_iff_constant f)

theorem derivative_iff_constant (f v : ℝ →ᵇ ℝ) :
    HasDerivWithinAt (fun t => evolution t f) v (Ici 0) 0 ↔
      (∃ c : ℝ, f = BoundedContinuousFunction.const ℝ c) ∧ v = 0 := by
  exact (derivative_iff equilibrium f v).trans (and_congr_left (fun _ => fixed_iff_constant f))

theorem cosine_not_fixed : equilibrium cosine ≠ cosine := by
  intro he
  have hx := congrArg (fun f : ℝ →ᵇ ℝ => f 0) he
  rw [equilibrium_apply] at hx
  have hc0 : cosine 0 = 1 := by norm_num [cosine]
  rw [hc0] at hx
  exact (ne_of_lt cosine_mean_lt_one) hx

theorem cosine_jump_norm (t : ℝ) (ht : 0 < t) :
    ‖evolution t cosine - cosine‖ = 1 + Real.exp (-(1 : ℝ)/2) := by
  have he (x : ℝ) : (evolution t cosine - cosine) x =
      Real.exp (-(1 : ℝ)/2) - Real.cos x := by
    change evolution t cosine x - cosine x = _
    rw [evolution_integral, limit_integral]
    rw [if_neg (ne_of_gt ht), cosine_mean]
    rfl
  have hm : 0 ≤ Real.exp (-(1 : ℝ)/2) := (Real.exp_pos _).le
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    rw [he]
    calc
      ‖Real.exp (-(1 : ℝ)/2) - Real.cos x‖ ≤
          ‖Real.exp (-(1 : ℝ)/2)‖ + ‖Real.cos x‖ := norm_sub_le _ _
      _ ≤ Real.exp (-(1 : ℝ)/2) + 1 := by
        rw [Real.norm_of_nonneg hm]
        exact add_le_add_right (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x) _
      _ = _ := add_comm _ _
  · have hb := (evolution t cosine - cosine).norm_coe_le_norm Real.pi
    rw [he, Real.cos_pi] at hb
    rw [sub_neg_eq_add, Real.norm_of_nonneg (by positivity)] at hb
    linarith

theorem generator_domain_not_dense :
    ¬ Dense {f : ℝ →ᵇ ℝ |
      DifferentiableWithinAt ℝ (fun t => evolution t f) (Ici 0) 0} :=
  domain_not_dense equilibrium ⟨cosine, cosine_not_fixed⟩

theorem not_strongly_continuous :
    ¬ ∀ f : ℝ →ᵇ ℝ, ContinuousWithinAt (fun t => evolution t f) (Ici 0) 0 := by
  intro h
  exact cosine_not_fixed ((continuous_iff_fixed equilibrium cosine).mp (h cosine))

end OperatorDerivativeRewrite.Foundation.GaussianKernelGeneratorObstruction
