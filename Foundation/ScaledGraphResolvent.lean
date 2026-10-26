import Foundation.ClosedOperatorEnergyResolvent
import Mathlib.Analysis.SpecificLimits.Basic

/-! Canonical dyadic regularization from existing closed-graph energy resolvents.
Strong identity approximation uses the actual dense domain; the unscaled native
derivative, exact adjoint correction, and weighted graph limits are retained. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ScaledGraphResolvent
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem smul_closed (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (a : ℝ) (ha : a ≠ 0) :
    (a • A).IsClosed := by
  have he : ((a • A).graph : Set (E × F)) =
      (fun z : E × F => (z.1,a⁻¹ • z.2)) ⁻¹' (A.graph : Set (E × F)) := by
    ext ⟨x,y⟩
    constructor
    · intro hz
      obtain ⟨u,hu,hv⟩ := (a • A).mem_graph_iff.mp hz
      refine A.mem_graph_iff.mpr ⟨u,hu,?_⟩
      rw [LinearPMap.smul_apply] at hv
      change A u = a⁻¹ • y
      change a • A u = y at hv
      rw [← hv,smul_smul,inv_mul_cancel₀ ha,one_smul]
    · intro hz
      obtain ⟨u,hu,hv⟩ := A.mem_graph_iff.mp hz
      refine (a • A).mem_graph_iff.mpr ⟨u,hu,?_⟩
      change a • A u = y
      rw [hv,smul_smul,mul_inv_cancel₀ ha,one_smul]
  change IsClosed ((a • A).graph : Set (E × F))
  rw [he]
  exact hA.preimage (continuous_fst.prodMk (continuous_snd.const_smul _))

def scale (n : ℕ) : ℝ := (1/2)^n

theorem scale_pos (n : ℕ) : 0 < scale n := pow_pos (by norm_num) n

theorem scale_tendsto : Tendsto scale atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

def regularize (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) : E →L[ℝ] E :=
  ClosedOperatorEnergyResolvent.resolvent (scale n • A)
    (smul_closed A hA _ (scale_pos n).ne')

theorem regularize_mem (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E) :
    regularize A hA n x ∈ A.domain := by
  change ClosedOperatorEnergyResolvent.resolvent (scale n • A)
    (smul_closed A hA _ (scale_pos n).ne') x ∈ (scale n • A).domain
  exact ClosedOperatorEnergyResolvent.resolvent_mem_domain (scale n • A)
    (smul_closed A hA _ (scale_pos n).ne') x

theorem regularize_contraction (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E) :
    ‖regularize A hA n x‖ ≤ ‖x‖ :=
  ClosedOperatorEnergyResolvent.resolvent_contraction _ _ x

theorem approximation_energy (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E) (u : A.domain) :
    ‖x-regularize A hA n x‖^2 ≤ ‖x-(u:E)‖^2+(scale n)^2*‖A u‖^2 := by
  have hm := ClosedOperatorEnergyResolvent.energy_minimum (scale n • A)
    (smul_closed A hA _ (scale_pos n).ne') x u
  change ‖x-regularize A hA n x‖^2 +
    ‖ClosedOperatorEnergyResolvent.gradient (scale n • A) _ x‖^2 ≤ _ at hm
  rw [LinearPMap.smul_apply,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] at hm
  linarith [sq_nonneg ‖ClosedOperatorEnergyResolvent.gradient (scale n • A)
    (smul_closed A hA _ (scale_pos n).ne') x‖]

theorem regularize_tendsto (A : E →ₗ.[ℝ] F) (hA : A.IsClosed)
    (hd : Dense (A.domain : Set E)) (x : E) :
    Tendsto (fun n => regularize A hA n x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨u,hu,hxu⟩ := hd.exists_dist_lt x (half_pos hε)
  have ht : Tendsto (fun n => (scale n)^2*‖A ⟨u,hu⟩‖^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2≠0),zero_mul] using
      (scale_tendsto.pow 2).mul_const (‖A ⟨u,hu⟩‖^2)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (ht.eventually (eventually_lt_nhds (by positivity : (0:ℝ)<ε^2/4)))
  refine ⟨N,fun n hn => ?_⟩
  have he := approximation_energy A hA n x ⟨u,hu⟩
  have hb := hN n hn
  rw [dist_eq_norm] at hxu ⊢
  have hsq : ‖x-u‖^2 < (ε/2)^2 := sq_lt_sq₀ (norm_nonneg _) (by positivity) |>.2 hxu
  rw [norm_sub_rev]
  nlinarith [norm_nonneg (x-regularize A hA n x)]

def nativeGradient (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E) : F :=
  A ⟨regularize A hA n x,regularize_mem A hA n x⟩

theorem scaled_gradient_eq (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E) :
    ClosedOperatorEnergyResolvent.gradient (scale n • A)
      (smul_closed A hA _ (scale_pos n).ne') x = scale n • nativeGradient A hA n x := by
  have h := ClosedOperatorEnergyResolvent.derivative_resolvent (scale n • A)
    (smul_closed A hA _ (scale_pos n).ne') x
  exact h.symm

theorem native_weak_identity (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E) (u : A.domain) :
    inner ℝ (regularize A hA n x) (u:E)+(scale n)^2*inner ℝ (nativeGradient A hA n x) (A u) =
      inner ℝ x (u:E) := by
  have h := ClosedOperatorEnergyResolvent.weak_identity (scale n • A)
    (smul_closed A hA _ (scale_pos n).ne') x u
  rw [scaled_gradient_eq A hA n x,LinearPMap.smul_apply,real_inner_smul_left,inner_smul_right] at h
  simpa only [regularize,pow_two,mul_assoc] using h

theorem weighted_gradient_mem_adjoint (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E) :
    (scale n)^2 • nativeGradient A hA n x ∈ A.adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists (T := A)
  refine ⟨x-regularize A hA n x,fun u => ?_⟩
  rw [inner_sub_left,real_inner_smul_left]
  linarith [native_weak_identity A hA n x u]

theorem native_adjoint_identity (A : E →ₗ.[ℝ] F) (hA : A.IsClosed)
    (hd : Dense (A.domain : Set E)) (n : ℕ) (x : E) :
    A.adjoint ⟨(scale n)^2 • nativeGradient A hA n x,weighted_gradient_mem_adjoint A hA n x⟩ =
      x-regularize A hA n x := by
  apply LinearPMap.adjoint_apply_eq hd
  intro u
  rw [inner_sub_left,real_inner_smul_left]
  linarith [native_weak_identity A hA n x u]

theorem scaled_gradient_bound (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E) :
    ‖scale n • nativeGradient A hA n x‖ ≤ ‖x‖ := by
  have he := ClosedOperatorEnergyResolvent.energy_identity (scale n • A)
    (smul_closed A hA _ (scale_pos n).ne') x
  rw [scaled_gradient_eq A hA n x] at he
  change ‖regularize A hA n x‖^2+‖scale n • nativeGradient A hA n x‖^2 =
    inner ℝ x (regularize A hA n x) at he
  have hb := real_inner_le_norm x (regularize A hA n x)
  have hr := regularize_contraction A hA n x
  nlinarith [norm_nonneg x,norm_nonneg (regularize A hA n x),
    norm_nonneg (scale n • nativeGradient A hA n x)]

theorem weighted_gradient_bound (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (n : ℕ) (x : E) :
    ‖(scale n)^2 • nativeGradient A hA n x‖ ≤ scale n*‖x‖ := by
  rw [pow_two,mul_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (scale_pos n)]
  exact mul_le_mul_of_nonneg_left (scaled_gradient_bound A hA n x) (scale_pos n).le

theorem weighted_gradient_tendsto_zero (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (x : E) :
    Tendsto (fun n => (scale n)^2 • nativeGradient A hA n x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => weighted_gradient_bound A hA n x)
  simpa only [zero_mul] using scale_tendsto.mul_const ‖x‖

end OperatorDerivativeRewrite.Foundation.ScaledGraphResolvent
