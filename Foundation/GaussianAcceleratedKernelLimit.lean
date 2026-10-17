import Foundation.GaussianMehlerKernel
import Foundation.AcceleratedDecayBoundary
import Foundation.TriadGaussianDephasing
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Weak row convergence of actual accelerated Mehler kernels to an invariant
Markov kernel semigroup that is not stochastically continuous at time zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.GaussianAcceleratedKernelLimit
open GaussianMehler GaussianMehlerKernel AcceleratedDecayBoundary

def acceleratedKernel (n : ℕ) (t : ℝ) : Kernel ℝ ℝ := kernel (rate n*t)

instance accelerated_markov (n : ℕ) (t : ℝ) : IsMarkovKernel (acceleratedKernel n t) :=
  kernel_markov _

theorem accelerated_zero (n : ℕ) : acceleratedKernel n 0 = Kernel.id := by
  simp [acceleratedKernel, kernel_zero]

theorem accelerated_compose (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    acceleratedKernel n (s+t) = acceleratedKernel n t ∘ₖ acceleratedKernel n s := by
  unfold acceleratedKernel
  rw [mul_add]
  exact kernel_compose _ _ (mul_nonneg (rate_positive n).le hs) (mul_nonneg (rate_positive n).le ht)

theorem accelerated_invariant (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : acceleratedKernel n t ∘ₘ γ = γ :=
  kernel_invariant _ (mul_nonneg (rate_positive n).le ht)

def limitKernel (t : ℝ) : Kernel ℝ ℝ := if t = 0 then Kernel.id else Kernel.const ℝ γ

instance limit_markov (t : ℝ) : IsMarkovKernel (limitKernel t) := by
  unfold limitKernel
  split_ifs <;> infer_instance

theorem limit_zero : limitKernel 0 = Kernel.id := by simp [limitKernel]

theorem limit_positive (t : ℝ) (ht : 0 < t) : limitKernel t = Kernel.const ℝ γ := by
  simp [limitKernel, ne_of_gt ht]

theorem limit_compose (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    limitKernel (s+t) = limitKernel t ∘ₖ limitKernel s := by
  by_cases hsz : s = 0
  · subst s
    simp [limit_zero]
  by_cases htz : t = 0
  · subst t
    simp [limit_zero]
  have hst : s+t ≠ 0 := ne_of_gt (add_pos (lt_of_le_of_ne hs (Ne.symm hsz))
    (lt_of_le_of_ne ht (Ne.symm htz)))
  simp [limitKernel, hsz, htz, hst]

theorem limit_invariant (t : ℝ) : limitKernel t ∘ₘ γ = γ := by
  rw [Measure.comp_eq_comp_const_apply]
  by_cases hz : t = 0
  · simp [limitKernel, hz, Kernel.id_comp]
  · simp [limitKernel, hz, Kernel.const_comp']

theorem limit_integral (t x : ℝ) (f : ℝ → ℝ) :
    (∫ y, f y ∂limitKernel t x) = if t = 0 then f x else ∫ y, f y ∂γ := by
  by_cases hz : t = 0 <;> simp [limitKernel, hz, Kernel.id_apply, Kernel.const_apply]

theorem accelerated_integral_limit (t : ℝ) (ht : 0 ≤ t) (x : ℝ)
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ y, f y ∂acceleratedKernel n t x) atTop
      (𝓝 (∫ y, f y ∂limitKernel t x)) := by
  by_cases hz : t = 0
  · subst t
    simp only [accelerated_zero, limit_zero]
    exact tendsto_const_nhds
  have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
  have hr : Tendsto (fun n => rate n*t) atTop atTop := rate_tendsto.atTop_mul_const hp
  have h := (mehler_tendsto_mean f.continuous f.norm_coe_le_norm x).comp hr
  simpa only [acceleratedKernel, Function.comp_def, integral_kernel _ _ f.continuous,
    limit_integral, if_neg hz] using h

def acceleratedRow (n : ℕ) (t x : ℝ) : ProbabilityMeasure ℝ :=
  ⟨acceleratedKernel n t x, inferInstance⟩

def limitRow (t x : ℝ) : ProbabilityMeasure ℝ := ⟨limitKernel t x, inferInstance⟩

theorem weak_row_limit (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    Tendsto (fun n => acceleratedRow n t x) atTop (𝓝 (limitRow t x)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  exact accelerated_integral_limit t ht x f

theorem accelerated_row_time_continuous (n : ℕ) (x : ℝ) :
    Continuous (fun t => acceleratedRow n t x) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  exact (time_continuous f.continuous f.norm_coe_le_norm x).comp
    (continuous_const.mul continuous_id)

def cosine : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
  Real.cos Real.continuous_cos 1 (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)

theorem cosine_mean : (∫ y, cosine y ∂γ) = Real.exp (-(1 : ℝ)/2) := by
  simpa [cosine] using TriadGaussianDephasing.gaussian_cosine (1 : ℝ)

theorem cosine_mean_lt_one : (∫ y, cosine y ∂γ) < 1 := by
  rw [cosine_mean]
  exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem limit_cosine_not_right_continuous :
    ¬ ContinuousWithinAt (fun t => ∫ y, cosine y ∂limitKernel t 0) (Ici 0) 0 := by
  let m : ℝ := Real.exp (-(1 : ℝ)/2)
  have hm : 1-m ≠ 0 := by
    have h := cosine_mean_lt_one
    rw [cosine_mean] at h
    dsimp [m]
    linarith
  have he : (fun t => (∫ y, cosine y ∂limitKernel t 0)-m) =
      fun t => boundaryLimit (fun (_ : ℝ) (_ : Unit) => 1-m) t () := by
    funext t
    rw [limit_integral]
    have hc0 : cosine 0 = 1 := by norm_num [cosine]
    by_cases ht : t = 0 <;> simp [boundaryLimit, ht, cosine_mean, hc0, m]
  intro hc
  have hcenter : ContinuousWithinAt (fun t => (∫ y, cosine y ∂limitKernel t 0)-m)
      (Ici 0) 0 := hc.sub continuousWithinAt_const
  rw [he] at hcenter
  exact boundary_not_right_continuous (fun (_ : ℝ) (_ : Unit) => 1-m) () hm hcenter

theorem limit_row_not_right_continuous :
    ¬ ContinuousWithinAt (fun t => limitRow t 0) (Ici 0) 0 := by
  intro hc
  have h := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction cosine).continuousAt
    |>.comp_continuousWithinAt hc
  exact limit_cosine_not_right_continuous h

end OperatorDerivativeRewrite.Foundation.GaussianAcceleratedKernelLimit
