import Foundation.GaussianSobolevCutoffs
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Compact-support transfer from Gaussian to Lebesgue L². -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.GaussianSobolevSmoothApprox
abbrev γ : Measure ℝ := GaussianCore.γ

theorem compact_support_in_Icc {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, Function.support f ⊆ Icc (-R) R := by
  obtain ⟨R, hR⟩ := hf.isBounded.subset_closedBall 0
  refine ⟨R, ?_⟩
  intro x hx
  have hxb : x ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport f hx)
  rw [Metric.mem_closedBall, Real.dist_eq] at hxb
  simp only [sub_zero] at hxb
  exact abs_le.mp hxb

theorem compact_derivative_memLp_volume {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hc : HasCompactSupport f)
    (hh : Integrable (fun x => h x ^ 2) γ) :
    MemLp h 2 (volume : Measure ℝ) := by
  have hmeas : Measurable h := by
    rw [GaussianLocalSobolev.derivative_eq_deriv hd]
    exact measurable_deriv f
  have hmem : MemLp h 2 γ :=
    (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hh
  obtain ⟨R, hR⟩ := compact_support_in_Icc hc.deriv
  have hs : Function.support h ⊆ Icc (-R) R := by
    rw [GaussianLocalSobolev.derivative_eq_deriv hd]
    exact hR
  have hlocal := GaussianLocalSobolev.memLp_two_volume_restrict_Icc_of_memLp_gaussian
    (-R) R hmem
  have hglobal := (memLp_indicator_iff_restrict measurableSet_Icc).2 hlocal
  rwa [Set.indicator_eq_self.mpr hs] at hglobal



theorem compact_derivative_integrable_volume {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hc : HasCompactSupport f)
    (hh : Integrable (fun x => h x ^ 2) γ) :
    Integrable h (volume : Measure ℝ) := by
  obtain ⟨R, hR⟩ := compact_support_in_Icc hc.deriv
  have hs : Function.support h ⊆ Icc (-R) R := by
    rw [GaussianLocalSobolev.derivative_eq_deriv hd]
    exact hR
  have hlocal : IntegrableOn h (Icc (-R) R) volume :=
    (GaussianLocalSobolev.memLp_two_volume_restrict_Icc_of_memLp_gaussian
      (-R) R (by
        have hmeas : Measurable h := by
          rw [GaussianLocalSobolev.derivative_eq_deriv hd]
          exact measurable_deriv f
        exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hh)).integrable
      (by norm_num)
  exact (integrableOn_iff_integrable_of_support_subset hs).mp hlocal

theorem compact_derivative_integral_zero {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hc : HasCompactSupport f)
    (hh : Integrable (fun x => h x ^ 2) γ) :
    (∫ x, h x ∂(volume : Measure ℝ)) = 0 := by
  obtain ⟨Rf, hfR⟩ := compact_support_in_Icc hc
  obtain ⟨Rh, hhR⟩ := compact_support_in_Icc hc.deriv
  have hsupport : Function.support h ⊆ Icc (-Rh) Rh := by
    rw [GaussianLocalSobolev.derivative_eq_deriv hd]
    exact hhR
  let R : ℝ := max (max Rf Rh) 0 + 1
  have hRf_le : Rf < R := by dsimp [R]; linarith [le_max_left Rf Rh, le_max_left (max Rf Rh) 0]
  have hRh_le : Rh < R := by dsimp [R]; linarith [le_max_right Rf Rh, le_max_left (max Rf Rh) 0]
  have hRpos : 0 < R := by dsimp [R]; linarith [le_max_right (max Rf Rh) 0]
  have hfleft : f (-R) = 0 := by
    by_contra hz
    have hx : -R ∈ Function.support f := hz
    have := (hfR hx).1
    linarith
  have hfright : f R = 0 := by
    by_contra hz
    have hx : R ∈ Function.support f := hz
    have := (hfR hx).2
    linarith
  have hsIoc : Function.support h ⊆ Ioc (-R) R := by
    intro x hx
    have hx' := hsupport hx
    constructor <;> linarith [hx'.1, hx'.2]
  have hfull : (∫ x, h x ∂(volume : Measure ℝ)) = ∫ x in Ioc (-R) R, h x := by
    rw [← integral_indicator measurableSet_Ioc, Set.indicator_eq_self.mpr hsIoc]
  rw [hfull, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  rw [GaussianLocalSobolev.integral_derivative_eq_sub_of_gaussian_sq_integrable hd hh]
  simp [hfleft, hfright]



/-- A compactly supported everywhere-differentiable function is the actual
Lebesgue primitive of its derivative from a point left of its support. -/
theorem compact_primitive_representation {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hc : HasCompactSupport f)
    (hh : Integrable (fun x => h x ^ 2) γ) :
    ∃ a : ℝ, (∀ x ≤ a, f x = 0) ∧
      ∀ x, f x = ∫ y in a..x, h y := by
  obtain ⟨R, hR⟩ := compact_support_in_Icc hc
  refine ⟨-R - 1, ?_, ?_⟩
  · intro x hx
    by_contra hz
    have hmem : x ∈ Function.support f := hz
    have hbound := (hR hmem).1
    linarith
  · intro x
    have hzero : f (-R - 1) = 0 := by
      by_contra hz
      have hmem : -R - 1 ∈ Function.support f := hz
      have hbound := (hR hmem).1
      linarith
    rw [GaussianLocalSobolev.integral_derivative_eq_sub_of_gaussian_sq_integrable hd hh]
    simp [hzero]



/-- The actual derivative of every cutoff is square integrable under γ. -/
theorem truncated_derivative_sq_integrable {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hf_sq : Integrable (fun x => f x ^ 2) γ)
    (hh_sq : Integrable (fun x => h x ^ 2) γ)
    (n : ℕ) :
    Integrable (fun x => (deriv (GaussianSobolevCutoffs.truncated f n) x) ^ 2) γ := by
  have hfmeas : Measurable f :=
    (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).measurable
  have hhmeas : Measurable h := by
    rw [GaussianLocalSobolev.derivative_eq_deriv hd]
    exact measurable_deriv f
  have hflp : MemLp f 2 γ :=
    (memLp_two_iff_integrable_sq hfmeas.aestronglyMeasurable).2 hf_sq
  have hhlp : MemLp h 2 γ :=
    (memLp_two_iff_integrable_sq hhmeas.aestronglyMeasurable).2 hh_sq
  have hcut : MemLp (fun x => GaussianSobolevCutoffs.cutoff n x * h x) 2 γ := by
    apply hhlp.of_le_mul (c := 1)
      ((GaussianSobolevCutoffs.cutoff_contDiff n).continuous.measurable.mul
      hhmeas).aestronglyMeasurable
    filter_upwards [] with x
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (GaussianSobolevCutoffs.cutoff_bounds n x).1]
    rw [one_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (GaussianSobolevCutoffs.cutoff_bounds n x).2
  obtain ⟨C, hC, hbound⟩ := GaussianSobolevCutoffs.cutoff_derivative_bound
  have hderivcut : MemLp (fun x => deriv (GaussianSobolevCutoffs.cutoff n) x * f x) 2 γ := by
    apply hflp.of_le_mul (c := C) ((((GaussianSobolevCutoffs.cutoff_contDiff n).continuous_deriv
      (by norm_num)).measurable).mul hfmeas).aestronglyMeasurable
    filter_upwards [] with x
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    have hden : 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast (show 1 ≤ n + 1 by omega)
    have hle : |deriv (GaussianSobolevCutoffs.cutoff n) x| ≤ C :=
      (hbound n x).trans (div_le_self hC hden)
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hsum := hcut.add hderivcut
  have heq : (fun x => deriv (GaussianSobolevCutoffs.truncated f n) x) =
      (fun x => GaussianSobolevCutoffs.cutoff n x * h x) +
      (fun x => deriv (GaussianSobolevCutoffs.cutoff n) x * f x) := by
    funext x
    exact GaussianSobolevCutoffs.deriv_truncated hd n x
  have hmem : MemLp (fun x => deriv (GaussianSobolevCutoffs.truncated f n) x) 2 γ := by
    rw [heq]
    exact hsum
  exact (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem

/-- The truncated derivative has zero Lebesgue integral. -/
theorem truncated_derivative_integral_zero {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hf_sq : Integrable (fun x => f x ^ 2) γ)
    (hh_sq : Integrable (fun x => h x ^ 2) γ)
    (n : ℕ) :
    (∫ x, deriv (GaussianSobolevCutoffs.truncated f n) x ∂(volume : Measure ℝ)) = 0 := by
  have hdtr : ∀ x, HasDerivAt (GaussianSobolevCutoffs.truncated f n)
      (deriv (GaussianSobolevCutoffs.truncated f n) x) x := by
    intro x
    rw [GaussianSobolevCutoffs.deriv_truncated hd n x]
    exact GaussianSobolevCutoffs.hasDerivAt_truncated hd n x
  exact compact_derivative_integral_zero hdtr
    (GaussianSobolevCutoffs.truncated_compact f n)
    (truncated_derivative_sq_integrable hd hf_sq hh_sq n)


/-- Each cutoff is recovered from the Lebesgue primitive of its actual derivative
starting left of its compact support. -/
theorem truncated_primitive_representation {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hf_sq : Integrable (fun x => f x ^ 2) γ)
    (hh_sq : Integrable (fun x => h x ^ 2) γ)
    (n : ℕ) :
    ∃ a : ℝ,
      (∀ x ≤ a, GaussianSobolevCutoffs.truncated f n x = 0) ∧
      ∀ x, GaussianSobolevCutoffs.truncated f n x =
        ∫ y in a..x, deriv (GaussianSobolevCutoffs.truncated f n) y := by
  have hdtr : ∀ x, HasDerivAt (GaussianSobolevCutoffs.truncated f n)
      (deriv (GaussianSobolevCutoffs.truncated f n) x) x := by
    intro x
    rw [GaussianSobolevCutoffs.deriv_truncated hd n x]
    exact GaussianSobolevCutoffs.hasDerivAt_truncated hd n x
  exact compact_primitive_representation hdtr
    (GaussianSobolevCutoffs.truncated_compact f n)
    (truncated_derivative_sq_integrable hd hf_sq hh_sq n)

end OperatorDerivativeRewrite.Foundation.GaussianSobolevSmoothApprox
