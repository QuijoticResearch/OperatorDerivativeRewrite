import Foundation.GaussianSobolevPrimitives
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Quantitative fixed-support Gaussian Sobolev smoothing with actual derivatives. -/
noncomputable section
open MeasureTheory Set
open ProbabilityTheory
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianSobolevFixedSupport

theorem cs_setIntegral (A B : ℝ) (hAB : A ≤ B) {u : ℝ → ℝ}
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Icc A B))) :
    |∫ x in Icc A B, u x ∂(volume : Measure ℝ)| ≤
      Real.sqrt (B - A) *
        Real.sqrt (∫ x in Icc A B, u x ^ 2 ∂(volume : Measure ℝ)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Icc A B)
  have : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hμ : μ Set.univ = ENNReal.ofReal (B - A) := by
    simp [μ, Real.volume_Icc]
  have hconst : MemLp (fun _ : ℝ => (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ)
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hcs := integral_mul_norm_le_Lp_mul_Lq hholder
    (by simpa using hu) hconst
  simp only [Real.norm_eq_abs, abs_one, mul_one, integral_const] at hcs
  have hμreal : μ.real Set.univ = B - A := by
    rw [measureReal_def, hμ, ENNReal.toReal_ofReal (sub_nonneg.mpr hAB)]
  have hnorm := norm_integral_le_integral_norm (μ := μ) u
  calc
    |∫ x in Icc A B, u x ∂(volume : Measure ℝ)| =
        ‖∫ x, u x ∂μ‖ := by simp [μ, Real.norm_eq_abs]
    _ ≤ ∫ x, ‖u x‖ ∂μ := hnorm
    _ ≤ (∫ x, |u x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (μ.real Set.univ • (1 : ℝ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hcs
    _ = Real.sqrt (B - A) *
          Real.sqrt (∫ x in Icc A B, u x ^ 2 ∂(volume : Measure ℝ)) := by
      simp [hμreal, Real.sqrt_eq_rpow, sq_abs, μ, mul_comm]

def L2Norm (u : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ x, u x ^ 2 ∂(volume : Measure ℝ))

theorem L2Norm_eq_eLpNorm {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume : Measure ℝ)) :
    L2Norm u = (eLpNorm u 2 (volume : Measure ℝ)).toReal := by
  rw [hu.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num [L2Norm, Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  exact (ENNReal.toReal_ofReal
    (Real.rpow_nonneg (integral_nonneg (fun x => sq_nonneg (u x))) _)).symm

theorem cs_integral_of_support (A B : ℝ) (hAB : A ≤ B) {u : ℝ → ℝ}
    (hs : Function.support u ⊆ Icc A B)
    (hu : MemLp u 2 (volume : Measure ℝ)) :
    |∫ x, u x ∂(volume : Measure ℝ)| ≤ Real.sqrt (B - A) * L2Norm u := by
  have hsq : Function.support (fun x => u x ^ 2) ⊆ Icc A B := by
    intro x hx
    apply hs
    intro hu0
    simp [hu0] at hx
  have hint : (∫ x, u x ∂(volume : Measure ℝ)) =
      ∫ x in Icc A B, u x ∂(volume : Measure ℝ) := by
    rw [← integral_indicator measurableSet_Icc, Set.indicator_eq_self.mpr hs]
  have hsqint : (∫ x, u x ^ 2 ∂(volume : Measure ℝ)) =
      ∫ x in Icc A B, u x ^ 2 ∂(volume : Measure ℝ) := by
    rw [← integral_indicator measurableSet_Icc, Set.indicator_eq_self.mpr hsq]
  rw [hint, L2Norm, hsqint]
  exact cs_setIntegral A B hAB (hu.restrict _)

theorem integral_v_bound (A B : ℝ) (hAB : A ≤ B) {h v : ℝ → ℝ}
    (hh : MemLp h 2 (volume : Measure ℝ))
    (hv : MemLp v 2 (volume : Measure ℝ))
    (hhs : Function.support h ⊆ Icc A B)
    (hvs : Function.support v ⊆ Icc A B)
    (hzero : (∫ x, h x ∂(volume : Measure ℝ)) = 0) :
    |∫ x, v x ∂(volume : Measure ℝ)| ≤
      Real.sqrt (B - A) * L2Norm (v - h) := by
  have hhi := integrable_of_memLp_two_support hhs hh
  have hvi := integrable_of_memLp_two_support hvs hv
  have hsubsupport : Function.support (v - h) ⊆ Icc A B := by
    intro x hx
    by_contra hxK
    have hv0 : v x = 0 := by
      by_contra hn
      exact hxK (hvs hn)
    have hh0 : h x = 0 := by
      by_contra hn
      exact hxK (hhs hn)
    exact hx (by simp [hv0, hh0])
  calc
    |∫ x, v x ∂(volume : Measure ℝ)| =
        |∫ x, (v - h) x ∂(volume : Measure ℝ)| := by
          simp only [Pi.sub_apply]
          rw [integral_sub hvi hhi, hzero, sub_zero]
    _ ≤ Real.sqrt (B - A) * L2Norm (v - h) :=
      cs_integral_of_support A B hAB hsubsupport (hv.sub hh)

theorem L2Norm_sub_le {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    L2Norm (f - g) ≤ L2Norm f + L2Norm g := by
  rw [L2Norm_eq_eLpNorm (hf.sub hg), L2Norm_eq_eLpNorm hf,
    L2Norm_eq_eLpNorm hg]
  exact lpNorm_sub_le hf (by norm_num)

theorem L2Norm_const_mul {q : ℝ → ℝ}
    (hq : MemLp q 2 (volume : Measure ℝ)) (c : ℝ) :
    L2Norm (fun x => c * q x) = |c| * L2Norm q := by
  rw [L2Norm_eq_eLpNorm (hq.const_mul c), L2Norm_eq_eLpNorm hq]
  have hfun : (c • q) = (fun x => c * q x) := by
    funext x
    simp [Pi.smul_apply, smul_eq_mul]
  have h := lpNorm_const_smul (p := 2) c q (volume : Measure ℝ)
  rw [hfun] at h
  simpa [lpNorm, Real.norm_eq_abs] using h

theorem correction_error (A B : ℝ) (hAB : A ≤ B) {h v q : ℝ → ℝ}
    (hh : MemLp h 2 (volume : Measure ℝ))
    (hv : MemLp v 2 (volume : Measure ℝ))
    (hq : MemLp q 2 (volume : Measure ℝ))
    (hhs : Function.support h ⊆ Icc A B)
    (hvs : Function.support v ⊆ Icc A B)
    (hzero : (∫ x, h x ∂(volume : Measure ℝ)) = 0) :
    L2Norm (corrected v q - h) ≤
      (1 + Real.sqrt (B - A) * L2Norm q) * L2Norm (v - h) := by
  let c : ℝ := ∫ x, v x ∂(volume : Measure ℝ)
  have hnormq : 0 ≤ L2Norm q := Real.sqrt_nonneg _
  have hrewrite : corrected v q - h =
      (v - h) - (fun x => c * q x) := by
    funext x
    simp [corrected, c]
    ring
  rw [hrewrite]
  calc
    L2Norm ((v - h) - fun x => c * q x) ≤
        L2Norm (v - h) + L2Norm (fun x => c * q x) :=
          L2Norm_sub_le (hv.sub hh) (hq.const_mul c)
    _ = L2Norm (v - h) + |c| * L2Norm q := by rw [L2Norm_const_mul hq]
    _ ≤ L2Norm (v - h) +
          (Real.sqrt (B - A) * L2Norm (v - h)) * L2Norm q := by
            exact add_le_add_right
              (mul_le_mul_of_nonneg_right
                (integral_v_bound A B hAB hh hv hhs hvs hzero) hnormq) _
    _ = (1 + Real.sqrt (B - A) * L2Norm q) * L2Norm (v - h) := by ring

theorem primitive_error_on_Icc (A B : ℝ) {h w : ℝ → ℝ}
    (hh : MemLp h 2 (volume : Measure ℝ))
    (hw : MemLp w 2 (volume : Measure ℝ))
    (hhs : Function.support h ⊆ Icc A B)
    (hws : Function.support w ⊆ Icc A B)
    {x : ℝ} (hx : x ∈ Icc A B) :
    |primitive A w x - primitive A h x| ≤
      Real.sqrt (B - A) * L2Norm (w - h) := by
  have hhi := integrable_of_memLp_two_support hhs hh
  have hwi := integrable_of_memLp_two_support hws hw
  have hu : MemLp (w - h) 2 (volume : Measure ℝ) := hw.sub hh
  have husq : Integrable (fun y => ((w - h) y) ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).1 hu
  have hcs := cs_setIntegral A x hx.1 (hu.restrict (Icc A x))
  have hsqle : (∫ y in Icc A x, ((w - h) y) ^ 2 ∂(volume : Measure ℝ)) ≤
      ∫ y, ((w - h) y) ^ 2 ∂(volume : Measure ℝ) := by
    exact setIntegral_le_integral husq (Filter.Eventually.of_forall (fun y => sq_nonneg _))
  calc
    |primitive A w x - primitive A h x| =
        |∫ y in Icc A x, (w - h) y ∂(volume : Measure ℝ)| := by
          simp only [primitive]
          rw [← intervalIntegral.integral_sub hwi.intervalIntegrable hhi.intervalIntegrable,
            intervalIntegral.integral_of_le hx.1, integral_Icc_eq_integral_Ioc]
          simp only [Pi.sub_apply]
    _ ≤ Real.sqrt (x - A) *
          Real.sqrt (∫ y in Icc A x, ((w - h) y) ^ 2 ∂(volume : Measure ℝ)) := hcs
    _ ≤ Real.sqrt (B - A) * L2Norm (w - h) := by
          unfold L2Norm
          gcongr
          exact hx.2

theorem primitive_change_base {w : ℝ → ℝ} {A B a : ℝ}
    (ha : a < A) (hs : Function.support w ⊆ Icc A B)
    (hi : Integrable w (volume : Measure ℝ)) (x : ℝ) :
    primitive a w x = primitive A w x := by
  have hzero := primitive_zero_left ha (le_refl A) hs
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable : IntervalIntegrable w volume a A)
    (hi.intervalIntegrable : IntervalIntegrable w volume A x)
  change (∫ y in a..A, w y) = 0 at hzero
  change (∫ y in a..x, w y) = (∫ y in A..x, w y)
  simpa [hzero] using hadd.symm

theorem primitive_error_on_Icc_from_left (A B a : ℝ) (ha : a < A)
    {h w : ℝ → ℝ}
    (hh : MemLp h 2 (volume : Measure ℝ))
    (hw : MemLp w 2 (volume : Measure ℝ))
    (hhs : Function.support h ⊆ Icc A B)
    (hws : Function.support w ⊆ Icc A B)
    {x : ℝ} (hx : x ∈ Icc A B) :
    |primitive a w x - primitive a h x| ≤
      Real.sqrt (B - A) * L2Norm (w - h) := by
  rw [primitive_change_base ha hws (integrable_of_memLp_two_support hws hw) x,
      primitive_change_base ha hhs (integrable_of_memLp_two_support hhs hh) x]
  exact primitive_error_on_Icc A B hh hw hhs hws hx

theorem standard_gaussian_le_volume :
    GaussianCore.γ ≤ (volume : Measure ℝ) := by
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
    rw [gaussianPDFReal_def]
    have hπ : 1 ≤ (2 : ℝ) * Real.pi := by
      have := Real.two_le_pi
      linarith
    have hsqrt : 1 ≤ Real.sqrt ((2 : ℝ) * Real.pi) :=
      Real.one_le_sqrt.mpr hπ
    have hinv : (Real.sqrt ((2 : ℝ) * Real.pi))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hsqrt
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    have hcoef : 0 ≤ (Real.sqrt ((2 : ℝ) * Real.pi))⁻¹ := by positivity
    simpa using (mul_le_mul hinv hexp (Real.exp_nonneg _) (by norm_num)).trans (by norm_num)
  have hpdf' (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
    rw [gaussianPDF_def]
    simpa using ENNReal.ofReal_le_ofReal (hpdf x)
  have hγ : GaussianCore.γ =
      (volume : Measure ℝ).withDensity (gaussianPDF 0 1) := by
    rw [GaussianCore.γ, gaussianReal_of_var_ne_zero 0 (by norm_num)]
  calc
    GaussianCore.γ = (volume : Measure ℝ).withDensity (gaussianPDF 0 1) := hγ
    _ ≤ (volume : Measure ℝ).withDensity 1 := by
      apply withDensity_mono
      exact Filter.Eventually.of_forall hpdf'
    _ = volume := withDensity_one

theorem gaussian_sq_error_le_volume {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume : Measure ℝ)) :
    Integrable (fun x => u x ^ 2) GaussianCore.γ ∧
      (∫ x, u x ^ 2 ∂GaussianCore.γ) ≤ L2Norm u ^ 2 := by
  have huγ : MemLp u 2 GaussianCore.γ := hu.mono_measure standard_gaussian_le_volume
  have hvi : Integrable (fun x => u x ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).1 hu
  have hγi : Integrable (fun x => u x ^ 2) GaussianCore.γ :=
    (memLp_two_iff_integrable_sq huγ.aestronglyMeasurable).1 huγ
  refine ⟨hγi, ?_⟩
  have hle : (∫ x, u x ^ 2 ∂GaussianCore.γ) ≤
      ∫ x, u x ^ 2 ∂(volume : Measure ℝ) :=
    integral_mono_measure standard_gaussian_le_volume
      (Filter.Eventually.of_forall fun x => sq_nonneg (u x)) hvi
  simpa [L2Norm, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (u x)))] using hle

theorem primitive_error_global (A B a : ℝ) (ha : a < A)
    {h w : ℝ → ℝ}
    (hh : MemLp h 2 (volume : Measure ℝ))
    (hw : MemLp w 2 (volume : Measure ℝ))
    (hhs : Function.support h ⊆ Icc A B)
    (hws : Function.support w ⊆ Icc A B)
    (hhzero : (∫ x, h x ∂(volume : Measure ℝ)) = 0)
    (hwzero : (∫ x, w x ∂(volume : Measure ℝ)) = 0) (x : ℝ) :
    |primitive a w x - primitive a h x| ≤
      Real.sqrt (B - A) * L2Norm (w - h) := by
  by_cases hxK : x ∈ Icc A B
  · exact primitive_error_on_Icc_from_left A B a ha hh hw hhs hws hxK
  · have hnonneg : 0 ≤ Real.sqrt (B - A) * L2Norm (w - h) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    by_cases hxA : x ≤ A
    · simpa [primitive_zero_left ha hxA hws,
        primitive_zero_left ha hxA hhs] using hnonneg
    · have hxB : B ≤ x := by
        by_contra hn
        exact hxK ⟨le_of_lt (lt_of_not_ge hxA), le_of_lt (lt_of_not_ge hn)⟩
      simpa [primitive_zero_right ha hxB hws hwzero,
        primitive_zero_right ha hxB hhs hhzero] using hnonneg

theorem primitive_gaussian_sq_error (A B a : ℝ) (ha : a < A) (hAB : A ≤ B)
    {h w : ℝ → ℝ}
    (hh : MemLp h 2 (volume : Measure ℝ))
    (hw : MemLp w 2 (volume : Measure ℝ))
    (hhs : Function.support h ⊆ Icc A B)
    (hws : Function.support w ⊆ Icc A B)
    (hhzero : (∫ x, h x ∂(volume : Measure ℝ)) = 0)
    (hwzero : (∫ x, w x ∂(volume : Measure ℝ)) = 0) :
    Integrable (fun x => (primitive a w x - primitive a h x) ^ 2) GaussianCore.γ ∧
      (∫ x, (primitive a w x - primitive a h x) ^ 2 ∂GaussianCore.γ) ≤
        (B - A) * L2Norm (w - h) ^ 2 := by
  let C := Real.sqrt (B - A) * L2Norm (w - h)
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hwcont : Continuous (primitive a w) :=
    (integrable_of_memLp_two_support hws hw).continuous_primitive a
  have hhcont : Continuous (primitive a h) :=
    (integrable_of_memLp_two_support hhs hh).continuous_primitive a
  have hmeas : AEStronglyMeasurable
      (fun x => (primitive a w x - primitive a h x) ^ 2) GaussianCore.γ :=
    ((hwcont.measurable.sub hhcont.measurable).pow_const 2).aestronglyMeasurable
  have hpoint (x : ℝ) : (primitive a w x - primitive a h x) ^ 2 ≤ C ^ 2 := by
    have hb := primitive_error_global A B a ha hh hw hhs hws hhzero hwzero x
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 hb
  have hint : Integrable (fun x => (primitive a w x - primitive a h x) ^ 2)
      GaussianCore.γ := by
    apply Integrable.mono' (integrable_const (C ^ 2)) hmeas
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  refine ⟨hint, ?_⟩
  have hle := integral_mono hint (integrable_const (C ^ 2)) hpoint
  simpa [C, mul_pow, Real.sq_sqrt (sub_nonneg.mpr hAB)] using hle

theorem actual_derivative_support_in_Icc {f h : ℝ → ℝ} {A B : ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hfs : Function.support f ⊆ Icc A B) :
    Function.support h ⊆ Icc A B := by
  rw [GaussianLocalSobolev.derivative_eq_deriv hd]
  exact support_deriv_subset.trans (closure_minimal hfs isClosed_Icc)

theorem actual_primitive_from_left {f h : ℝ → ℝ} {A B a : ℝ}
    (ha : a < A) (hd : ∀ x, HasDerivAt f (h x) x)
    (hfs : Function.support f ⊆ Icc A B)
    (hh_sq : Integrable (fun x => h x ^ 2) GaussianCore.γ) :
    ∀ x, f x = primitive a h x := by
  have hfa : f a = 0 := by
    by_contra hn
    have hmem := hfs hn
    linarith [hmem.1]
  intro x
  unfold primitive
  rw [GaussianLocalSobolev.integral_derivative_eq_sub_of_gaussian_sq_integrable
    hd hh_sq a x, hfa, sub_zero]

theorem fixed_support_graph_error (A B a : ℝ) (ha : a < A) (hAB : A ≤ B)
    {f h w : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hfs : Function.support f ⊆ Icc A B)
    (hh_sq : Integrable (fun x => h x ^ 2) GaussianCore.γ)
    (hw : ContDiff ℝ ∞ w)
    (hws : Function.support w ⊆ Icc A B)
    (hwzero : (∫ x, w x ∂(volume : Measure ℝ)) = 0) :
    Integrable (fun x => (primitive a w x - f x) ^ 2) GaussianCore.γ ∧
      (∫ x, (primitive a w x - f x) ^ 2 ∂GaussianCore.γ) ≤
        (B - A) * L2Norm (w - h) ^ 2 ∧
    Integrable (fun x => (deriv (primitive a w) x - h x) ^ 2) GaussianCore.γ ∧
      (∫ x, (deriv (primitive a w) x - h x) ^ 2 ∂GaussianCore.γ) ≤
        L2Norm (w - h) ^ 2 := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hfs
  have hhs := actual_derivative_support_in_Icc hd hfs
  have hhLp : MemLp h 2 (volume : Measure ℝ) :=
    GaussianSobolevSmoothApprox.compact_derivative_memLp_volume hd hfc hh_sq
  have hwLp : MemLp w 2 (volume : Measure ℝ) :=
    hw.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hws)
  have hhzero := GaussianSobolevSmoothApprox.compact_derivative_integral_zero
    hd hfc hh_sq
  have hrep := actual_primitive_from_left ha hd hfs hh_sq
  have hder : ∀ x, deriv (primitive a w) x = w x :=
    deriv_primitive hw.continuous a
  have hfun := primitive_gaussian_sq_error A B a ha hAB hhLp hwLp hhs hws hhzero hwzero
  have hgrad := gaussian_sq_error_le_volume (hwLp.sub hhLp)
  simp_rw [hrep] at *
  simpa only [hder, Pi.sub_apply] using
    (And.intro hfun.1 (And.intro hfun.2 (And.intro hgrad.1 hgrad.2)))

private theorem exists_tolerance_for_graph (K M tol : ℝ)
    (htol : 0 < tol) :
    ∃ ε : ℝ, 0 < ε ∧ K * (M * ε) ^ 2 < tol ∧ (M * ε) ^ 2 < tol := by
  let C := max (K * M ^ 2) (M ^ 2)
  have hC : 0 ≤ C := le_trans (sq_nonneg M) (le_max_right _ _)
  obtain ⟨δ, hδ, hCδ⟩ := exists_pos_mul_lt htol C
  let ε : ℝ := min δ 1
  have hε : 0 < ε := lt_min hδ zero_lt_one
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hbound : C * ε ^ 2 < tol :=
    (mul_le_mul_of_nonneg_left hε2 hC).trans_lt
      ((mul_le_mul_of_nonneg_left hεδ hC).trans_lt hCδ)
  refine ⟨ε, hε, ?_, ?_⟩
  · calc
      K * (M * ε) ^ 2 = (K * M ^ 2) * ε ^ 2 := by ring
      _ ≤ C * ε ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ε)
      _ < tol := hbound
  · calc
      (M * ε) ^ 2 = (M ^ 2) * ε ^ 2 := by ring
      _ ≤ C * ε ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg ε)
      _ < tol := hbound

/-- Smooth compactly supported approximation in the fixed-support Gaussian Sobolev graph. -/
theorem fixed_support_smooth_graph_approx (R : ℝ) (hR : 0 ≤ R)
    {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hfs : Function.support f ⊆ Icc (-R) R)
    (hh_sq : Integrable (fun x => h x ^ 2) GaussianCore.γ)
    {tol : ℝ} (htol : 0 < tol) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      (∫ x, (F x - f x) ^ 2 ∂GaussianCore.γ) < tol ∧
      (∫ x, (deriv F x - h x) ^ 2 ∂GaussianCore.γ) < tol := by
  let A : ℝ := -(R + 2)
  let B : ℝ := R + 2
  let a : ℝ := -(R + 3)
  have ha : a < A := by dsimp [a, A]; linarith
  have hAB : A ≤ B := by dsimp [A, B]; linarith
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hfs
  have hhsR : Function.support h ⊆ Icc (-R) R :=
    actual_derivative_support_in_Icc hd hfs
  have hhLp : MemLp h 2 (volume : Measure ℝ) :=
    GaussianSobolevSmoothApprox.compact_derivative_memLp_volume hd hfc hh_sq
  have hhzero := GaussianSobolevSmoothApprox.compact_derivative_integral_zero
    hd hfc hh_sq
  obtain ⟨q, hq, hqs, hqint⟩ := exists_unit_integral_bump R hR
  have hqLp : MemLp q 2 (volume : Measure ℝ) :=
    hq.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hqs)
  let M : ℝ := 1 + Real.sqrt (B - A) * L2Norm q
  have hM : 0 ≤ M := by dsimp [M, L2Norm]; positivity
  obtain ⟨ε, hε, hεfun, hεgrad⟩ :=
    exists_tolerance_for_graph (B - A) M tol htol
  obtain ⟨v, hv, hvs, hverror⟩ :=
    exists_fixed_support_smooth_approx R hR hhsR hhLp hε
  have hvLp : MemLp v 2 (volume : Measure ℝ) :=
    hv.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hvs)
  have hhs : Function.support h ⊆ Icc A B := by
    intro x hx
    have hx' := hhsR hx
    dsimp [A, B]
    constructor <;> linarith [hx'.1, hx'.2]
  have hfsK : Function.support f ⊆ Icc A B := by
    intro x hx
    have hx' := hfs hx
    dsimp [A, B]
    constructor <;> linarith [hx'.1, hx'.2]
  have hnorm : L2Norm (v - h) ≤ ε := by
    rw [L2Norm_eq_eLpNorm (hvLp.sub hhLp), eLpNorm_sub_comm]
    exact (ENNReal.toReal_mono (by simp) hverror).trans_eq
      (ENNReal.toReal_ofReal hε.le)
  let w := corrected v q
  obtain ⟨hw, hws, hwzero⟩ := corrected_properties R hv hq hvs hqs hqint
  have hwLp : MemLp w 2 (volume : Measure ℝ) :=
    hw.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hws)
  have hcor : L2Norm (w - h) ≤ M * ε := by
    exact (correction_error A B hAB hhLp hvLp hqLp hhs hvs hhzero).trans
      (mul_le_mul_of_nonneg_left hnorm hM)
  have hsq : L2Norm (w - h) ^ 2 ≤ (M * ε) ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hM hε.le)).2 hcor
  let F := primitive a w
  have hF := corrected_primitive_properties R hv hq hvs hqs hqint
  have hgraph := fixed_support_graph_error A B a ha hAB hd hfsK hh_sq hw hws hwzero
  refine ⟨F, hF.1, hF.2.1, ?_, ?_⟩
  · calc
      (∫ x, (F x - f x) ^ 2 ∂GaussianCore.γ) ≤
          (B - A) * L2Norm (w - h) ^ 2 := hgraph.2.1
      _ ≤ (B - A) * (M * ε) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr hAB)
      _ < tol := hεfun
  · calc
      (∫ x, (deriv F x - h x) ^ 2 ∂GaussianCore.γ) ≤
          L2Norm (w - h) ^ 2 := hgraph.2.2.2
      _ ≤ (M * ε) ^ 2 := hsq
      _ < tol := hεgrad
end OperatorDerivativeRewrite.Foundation.GaussianSobolevFixedSupport
