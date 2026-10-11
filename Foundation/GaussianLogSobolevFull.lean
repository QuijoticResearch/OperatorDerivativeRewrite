import Foundation.GaussianSobolevGlobalApprox
import Foundation.GaussianLogSobolevCore
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Extension of Gaussian log-Sobolev from the bounded smooth core. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace OperatorDerivativeRewrite.Foundation.GaussianLogSobolevFull

private theorem lpNorm_sq_eq_integral_sq {u : ℝ → ℝ}
    (hu : MemLp u 2 GaussianCore.γ) :
    (lpNorm u 2 GaussianCore.γ) ^ 2 =
      ∫ x, u x ^ 2 ∂GaussianCore.γ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hu.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  have heq (x : ℝ) : |u x| ^ (2 : ℝ) = u x ^ 2 := by
    norm_num [Real.rpow_natCast, sq_abs]
  simp_rw [heq]
  simpa only [Real.sqrt_eq_rpow, one_div] using
    (Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (u x))))

private theorem lpNorm_sub_tendsto_zero {u : ℕ → ℝ → ℝ} {v : ℝ → ℝ}
    (hu : ∀ n, MemLp (u n) 2 GaussianCore.γ)
    (hv : MemLp v 2 GaussianCore.γ)
    (herr : Tendsto (fun n => ∫ x, (u n x - v x) ^ 2 ∂GaussianCore.γ)
      atTop (𝓝 0)) :
    Tendsto (fun n => lpNorm (u n - v) 2 GaussianCore.γ) atTop (𝓝 0) := by
  have heq (n : ℕ) : lpNorm (u n - v) 2 GaussianCore.γ =
      Real.sqrt (∫ x, (u n x - v x) ^ 2 ∂GaussianCore.γ) := by
    change lpNorm (u n - v) 2 GaussianCore.γ =
      Real.sqrt (∫ x, (u n - v) x ^ 2 ∂GaussianCore.γ)
    rw [← lpNorm_sq_eq_integral_sq ((hu n).sub hv)]
    exact (Real.sqrt_sq (lpNorm_nonneg)).symm
  simpa only [heq, Real.sqrt_zero, Function.comp_def] using
    (Real.continuous_sqrt.tendsto 0).comp herr

private theorem integral_sq_tendsto_of_graph_error {u : ℕ → ℝ → ℝ} {v : ℝ → ℝ}
    (hu : ∀ n, MemLp (u n) 2 GaussianCore.γ)
    (hv : MemLp v 2 GaussianCore.γ)
    (herr : Tendsto (fun n => ∫ x, (u n x - v x) ^ 2 ∂GaussianCore.γ)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, u n x ^ 2 ∂GaussianCore.γ)
      atTop (𝓝 (∫ x, v x ^ 2 ∂GaussianCore.γ)) := by
  have hnormerr := lpNorm_sub_tendsto_zero hu hv herr
  have hminus : Tendsto (fun n => -lpNorm (u n - v) 2 GaussianCore.γ)
      atTop (𝓝 0) := by simpa using hnormerr.neg
  have hdiff : Tendsto (fun n => lpNorm (u n) 2 GaussianCore.γ -
      lpNorm v 2 GaussianCore.γ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hminus hnormerr
    · intro n
      have hh := lpNorm_le_lpNorm_add_lpNorm_sub (hg := hu n) (f := v) (g := u n)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      dsimp at hh ⊢
      linarith
    · intro n
      have hh := lpNorm_le_lpNorm_add_lpNorm_sub' (hg := hv) (f := u n) (g := v)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      dsimp at hh ⊢
      linarith
  have hnorm : Tendsto (fun n => lpNorm (u n) 2 GaussianCore.γ)
      atTop (𝓝 (lpNorm v 2 GaussianCore.γ)) := by
    convert hdiff.add_const (lpNorm v 2 GaussianCore.γ) using 1 <;> simp
  convert hnorm.pow 2 using 1
  · funext n
    exact (lpNorm_sq_eq_integral_sq (hu n)).symm
  · congr 1
    exact (lpNorm_sq_eq_integral_sq hv).symm

private theorem klFun_integral_eq_entropySq {u : ℝ → ℝ}
    (hsq : Integrable (fun x => u x ^ 2) GaussianCore.γ)
    (hlog : Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2))
      GaussianCore.γ) :
    (∫ x, InformationTheory.klFun (u x ^ 2) ∂GaussianCore.γ) =
      entropySq GaussianCore.γ u +
        InformationTheory.klFun (∫ x, u x ^ 2 ∂GaussianCore.γ) := by
  have hkl : Integrable (fun x => InformationTheory.klFun (u x ^ 2))
      GaussianCore.γ := by
    convert (hlog.add (integrable_const (1 : ℝ))).sub hsq using 1
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, InformationTheory.klFun]
  simp only [InformationTheory.klFun, entropySq]
  calc
    (∫ x, u x ^ 2 * Real.log (u x ^ 2) + 1 - u x ^ 2 ∂GaussianCore.γ) =
        (∫ x, (u x ^ 2 * Real.log (u x ^ 2) + 1) ∂GaussianCore.γ) -
          (∫ x, u x ^ 2 ∂GaussianCore.γ) :=
      integral_sub (hlog.add (integrable_const (1 : ℝ))) hsq
    _ = _ := by
      rw [integral_add hlog (integrable_const (1 : ℝ))]
      simp only [integral_const]
      have hγ : GaussianCore.γ.real Set.univ = 1 := by simp
      rw [hγ]
      ring

private theorem smooth_compact_core_bound {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u) :
    Integrable (fun x => InformationTheory.klFun (u x ^ 2)) GaussianCore.γ ∧
      (∫ x, InformationTheory.klFun (u x ^ 2) ∂GaussianCore.γ) ≤
        2 * ∫ x, (deriv u x) ^ 2 ∂GaussianCore.γ +
        InformationTheory.klFun (∫ x, u x ^ 2 ∂GaussianCore.γ) := by
  obtain ⟨A, hA⟩ := hu.continuous.bounded_above_of_compact_support hs
  obtain ⟨B, hB⟩ := (hu.continuous_deriv (by norm_num)).bounded_above_of_compact_support
    hs.deriv
  let M := max A B
  have hfb (x : ℝ) : ‖u x‖ ≤ M := (hA x).trans (le_max_left _ _)
  have hdb (x : ℝ) : ‖deriv u x‖ ≤ M := (hB x).trans (le_max_right _ _)
  have hsq : Integrable (fun x => u x ^ 2) GaussianCore.γ :=
    ((hu.continuous.memLp_of_hasCompactSupport hs : MemLp u 2 GaussianCore.γ)).integrable_sq
  have hlog := GaussianLogSobolevCore.core_sq_mul_log_integrable
    (hu.of_le (by norm_num)) hfb
  have hkl : Integrable (fun x => InformationTheory.klFun (u x ^ 2))
      GaussianCore.γ := by
    convert (hlog.add (integrable_const (1 : ℝ))).sub hsq using 1
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, InformationTheory.klFun]
  refine ⟨hkl, ?_⟩
  rw [klFun_integral_eq_entropySq hsq hlog]
  have hcore := GaussianLogSobolevCore.gaussian_logSobolev_core
    (hu.of_le (by norm_num)) hfb hdb
  linarith

private theorem klFun_fatou_bound {f : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (hf : MemLp f 2 GaussianCore.γ)
    (hF : ∀ n, ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n))
    (herr : Tendsto (fun n => ∫ x, (F n x - f x) ^ 2 ∂GaussianCore.γ)
      atTop (𝓝 0))
    {E : ℝ}
    (henergy : Tendsto (fun n => ∫ x, (deriv (F n) x) ^ 2 ∂GaussianCore.γ)
      atTop (𝓝 E)) :
    Integrable (fun x => InformationTheory.klFun (f x ^ 2)) GaussianCore.γ ∧
      (∫ x, InformationTheory.klFun (f x ^ 2) ∂GaussianCore.γ) ≤
        2 * E + InformationTheory.klFun (∫ x, f x ^ 2 ∂GaussianCore.γ) := by
  have hFLp (n : ℕ) : MemLp (F n) 2 GaussianCore.γ :=
    (hF n).1.continuous.memLp_of_hasCompactSupport (hF n).2
  have hmass := integral_sq_tendsto_of_graph_error hFLp hf herr
  have hnorm := lpNorm_sub_tendsto_zero hFLp hf herr
  have heLp : Tendsto (fun n => eLpNorm (F n - f) 2 GaussianCore.γ)
      atTop (𝓝 0) := by
    have hh := ENNReal.tendsto_ofReal hnorm
    simpa only [ENNReal.ofReal_zero] using
      (show Tendsto (fun n => eLpNorm (F n - f) 2 GaussianCore.γ)
        atTop (𝓝 (ENNReal.ofReal 0)) from by
          convert hh using 1
          funext n
          exact (ofReal_lpNorm ((hFLp n).sub hf)).symm)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      heLp).exists_seq_tendsto_ae
  have hkl (n : ℕ) := smooth_compact_core_bound (hF n).1 (hF n).2
  let K : ℕ → ℝ := fun n => ∫ x, InformationTheory.klFun (F n x ^ 2) ∂GaussianCore.γ
  let B : ℕ → ℝ := fun n =>
    2 * (∫ x, (deriv (F n) x) ^ 2 ∂GaussianCore.γ) +
      InformationTheory.klFun (∫ x, F n x ^ 2 ∂GaussianCore.γ)
  let L : ℝ := 2 * E + InformationTheory.klFun (∫ x, f x ^ 2 ∂GaussianCore.γ)
  have hKL (n : ℕ) : K n ≤ B n := (hkl n).2
  have hB : Tendsto B atTop (𝓝 L) := by
    exact (henergy.const_mul 2).add
      (InformationTheory.continuous_klFun.tendsto _ |>.comp hmass)
  have hnsT : Tendsto ns atTop atTop := hns.tendsto_atTop
  have hBsub : Tendsto (fun n => B (ns n)) atTop (𝓝 L) := hB.comp hnsT
  have hKpoint : ∀ᵐ x ∂GaussianCore.γ,
      Tendsto (fun n => InformationTheory.klFun (F (ns n) x ^ 2))
        atTop (𝓝 (InformationTheory.klFun (f x ^ 2))) := by
    filter_upwards [hae] with x hx
    exact InformationTheory.continuous_klFun.continuousAt.tendsto.comp
      ((continuous_pow 2).tendsto (f x) |>.comp hx)
  have hfatou := lintegral_enorm_le_liminf_of_tendsto hKpoint
    (fun n => (InformationTheory.continuous_klFun.measurable.comp
      ((hF (ns n)).1.continuous.measurable.pow_const 2)).aemeasurable.enorm)
  have hlin (n : ℕ) :
      (∫⁻ x, ‖InformationTheory.klFun (F (ns n) x ^ 2)‖ₑ ∂GaussianCore.γ) =
        ENNReal.ofReal (K (ns n)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hkl (ns n)).1
      (Filter.Eventually.of_forall fun x => InformationTheory.klFun_nonneg (sq_nonneg _))]
    apply lintegral_congr
    intro x
    rw [Real.enorm_eq_ofReal (InformationTheory.klFun_nonneg (sq_nonneg _))]
  have hliminf : liminf (fun n => ENNReal.ofReal (K (ns n))) atTop ≤
      ENNReal.ofReal L := by
    calc
      liminf (fun n => ENNReal.ofReal (K (ns n))) atTop ≤
          liminf (fun n => ENNReal.ofReal (B (ns n))) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n =>
          ENNReal.ofReal_le_ofReal (hKL (ns n)))
      _ = ENNReal.ofReal L :=
        (ENNReal.tendsto_ofReal hBsub).liminf_eq
  have htop : (∫⁻ x, ‖InformationTheory.klFun (f x ^ 2)‖ₑ ∂GaussianCore.γ) ≠ ⊤ := by
    have hh : (∫⁻ x, ‖InformationTheory.klFun (f x ^ 2)‖ₑ
        ∂GaussianCore.γ) ≤ ENNReal.ofReal L := by
      exact hfatou.trans (by simpa only [hlin] using hliminf)
    exact (lt_of_le_of_lt hh ENNReal.ofReal_lt_top).ne
  have hliminf_ne : liminf (fun n =>
      ∫⁻ x, ‖InformationTheory.klFun (F (ns n) x ^ 2)‖ₑ
        ∂GaussianCore.γ) atTop ≠ ⊤ := by
    rw [show (fun n => ∫⁻ x, ‖InformationTheory.klFun (F (ns n) x ^ 2)‖ₑ
        ∂GaussianCore.γ) = (fun n => ENNReal.ofReal (K (ns n))) by
          funext n; exact hlin n]
    exact (lt_of_le_of_lt hliminf ENNReal.ofReal_lt_top).ne
  have hInt : Integrable (fun x => InformationTheory.klFun (f x ^ 2))
      GaussianCore.γ := integrable_of_tendsto hKpoint
        (fun n => (InformationTheory.continuous_klFun.measurable.comp
          ((hF (ns n)).1.continuous.measurable.pow_const 2)).aestronglyMeasurable)
        hliminf_ne
  refine ⟨hInt, ?_⟩
  have hreal : ENNReal.ofReal
      (∫ x, InformationTheory.klFun (f x ^ 2) ∂GaussianCore.γ) ≤
      ENNReal.ofReal L := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun x => InformationTheory.klFun_nonneg (sq_nonneg _))]
    have hh : (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (f x ^ 2))
      ∂GaussianCore.γ) =
        (∫⁻ x, ‖InformationTheory.klFun (f x ^ 2)‖ₑ ∂GaussianCore.γ) := by
      apply lintegral_congr
      intro x
      rw [Real.enorm_eq_ofReal (InformationTheory.klFun_nonneg (sq_nonneg _))]
    rw [hh]
    exact hfatou.trans (by simpa only [hlin] using hliminf)
  have hL : 0 ≤ L := by
    have hBn (n : ℕ) : 0 ≤ B n := le_trans
      (integral_nonneg fun x => InformationTheory.klFun_nonneg (sq_nonneg _)) (hKL n)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hB
      (Filter.Eventually.of_forall hBn)
  exact (ENNReal.ofReal_le_ofReal_iff hL).1 hreal

/-- Full variance-one Gaussian log-Sobolev inequality for everywhere
differentiable functions with Gaussian-L² value and actual derivative.
Finiteness of the entropy integrand is a conclusion. -/
theorem gaussian_logSobolev_of_hasDerivAt {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hf_sq : Integrable (fun x => f x ^ 2) GaussianCore.γ)
    (hh_sq : Integrable (fun x => h x ^ 2) GaussianCore.γ) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) GaussianCore.γ ∧
      entropySq GaussianCore.γ f ≤
        2 * ∫ x, h x ^ 2 ∂GaussianCore.γ := by
  obtain ⟨F, hFsmooth, hFcompact, hFerror, hDerror⟩ :=
    GaussianSobolevGlobalApprox.exists_smooth_compact_graph_sequence hd hf_sq hh_sq
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hd x).continuousAt)
  have hhMeas : Measurable h := by
    rw [GaussianLocalSobolev.derivative_eq_deriv hd]
    exact measurable_deriv f
  have hfLp : MemLp f 2 GaussianCore.γ :=
    (memLp_two_iff_integrable_sq hfcont.measurable.aestronglyMeasurable).2 hf_sq
  have hhLp : MemLp h 2 GaussianCore.γ :=
    (memLp_two_iff_integrable_sq hhMeas.aestronglyMeasurable).2 hh_sq
  have hDLp (n : ℕ) : MemLp (deriv (F n)) 2 GaussianCore.γ :=
    ((hFsmooth n).continuous_deriv (by norm_num)).memLp_of_hasCompactSupport
      (hFcompact n).deriv
  have henergy := integral_sq_tendsto_of_graph_error hDLp hhLp hDerror
  obtain ⟨hklInt, hklBound⟩ := klFun_fatou_bound hfLp
    (fun n => ⟨hFsmooth n, hFcompact n⟩) hFerror henergy
  have hlog : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2))
      GaussianCore.γ := by
    convert (hklInt.sub (integrable_const (1 : ℝ))).add hf_sq using 1
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, InformationTheory.klFun]
    ring
  refine ⟨hlog, ?_⟩
  rw [klFun_integral_eq_entropySq hf_sq hlog] at hklBound
  linarith

/-- Compatibility with the original axiom's (unnecessary) strict-positivity
assumption. The measure and constant agree exactly with that statement. -/
theorem gaussian_logSobolev_of_hasDerivAt_pos (f h : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (h x) x)
    (_hpos : ∀ x, 0 < f x)
    (hf_sq : Integrable (fun x => f x ^ 2) GaussianCore.γ)
    (hh_sq : Integrable (fun x => h x ^ 2) GaussianCore.γ) :
    entropySq GaussianCore.γ f ≤
      2 * ∫ x, h x ^ 2 ∂GaussianCore.γ :=
  (gaussian_logSobolev_of_hasDerivAt hd hf_sq hh_sq).2

end OperatorDerivativeRewrite.Foundation.GaussianLogSobolevFull
