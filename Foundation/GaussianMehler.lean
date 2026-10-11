/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Copyright (c) 2026 OperatorDerivativeRewrite contributors.
Portions adapted from MarkovSemigroups/Instances/WorkInProgress/Euclidean.lean,
namespace Gaussian1D, by Michael R. Douglas and contributors, commit
acf649108ea2222f4a8544a2782f448cb502492a (Apache License 2.0).
See LICENSES/Apache-2.0.txt and MATHEMATICAL_AUDIT.md for attribution and scope.
-/
import Foundation.GaussianCore
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! Concrete Mehler kernels on bounded continuous real functions. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianMehler

abbrev γ : Measure ℝ := GaussianCore.γ

/-- The integral kernel; the theorems below justify its use on bounded continuous functions. -/
def mehler (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ

theorem one_sub_exp_nonneg (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-2 * t) := by
  have h : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- Bounded measurable functions composed with any measurable map are integrable
against a finite measure. This supplies the domination for every kernel integral. -/
theorem integrable_comp_of_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    {g : α → ℝ} (hg : Measurable g) : Integrable (fun z => f (g z)) μ := by
  refine Integrable.mono' (integrable_const M) (hf.comp hg).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun z => hM (g z))

theorem kernel_integrable {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (t x : ℝ) :
    Integrable (fun y => f (Real.exp (-t) * x +
      Real.sqrt (1 - Real.exp (-2 * t)) * y)) γ := by
  apply integrable_comp_of_bounded hf.measurable hM
  fun_prop

theorem mehler_zero (f : ℝ → ℝ) : mehler 0 f = f := by
  funext x
  simp [mehler]

theorem mehler_const (t c : ℝ) : mehler t (fun _ => c) = fun _ => c := by
  funext x
  simp [mehler]

theorem mehler_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {M N : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (hN : ∀ z, ‖g z‖ ≤ N)
    (hfg : ∀ z, f z ≤ g z) (t x : ℝ) : mehler t f x ≤ mehler t g x := by
  apply integral_mono (kernel_integrable hf hM t x) (kernel_integrable hg hN t x)
  intro y
  exact hfg _

theorem mehler_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (hpos : ∀ z, 0 ≤ f z) (t x : ℝ) :
    0 ≤ mehler t f x := by
  have h := mehler_mono continuous_const hf (M := 0) (by simp) hM hpos t x
  simpa [mehler_const] using h

theorem mehler_norm_le {f : ℝ → ℝ} {M : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (t x : ℝ) : ‖mehler t f x‖ ≤ M := by
  simpa [mehler] using
    (norm_integral_le_of_norm_le_const (μ := γ)
      (Filter.Eventually.of_forall (fun y => hM (Real.exp (-t) * x +
        Real.sqrt (1 - Real.exp (-2 * t)) * y))))

/-- Mehler kernels preserve the continuous bounded class, by dominated convergence. -/
theorem mehler_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (t : ℝ) : Continuous (mehler t f) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (mehler t f) (𝓝 x) (𝓝 (mehler t f x))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => M)
  · exact Filter.Eventually.of_forall (fun z => (kernel_integrable hf hM t z).1)
  · exact Filter.Eventually.of_forall (fun z => Filter.Eventually.of_forall (fun y => hM _))
  · exact integrable_const M
  · apply Filter.Eventually.of_forall
    intro y
    apply (hf.continuousAt.tendsto).comp
    exact ((continuous_const.mul continuous_id).add continuous_const).continuousAt.tendsto

/-- Pointwise convergence to the invariant mean, using constant domination. -/
theorem mehler_tendsto_mean {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (x : ℝ) :
    Tendsto (fun t => mehler t f x) atTop (𝓝 (∫ y, f y ∂γ)) := by
  have ha : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have ha2 : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (𝓝 0) := by
    have h := ha.pow 2
    convert h using 1
    · funext t
      rw [show -2 * t = -t + -t by ring, Real.exp_add]
      ring
    · simp
  have hb : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t)))
      atTop (𝓝 1) := by
    simpa using (ha2.const_sub 1).sqrt
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => M)
  · exact Filter.Eventually.of_forall (fun t => (kernel_integrable hf hM t x).1)
  · exact Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun y => hM _))
  · exact integrable_const M
  · apply Filter.Eventually.of_forall
    intro y
    have harg : Tendsto (fun t => Real.exp (-t) * x +
        Real.sqrt (1 - Real.exp (-2 * t)) * y) atTop (𝓝 y) := by
      simpa using (ha.mul_const x).add (hb.mul_const y)
    exact (hf.tendsto y).comp harg

/-- Independent standard Gaussian linear combinations have the stated variance. -/
theorem gaussian_combination_map (a b : ℝ) :
    (γ.prod γ).map (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      gaussianReal 0 (⟨a ^ 2, sq_nonneg a⟩ + ⟨b ^ 2, sq_nonneg b⟩) := by
  have hX : HasLaw (fun p : ℝ × ℝ => p.1) γ (γ.prod γ) :=
    ⟨measurable_fst.aemeasurable,
      by rw [Measure.map_fst_prod]; simp [measure_univ]⟩
  have hY : HasLaw (fun p : ℝ × ℝ => p.2) γ (γ.prod γ) :=
    ⟨measurable_snd.aemeasurable,
      by rw [Measure.map_snd_prod]; simp [measure_univ]⟩
  have ha := gaussianReal_const_mul hX a
  have hb := gaussianReal_const_mul hY b
  have hindep : (fun p : ℝ × ℝ => a * p.1) ⟂ᵢ[γ.prod γ]
      (fun p : ℝ × ℝ => b * p.2) :=
    (indepFun_prod measurable_id measurable_id).comp
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  rw [show (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
    (fun p : ℝ × ℝ => a * p.1) + (fun p => b * p.2) from rfl]
  refine (gaussianReal_add_gaussianReal_of_indepFun hindep ha hb).trans ?_
  congr 1
  · simp
  · apply NNReal.eq
    simp
    rfl

/-- The two-coordinate Mehler mixing map preserves the standard Gaussian law. -/
theorem kernel_map (t : ℝ) (ht : 0 ≤ t) :
    (γ.prod γ).map (fun p : ℝ × ℝ => Real.exp (-t) * p.1 +
      Real.sqrt (1 - Real.exp (-2 * t)) * p.2) = γ := by
  rw [gaussian_combination_map]
  have hv : Real.exp (-t) ^ 2 + Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 = 1 := by
    rw [Real.sq_sqrt (one_sub_exp_nonneg t ht)]
    have he : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
      rw [show -2 * t = -t + -t by ring, Real.exp_add]
      ring
    rw [he]
    ring
  congr 1
  exact NNReal.eq hv

/-- Gaussian invariance, obtained from the Gaussian mixing law and Fubini. -/
theorem integral_mehler {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    ∫ x, mehler t f x ∂γ = ∫ x, f x ∂γ := by
  have hprod : Integrable (fun p : ℝ × ℝ => f (Real.exp (-t) * p.1 +
      Real.sqrt (1 - Real.exp (-2 * t)) * p.2)) (γ.prod γ) := by
    apply integrable_comp_of_bounded hf.measurable hM
    fun_prop
  have hmap := integral_map
    (μ := γ.prod γ)
    (φ := fun p : ℝ × ℝ => Real.exp (-t) * p.1 +
      Real.sqrt (1 - Real.exp (-2 * t)) * p.2)
    (by fun_prop : AEMeasurable _ (γ.prod γ))
    (hf.measurable.aestronglyMeasurable : AEStronglyMeasurable f _)
  rw [kernel_map t ht] at hmap
  rw [hmap, integral_prod _ hprod]
  rfl

/-- In particular the invariant-measure identity involves an integrable function. -/
theorem mehler_integrable {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (t : ℝ) : Integrable (mehler t f) γ :=
  integrable_comp_of_bounded (mehler_continuous hf hM t).measurable
    (fun z => mehler_norm_le hM t z) measurable_id
/-- Composition follows from equality of the two Gaussian mixing laws and Fubini. -/
theorem mehler_compose (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) :
    mehler (s + t) f = mehler s (mehler t f) := by
  ext x
  have hf_meas : Measurable f := hf.measurable
  set ast := Real.exp (-(s + t))
  set bst := Real.sqrt (1 - Real.exp (-2 * (s + t)))
  set as := Real.exp (-s)
  set bs := Real.sqrt (1 - Real.exp (-2 * s))
  set at_ := Real.exp (-t)
  set bt := Real.sqrt (1 - Real.exp (-2 * t))
  have hbst_nn : 0 ≤ 1 - Real.exp (-2 * (s + t)) :=
    one_sub_exp_nonneg (s + t) (by linarith)
  have hbs_nn : 0 ≤ 1 - Real.exp (-2 * s) := one_sub_exp_nonneg s hs
  have hbt_nn : 0 ≤ 1 - Real.exp (-2 * t) := one_sub_exp_nonneg t ht
  have h_ast : ast = as * at_ := by
    change Real.exp (-(s + t)) = Real.exp (-s) * Real.exp (-t)
    rw [show -(s + t) = -s + -t from by ring, Real.exp_add]
  set Ψ : ℝ × ℝ → ℝ := fun p => at_ * bs * p.1 + bt * p.2 with hΨ_def
  have hΨ_meas : Measurable Ψ :=
    (measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)
  have h_var_eq : (at_ * bs) ^ 2 + bt ^ 2 = 1 - Real.exp (-2 * (s + t)) := by
    change (Real.exp (-t) * Real.sqrt (1 - Real.exp (-2 * s))) ^ 2 +
         (Real.sqrt (1 - Real.exp (-2 * t))) ^ 2 = 1 - Real.exp (-2 * (s + t))
    rw [mul_pow, Real.sq_sqrt hbs_nn, Real.sq_sqrt hbt_nn,
      show (Real.exp (-t)) ^ 2 = Real.exp (-2 * t) by
        rw [show (-2 * t : ℝ) = -t + -t from by ring, Real.exp_add]; ring]
    have h2 : Real.exp (-2 * t) * Real.exp (-2 * s) = Real.exp (-2 * (s + t)) := by
      rw [← Real.exp_add]; congr 1; ring
    linarith [h2]
  have hX : HasLaw (fun p : ℝ × ℝ => p.1) γ (γ.prod γ) :=
    ⟨measurable_fst.aemeasurable,
     by rw [Measure.map_fst_prod]; simp [measure_univ]⟩
  have hY : HasLaw (fun p : ℝ × ℝ => p.2) γ (γ.prod γ) :=
    ⟨measurable_snd.aemeasurable,
     by rw [Measure.map_snd_prod]; simp [measure_univ]⟩
  have h1 := gaussianReal_const_mul hX (at_ * bs)
  have h2 := gaussianReal_const_mul hY bt
  have hindep : (fun p : ℝ × ℝ => (at_ * bs) * p.1) ⟂ᵢ[γ.prod γ]
      (fun p : ℝ × ℝ => bt * p.2) :=
    (indepFun_prod measurable_id measurable_id).comp
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  have hΨ_law := gaussianReal_add_gaussianReal_of_indepFun hindep h1 h2
  have h_eq : gaussianReal ((at_ * bs) * 0 + bt * 0)
      (⟨(at_ * bs) ^ 2, sq_nonneg _⟩ * 1 + ⟨bt ^ 2, sq_nonneg _⟩ * 1) =
      gaussianReal 0 ⟨1 - Real.exp (-2 * (s + t)), hbst_nn⟩ := by
    congr 1
    · simp
    · simp only [mul_one]
      apply NNReal.eq
      simp only [NNReal.coe_add]
      exact h_var_eq
  replace hΨ_law := hΨ_law.trans h_eq
  have hZ : HasLaw (fun z : ℝ => z) γ γ := ⟨measurable_id.aemeasurable, by simp⟩
  have h_bst_law := gaussianReal_const_mul hZ bst
  have h_bst_sq : bst ^ 2 = 1 - Real.exp (-2 * (s + t)) := Real.sq_sqrt hbst_nn
  have h_bst_law' : Measure.map (fun z => bst * z) γ =
      gaussianReal 0 ⟨1 - Real.exp (-2 * (s + t)), hbst_nn⟩ := by
    have := h_bst_law.map_eq
    rw [this]
    simp only [mul_zero, mul_one]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mk]
    exact h_bst_sq
  have hf_int_Ψ : Integrable (fun p : ℝ × ℝ => f (ast * x + Ψ p)) (γ.prod γ) := by
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · have : Measurable (fun p : ℝ × ℝ => f (ast * x + Ψ p)) :=
        hf_meas.comp (measurable_const.add hΨ_meas)
      exact this.aestronglyMeasurable
    · filter_upwards with p; exact hM _
  have hRHS : mehler s (mehler t f) x =
      ∫ p, f (ast * x + Ψ p) ∂(γ.prod γ) := by
    change ∫ y', (∫ y, f (at_ * (as * x + bs * y') + bt * y) ∂γ) ∂γ =
        ∫ p, f (ast * x + Ψ p) ∂(γ.prod γ)
    have h_eq_pt : ∀ y' y, at_ * (as * x + bs * y') + bt * y = ast * x + Ψ (y', y) := by
      intro y' y
      change at_ * (as * x + bs * y') + bt * y = ast * x + (at_ * bs * y' + bt * y)
      rw [h_ast]; ring
    simp_rw [h_eq_pt]
    rw [integral_prod _ hf_int_Ψ]
  have hΨ_law' : Measure.map Ψ (γ.prod γ) =
      gaussianReal 0 ⟨1 - Real.exp (-2 * (s + t)), hbst_nn⟩ := by
    have hΨ_eq : Ψ = (fun p : ℝ × ℝ => at_ * bs * p.1) + fun p => bt * p.2 := by
      funext p; rfl
    rw [hΨ_eq]; exact hΨ_law
  have hcompose : ∫ p, f (ast * x + Ψ p) ∂(γ.prod γ) =
      ∫ z, f (ast * x + bst * z) ∂γ := by
    have h_lhs_via_law :
        ∫ p, f (ast * x + Ψ p) ∂(γ.prod γ) =
        ∫ w, f (ast * x + w) ∂((γ.prod γ).map Ψ) := by
      have hf_w_int : AEStronglyMeasurable (fun w => f (ast * x + w)) ((γ.prod γ).map Ψ) := by
        rw [hΨ_law']
        exact (hf_meas.comp (measurable_const.add measurable_id')).aestronglyMeasurable
      rw [integral_map hΨ_meas.aemeasurable hf_w_int]
    have h_rhs_via_law :
        ∫ z, f (ast * x + bst * z) ∂γ =
        ∫ w, f (ast * x + w) ∂(Measure.map (fun z => bst * z) γ) := by
      have h_bst_meas : Measurable (fun z : ℝ => bst * z) := measurable_const.mul measurable_id'
      have hf_w_int : AEStronglyMeasurable (fun w => f (ast * x + w))
          (Measure.map (fun z => bst * z) γ) := by
        rw [h_bst_law']
        exact (hf_meas.comp (measurable_const.add measurable_id')).aestronglyMeasurable
      rw [integral_map h_bst_meas.aemeasurable hf_w_int]
    rw [h_lhs_via_law, h_rhs_via_law, hΨ_law', h_bst_law']
  change mehler (s + t) f x = mehler s (mehler t f) x
  rw [hRHS, hcompose]
  rfl


/-- Strictly positive bounded continuous functions have strictly positive kernels. -/
theorem mehler_pos {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (hpos : ∀ z, 0 < f z) (t x : ℝ) :
    0 < mehler t f x := by
  rw [mehler, integral_pos_iff_support_of_nonneg
    (fun y => (hpos _).le) (kernel_integrable hf hM t x)]
  convert (show 0 < γ Set.univ by simp) using 1
  congr 1
  ext y
  simp only [Function.mem_support, Set.mem_univ, iff_true]
  exact (hpos _).ne'
end OperatorDerivativeRewrite.Foundation.GaussianMehler
