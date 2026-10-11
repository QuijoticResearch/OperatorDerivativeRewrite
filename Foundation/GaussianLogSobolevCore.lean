import Foundation.GaussianEntropyDissipationProof

/-!
# Gaussian log-Sobolev inequality on the bounded C¹ core

Variance-one normalization gives `Entγ(f²) ≤ 2 ∫ (f′)² dγ`.
The proof combines the verified positive-time entropy dissipation and Fisher
contraction, then removes strict positivity using `f² + ε` and genuine
bounded dominated convergence. No new semigroup property is assumed.
-/


noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianLogSobolevCore

abbrev γ : Measure ℝ := GaussianEntropyDissipation.γ

/-- Entropy is at most half the Fisher information for a positive bounded C¹ density. -/
theorem entropyDensity_le_half_fisher (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x)
    (hhi : ∀ x, g x ≤ M) (hderiv : ∀ x, ‖deriv g x‖ ≤ M) :
    GaussianEntropyDissipation.entropyDensity g ≤
      (1 / 2 : ℝ) * GaussianFisher.fisherInformation g := by
  have hnorm : ∀ x, ‖g x‖ ≤ M := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (hε.trans_le (hlo x))]
    exact hhi x
  let H : ℝ → ℝ := fun t => GaussianEntropyDissipation.entropyTrajectory g t -
    (1 / 2 : ℝ) * Real.exp (-2 * t) * GaussianFisher.fisherInformation g
  have hHcont : Continuous H := by
    dsimp [H]
    exact (GaussianEntropyDissipation.entropyTrajectory_continuous hg.continuous hnorm).sub
      (by fun_prop)
  have hHHas (t : ℝ) (ht : 0 < t) : HasDerivAt H
      (-GaussianFisher.fisherInformation (GaussianMehler.mehler t g) +
        Real.exp (-2 * t) * GaussianFisher.fisherInformation g) t := by
    have hE := GaussianEntropyDissipationProof.hasDerivAt_entropy_dissipation
      t ht hg hε hlo hhi hderiv
    have hlinear : HasDerivAt (fun s : ℝ => -2 * s) (-2) t := by
      simpa only [mul_one, id_eq] using (hasDerivAt_id t).const_mul (-2)
    have hExp : HasDerivAt (fun s : ℝ => Real.exp (-2 * s))
        (-2 * Real.exp (-2 * t)) t := by
      have hh := (Real.hasDerivAt_exp (-2 * t)).comp t hlinear
      convert hh using 1
      · funext s
        rfl
      · ring
    dsimp [H]
    convert hE.sub ((hExp.const_mul (1 / 2 : ℝ)).mul_const
      (GaussianFisher.fisherInformation g)) using 1 ; ring
  have hHderiv (t : ℝ) (ht : 0 < t) : 0 ≤ deriv H t := by
    rw [(hHHas t ht).deriv]
    have hdec := GaussianFisher.fisherInformation_decay g hg hε hlo hhi
      (fun x => by simpa [Real.norm_eq_abs] using hderiv x) t ht.le
    nlinarith
  have hmono : MonotoneOn H (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hHcont.continuousOn
    · intro t ht
      have htpos : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
      exact (hHHas t htpos).differentiableAt.differentiableWithinAt
    · intro t ht
      exact hHderiv t (by simpa only [interior_Ici, Set.mem_Ioi] using ht)
  have hlim : Tendsto H atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
    have hterm : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.exp (-2 * t) *
        GaussianFisher.fisherInformation g) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul he).mul tendsto_const_nhds
    simpa only [H, sub_zero] using
      (GaussianEntropyDissipation.entropyTrajectory_tendsto_atTop
        hg.continuous hnorm).sub hterm
  have hHle : H 0 ≤ 0 := by
    have hpoint : ∀ t : ℝ, 0 ≤ t → H 0 ≤ H t := by
      intro t ht
      exact hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    apply ge_of_tendsto hlim
    exact Filter.eventually_atTop.2 ⟨0, fun t ht => hpoint t ht⟩
  simpa [H, GaussianEntropyDissipation.entropyTrajectory_zero] using hHle

theorem regularized_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (ε x : ℝ) : deriv (fun y => f y ^ 2 + ε) x = 2 * f x * deriv f x := by
  rw [deriv_add_const]
  convert deriv_pow (hf.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0) x) 2 using 1 ; ring

/-- Regularization by ε gives a Fisher-energy estimate uniform as ε tends to zero. -/
theorem regularized_fisher_le_energy {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hfb : ∀ x, ‖f x‖ ≤ M) (hfdb : ∀ x, ‖deriv f x‖ ≤ M) :
    GaussianFisher.fisherInformation (fun x => f x ^ 2 + ε) ≤
      4 * ∫ x, (deriv f x) ^ 2 ∂γ := by
  let g : ℝ → ℝ := fun x => f x ^ 2 + ε
  have hpos (x : ℝ) : 0 < g x := by dsimp [g]; positivity
  have hgC : ContDiff ℝ 1 g := (hf.pow 2).add contDiff_const
  have hdg (x : ℝ) : deriv g x = 2 * f x * deriv f x :=
    regularized_deriv hf ε x
  have hbound (x : ℝ) : |deriv g x| ≤ 2 * M ^ 2 := by
    rw [hdg x, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hf1 : |f x| ≤ M := by simpa [Real.norm_eq_abs] using hfb x
    have hf2 : |deriv f x| ≤ M := by simpa [Real.norm_eq_abs] using hfdb x
    have hprod := mul_le_mul hf1 hf2 (abs_nonneg (deriv f x)) hM
    nlinarith
  have hint : Integrable (fun x => (deriv g x) ^ 2 / g x) γ := by
    have hm : Measurable (deriv g) := by
      rw [funext hdg]
      exact (measurable_const.mul hf.continuous.measurable).mul
        (hf.continuous_deriv le_rfl).measurable
    apply GaussianFisher.fisherInformation_integrable hε hgC.continuous.measurable hm
    · intro x
      dsimp [g]
      nlinarith [sq_nonneg (f x)]
    · exact hbound
  have henergy : Integrable (fun x => (deriv f x) ^ 2) γ := by
    apply Integrable.mono' (integrable_const (M ^ 2))
      ((hf.continuous_deriv le_rfl).pow 2).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh : |deriv f x| ≤ M := by simpa [Real.norm_eq_abs] using hfdb x
    calc
      (deriv f x) ^ 2 = |deriv f x| ^ 2 := (sq_abs _).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
  unfold GaussianFisher.fisherInformation
  rw [← integral_const_mul]
  apply integral_mono hint (henergy.const_mul 4)
  intro x
  change deriv g x ^ 2 / g x ≤ 4 * deriv f x ^ 2
  rw [hdg x]
  have hdiv : f x ^ 2 / g x ≤ 1 :=
    (div_le_one (hpos x)).2 (by dsimp [g]; linarith)
  calc
    (2 * f x * deriv f x) ^ 2 / g x =
        4 * (deriv f x) ^ 2 * (f x ^ 2 / g x) := by ring
    _ ≤ 4 * (deriv f x) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = 4 * (deriv f x) ^ 2 := by ring

/-- The finite entropies of `f² + 1/(n+1)` converge to square entropy, including at zeros of f. -/
theorem regularized_entropy_tendsto {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M) :
    Tendsto (fun n : ℕ => GaussianEntropyDissipation.entropyDensity
      (fun x => f x ^ 2 + (1 : ℝ) / ((n : ℝ) + 1))) atTop
      (𝓝 (entropySq γ f)) := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hfb 0)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let g : ℕ → ℝ → ℝ := fun n x => f x ^ 2 + ε n
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hεbound (n : ℕ) : 0 ≤ ε n ∧ ε n ≤ 1 := by
    dsimp [ε]
    constructor
    · positivity
    · apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.succ_pos n
  have hfsq (x : ℝ) : f x ^ 2 ≤ M ^ 2 := by
    calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using hfb x) 2
  have hgb (n : ℕ) (x : ℝ) : ‖g n x‖ ≤ M ^ 2 + 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g]; positivity)]
    dsimp [g]
    linarith [hfsq x, (hεbound n).2]
  have hgi (n : ℕ) : Integrable (g n) γ ∧
      Integrable (fun x => g n x * Real.log (g n x)) γ :=
    GaussianEntropyDissipation.entropyDensity_integrable
      (by dsimp [g]; fun_prop) (hgb n)
  obtain ⟨B, hB⟩ := GaussianEntropyDissipation.exists_mul_log_bound (M ^ 2 + 1)
  have hpoint (x : ℝ) : Tendsto (fun n => g n x) atTop (𝓝 (f x ^ 2)) := by
    simpa only [g, add_zero] using (tendsto_const_nhds.add hεlim)
  have hmass : Tendsto (fun n => ∫ x, g n x ∂γ) atTop
      (𝓝 (∫ x, f x ^ 2 ∂γ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (μ := γ) (fun _ => M ^ 2 + 1)
    · exact Filter.Eventually.of_forall fun n => (hgi n).1.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall (hgb n)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall hpoint
  have hlog : Tendsto (fun n => ∫ x, g n x * Real.log (g n x) ∂γ) atTop
      (𝓝 (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂γ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (μ := γ) (fun _ => B)
    · exact Filter.Eventually.of_forall fun n => (hgi n).2.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall
        (fun x => hB _ (hgb n x))
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun x =>
        Real.continuous_mul_log.continuousAt.tendsto.comp (hpoint x)
  simpa [entropySq, GaussianEntropyDissipation.entropyDensity, g, ε, Function.comp_def] using
    hlog.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hmass)

/-- Bounded C¹ inputs have a genuine finite square-entropy integral. -/
theorem core_sq_mul_log_integrable {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) γ := by
  apply integrable_sq_mul_log_of_memLp_four
  exact MemLp.of_bound hf.continuous.measurable.aestronglyMeasurable M
    (Filter.Eventually.of_forall hfb)

/-- The variance-one Gaussian log-Sobolev inequality on bounded C¹ functions
with bounded actual derivative; zeros of `f` are allowed. -/
theorem gaussian_logSobolev_core {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M)
    (hfdb : ∀ x, ‖deriv f x‖ ≤ M) :
    entropySq γ f ≤ 2 * ∫ x, (deriv f x) ^ 2 ∂γ := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hfb 0)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let g : ℕ → ℝ → ℝ := fun n x => f x ^ 2 + ε n
  have hfsq (x : ℝ) : f x ^ 2 ≤ M ^ 2 := by
    calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using hfb x) 2
  have hseq (n : ℕ) :
      GaussianEntropyDissipation.entropyDensity (g n) ≤
        2 * ∫ x, (deriv f x) ^ 2 ∂γ := by
    have hε : 0 < ε n := by dsimp [ε]; positivity
    have hεle : ε n ≤ 1 := by
      dsimp [ε]
      exact (div_le_one (by positivity)).2 (by exact_mod_cast Nat.succ_pos n)
    let K : ℝ := 3 * M ^ 2 + 1
    have hgC : ContDiff ℝ 1 (g n) := (hf.pow 2).add contDiff_const
    have hlo (x : ℝ) : ε n ≤ g n x := by dsimp [g]; nlinarith [sq_nonneg (f x)]
    have hhi (x : ℝ) : g n x ≤ K := by dsimp [g, K]; nlinarith [hfsq x, sq_nonneg M]
    have hderiv (x : ℝ) : ‖deriv (g n) x‖ ≤ K := by
      have hdg := regularized_deriv hf (ε n) x
      change ‖deriv (fun y => f y ^ 2 + ε n) x‖ ≤ K
      rw [hdg, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hf1 : |f x| ≤ M := by simpa [Real.norm_eq_abs] using hfb x
      have hf2 : |deriv f x| ≤ M := by simpa [Real.norm_eq_abs] using hfdb x
      have hprod := mul_le_mul hf1 hf2 (abs_nonneg (deriv f x)) hM
      dsimp [K]
      nlinarith [sq_nonneg M]
    have hE := entropyDensity_le_half_fisher (g n) hgC hε hlo hhi hderiv
    have hI := regularized_fisher_le_energy hf hM hε hfb hfdb
    change GaussianFisher.fisherInformation (g n) ≤ 4 * ∫ x, (deriv f x) ^ 2 ∂γ at hI
    linarith
  have hlim : Tendsto (fun n => GaussianEntropyDissipation.entropyDensity (g n))
      atTop (𝓝 (entropySq γ f)) := by
    simpa only [g, ε] using regularized_entropy_tendsto hf.continuous hfb
  exact le_of_tendsto' hlim hseq

end OperatorDerivativeRewrite.Foundation.GaussianLogSobolevCore
