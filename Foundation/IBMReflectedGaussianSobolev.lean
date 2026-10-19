import Foundation.GaussianHermiteAdjoints
import Foundation.SmoothAbsoluteApproximation
import Foundation.FiniteMeasureL2Dominated
import Foundation.BrownianTanakaApproximation
import Foundation.IBMTimeAveragedObservable
import Mathlib.Analysis.Calculus.MeanValue

/-! Analytic-to-operator Gaussian Sobolev bridge for the reflected-clock route.
All graph statements refer to the existing polynomial-closure derivative. -/
noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMReflectedGaussianSobolev
open GaussianCore
open BrownianSignIntegral RealSteklovApprox

theorem stein_of_integrable {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hf : Integrable f γ) (hh : Integrable h γ)
    (hxf : Integrable (fun x => f x * x) γ) :
    (∫ x, h x ∂γ) = ∫ x, f x * x ∂γ := by
  have hi : Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using integrable_density_mul hf
  have hhi : Integrable (fun x => h x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using integrable_density_mul hh
  have hni : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert (integrable_density_mul hxf).neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hb := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hd x) (fun x _ => density_hasDerivAt x) hni hhi hi
  rw [integral_gaussianReal_eq_integral_smul (by norm_num),
    integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]
  have he : (fun x => f x * (-x * gaussianPDFReal 0 1 x)) =
      -(fun x => gaussianPDFReal 0 1 x * (f x * x)) := by
    funext x
    simp only [Pi.neg_apply]
    ring
  rw [he] at hb
  change (∫ x, -(gaussianPDFReal 0 1 x * (f x * x))) =
    -(∫ x, h x * gaussianPDFReal 0 1 x) at hb
  rw [integral_neg] at hb
  have heh : (∫ x, h x * gaussianPDFReal 0 1 x) =
      ∫ x, gaussianPDFReal 0 1 x * h x := by
    congr 1
    funext x
    ring
  rw [heh] at hb
  linarith

theorem polynomial_test_ibp {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hf : MemLp f 2 γ) (hh : MemLp h 2 γ) (q : ℝ[X]) :
    (∫ x, h x * q.eval x ∂γ) = ∫ x, f x * (divergencePolynomial q).eval x ∂γ := by
  have hq (p : ℝ[X]) := polynomial_memLp p 2 (by norm_num)
  have hi (p : ℝ[X]) : Integrable (fun x => f x * p.eval x) γ := hf.integrable_mul (hq p)
  have hj : Integrable (fun x => h x * q.eval x) γ := hh.integrable_mul (hq q)
  have hqx : Integrable (fun x => (f x * q.eval x) * x) γ := by
    convert hi (q * X) using 1
    funext x
    simp only [eval_mul, eval_X]
    ring
  have hdq (x : ℝ) : HasDerivAt (fun x => f x * q.eval x)
      (h x * q.eval x + f x * q.derivative.eval x) x := (hd x).mul (q.hasDerivAt x)
  have he := stein_of_integrable hdq (hi q) (hj.add (hi q.derivative)) hqx
  rw [integral_add hj (hi q.derivative)] at he
  have hx : Integrable (fun x => f x * (x * q.eval x)) γ := by
    convert hi (X * q) using 1
    simp
  simp only [divergencePolynomial, eval_sub, eval_mul, eval_X, mul_sub]
  rw [integral_sub hx (hi q.derivative)]
  have hre : (∫ x, f x * (x * q.eval x) ∂γ) = ∫ x, (f x * q.eval x) * x ∂γ := by
    congr 1
    funext x
    ring
  rw [hre]
  linarith

/-- Genuine classical L2 derivatives belong to the already verified closed graph. -/
theorem classical_closed_graph {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hf : MemLp f 2 γ) (hh : MemLp h 2 γ) :
    (hf.toLp f, hh.toLp h) ∈ closedDerivative.graph := by
  rw [closedDerivative_eq_divergence_adjoint,
    LinearPMap.adjoint_graph_eq_graph_adjoint polynomialDivergence_dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro u v huv
  rw [polynomialDivergence_graph] at huv
  obtain ⟨q, hq⟩ := huv
  have hu := congrArg Prod.fst hq
  have hv := congrArg Prod.snd hq
  change polynomialL2 q = u at hu
  change polynomialL2 (divergencePolynomial q) = v at hv
  subst u
  subst v
  simp only [sub_eq_zero]
  conv_lhs => rw [real_inner_comm]
  conv_rhs => rw [real_inner_comm]
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  have ha : (∫ x, inner ℝ (hf.toLp f x) (polynomialL2 (divergencePolynomial q) x) ∂γ) =
      ∫ x, f x * (divergencePolynomial q).eval x ∂γ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, polynomialL2_coeFn (divergencePolynomial q)] with x hx hq
    simp only [hx, hq, Real.inner_apply]
  have hb : (∫ x, inner ℝ (hh.toLp h x) (polynomialL2 q x) ∂γ) =
      ∫ x, h x * q.eval x ∂γ := by
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp, polynomialL2_coeFn q] with x hx hq
    simp only [hx, hq, Real.inner_apply]
  rw [ha, hb]
  exact (polynomial_test_ibp hd hf hh q).symm

theorem lipschitz_comp_memLp {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : MemLp g 2 γ) :
    MemLp (fun x => f (g x)) 2 γ := by
  let ψ : ℝ → ℝ := fun x => f x - f 0
  have hψ : LipschitzWith K ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [ψ, dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  have hm := (hψ.comp_memLp (sub_self (f 0)) hg).add (memLp_const (f 0))
  convert hm using 1
  funext x
  simp [ψ, Function.comp_def]

theorem radius_tendsto (x : ℝ) :
    Tendsto (fun n => SmoothAbsoluteApproximation.radius (width n) x) atTop (𝓝 |x|) := by
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := x ^ 2)).add ((width_tendsto.mono_right nhdsWithin_le_nhds).pow 2))
  simpa only [Function.comp_def, SmoothAbsoluteApproximation.radius, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    add_zero, Real.sqrt_sq_eq_abs] using ht

theorem reflected_memLp {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    MemLp (fun x => f |x|) 2 γ :=
  lipschitz_comp_memLp hf (by simpa only [eval_X, Real.norm_eq_abs] using
    (polynomial_memLp X 2 (by norm_num)).norm)

theorem reflectedDerivative_memLp {g : ℝ → ℝ} (hg : Continuous g)
    {K : ℝ} (hK : ∀ x, ‖g x‖ ≤ K) :
    MemLp (fun x => g |x| * signum x) 2 γ := by
  apply MemLp.of_bound ((hg.measurable.comp continuous_abs.measurable).mul signum_measurable).aestronglyMeasurable K
  apply ae_of_all
  intro x
  change ‖g |x| * signum x‖ ≤ K
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (signum_bound x) (norm_nonneg _)).trans
    (by simpa using hK |x|)

/-- Reflection has the genuine weak derivative g(|x|) sign(x), including
the cusp, in the existing Gaussian polynomial-closure graph. -/
theorem reflected_closed_graph {f g : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    {K : ℝ≥0} (hK : ∀ x, ‖g x‖ ≤ K) :
    ∃ (hf : MemLp (fun x => f |x|) 2 γ)
      (hh : MemLp (fun x => g |x| * signum x) 2 γ),
      (hf.toLp _, hh.toLp _) ∈ closedDerivative.graph := by
  have hLip : LipschitzWith K f := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    exact_mod_cast hK x
  let F (n : ℕ) (x : ℝ) := f (SmoothAbsoluteApproximation.radius (width n) x)
  let G (n : ℕ) (x : ℝ) := g (SmoothAbsoluteApproximation.radius (width n) x) *
    SmoothAbsoluteApproximation.slope (width n) x
  have hrad (n : ℕ) : MemLp (SmoothAbsoluteApproximation.radius (width n)) 2 γ := by
    apply ((polynomial_memLp X 2 (by norm_num)).norm.add (memLp_const (width n))).mono'
      ((SmoothAbsoluteApproximation.radius_smooth (width_pos n) 1).continuous.aestronglyMeasurable)
    apply ae_of_all
    intro x
    simpa only [Real.norm_eq_abs, abs_of_pos (SmoothAbsoluteApproximation.radius_pos (width_pos n) x),
      Pi.add_apply, eval_X] using SmoothAbsoluteApproximation.radius_le_abs_add (width_pos n) x
  have hF (n : ℕ) : MemLp (F n) 2 γ := lipschitz_comp_memLp hLip (hrad n)
  have hGb (n : ℕ) (x : ℝ) : ‖G n x‖ ≤ K := by
    dsimp only [G]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (SmoothAbsoluteApproximation.slope_bound (width_pos n) x)
      (norm_nonneg _)).trans (by simpa using hK _)
  have hG (n : ℕ) : MemLp (G n) 2 γ := by
    apply MemLp.of_bound ?_ K (ae_of_all _ (hGb n))
    have hs : Continuous (SmoothAbsoluteApproximation.slope (width n)) :=
      continuous_iff_continuousAt.mpr fun x =>
        (SmoothAbsoluteApproximation.slope_hasDerivAt (width_pos n) x).continuousAt
    exact ((hg.comp (SmoothAbsoluteApproximation.radius_smooth (width_pos n) 1).continuous).mul hs).aestronglyMeasurable
  have hFG (n : ℕ) : ((hF n).toLp _, (hG n).toLp _) ∈ closedDerivative.graph := by
    apply classical_closed_graph _ (hF n) (hG n)
    intro x
    exact (hd _).comp x (SmoothAbsoluteApproximation.radius_hasDerivAt (width_pos n) x)
  let hf := reflected_memLp hLip
  let hh := reflectedDerivative_memLp hg hK
  have htF : Tendsto (fun n => (hF n).toLp _) atTop (𝓝 (hf.toLp _)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hb (n : ℕ) : ‖(hF n).toLp _ - hf.toLp _‖ ≤ (K : ℝ) * width n := by
      have hn := Lp.norm_le_of_ae_bound (mul_nonneg K.coe_nonneg (width_pos n).le)
        (f := (hF n).toLp _ - hf.toLp _) ?_
      · simpa [measureUnivNNReal] using hn
      filter_upwards [Lp.coeFn_sub ((hF n).toLp _) (hf.toLp _), (hF n).coeFn_toLp,
        hf.coeFn_toLp] with x hs ha hb
      rw [hs]
      change ‖(hF n).toLp _ x - hf.toLp _ x‖ ≤ _
      rw [ha, hb]
      exact (hLip.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left
        (SmoothAbsoluteApproximation.uniform_error (width_pos n) x) K.coe_nonneg)
    exact squeeze_zero (fun n => norm_nonneg _) hb (by
      simpa only [mul_zero] using (width_tendsto.mono_right nhdsWithin_le_nhds).const_mul (K : ℝ))
  have htG : Tendsto (fun n => (hG n).toLp _) atTop (𝓝 (hh.toLp _)) := by
    apply FiniteMeasureL2Dominated.toLp_tendsto_of_constant_bound G _ hG hh K K.coe_nonneg
      (fun n => ae_of_all _ (hGb n))
    · apply ae_of_all
      intro x
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (signum_bound x) (norm_nonneg _)).trans
        (by simpa using hK |x|)
    · apply ae_of_all
      intro x
      exact ((hg.continuousAt.tendsto.comp (radius_tendsto x)).mul (BrownianTanakaApproximation.slope_tendsto_sign x))
  exact ⟨hf, hh, closedDerivative_isClosed.mem_of_tendsto (htF.prodMk_nhds htG)
    (Eventually.of_forall hFG)⟩

/-- Every scalar source test of the actual mollified scenery has a genuine
reflected Gaussian derivative graph, at every real Gaussian scale. -/
theorem mollified_pair_reflected_graph (n : ℕ) (V : InfiniteGaussian.GaussianL2) (a : ℝ) :
    ∃ (hf : MemLp (fun x : ℝ => inner ℝ V
          (IBMContinuousScenery.wholeLineScenery (IBMMollifier.kernel n) (a * |x|))) 2 γ)
      (hg : MemLp (fun x : ℝ => a * inner ℝ V
          (IBMClockAverageCandidate.sourceColumn n (a * |x|)) * signum x) 2 γ),
      (hf.toLp _, hg.toLp _) ∈ closedDerivative.graph := by
  let f : ℝ → ℝ := fun r => inner ℝ V
    (IBMContinuousScenery.wholeLineScenery (IBMMollifier.kernel n) (a * r))
  let g : ℝ → ℝ := fun r => a * inner ℝ V (IBMClockAverageCandidate.sourceColumn n (a * r))
  have hd (r : ℝ) : HasDerivAt f (g r) r := by
    have h := (innerSL ℝ V).hasFDerivAt.comp_hasDerivAt (a * r)
      (IBMTimeAveragedObservable.mollified_hasDerivAt n (a * r))
    convert h.comp r ((hasDerivAt_id r).const_mul a) using 1 <;>
      first | rfl | (dsimp [f, g]; ring)
  have hgc : Continuous g := by
    exact continuous_const.mul
      (continuous_const.inner ((IBMClockAverageCandidate.sourceColumn_continuous n).comp
        (continuous_const.mul continuous_id)))
  obtain ⟨C, hC, hb⟩ := IBMClockAverageCandidate.sourceColumn_bounded n
  have hbound (r : ℝ) : ‖g r‖ ≤ |a| * ‖V‖ * C := by
    dsimp only [g]
    rw [norm_mul, Real.norm_eq_abs]
    calc
      |a| * ‖inner ℝ V (IBMClockAverageCandidate.sourceColumn n (a * r))‖ ≤
          |a| * (‖V‖ * ‖IBMClockAverageCandidate.sourceColumn n (a * r)‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (abs_nonneg _)
      _ ≤ |a| * (‖V‖ * C) := by gcongr; exact hb _
      _ = |a| * ‖V‖ * C := by ring
  exact reflected_closed_graph hd hgc (K := ⟨|a| * ‖V‖ * C, by positivity⟩) hbound

end OperatorDerivativeRewrite.Foundation.IBMReflectedGaussianSobolev
