import Foundation.IBMFoldedSourceCovariance
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Actual source averaging gains finite-clock Lipschitz regularity. These
are value/L2 estimates, not an unproved Gaussian graph-domain assertion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFourierClockMeanRegularity
open InfiniteGaussian IBMFoldedSourceCovariance

def damping (q : ℝ) : ℝ := Real.exp (-q/2)

theorem damping_derivative (q : ℝ) : HasDerivAt damping (-(1/2:ℝ)*damping q) q := by
  have h := (((hasDerivAt_id q).neg).div_const 2).exp
  change HasDerivAt (fun x => Real.exp (-x/2)) (-(1/2:ℝ)*Real.exp (-q/2)) q
  convert h using 1 <;> simp only [Pi.neg_apply,id_eq] <;> ring

theorem damping_bound {q : ℝ} (hq : 0 ≤ q) : ‖damping q‖ ≤ 1 := by
  unfold damping
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem damping_difference {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) :
    |damping q-damping r| ≤ (1/2:ℝ)*|q-r| := by
  have hb (t : ℝ) (ht : t ∈ Ici (0:ℝ)) : ‖deriv damping t‖ ≤ (1/2:ℝ) := by
    rw [(damping_derivative t).deriv,norm_mul,Real.norm_eq_abs,
      abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    exact (mul_le_mul_of_nonneg_left (damping_bound ht) (by norm_num)).trans_eq (mul_one _)
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (damping_derivative t).differentiableAt) hb (convex_Ici (0:ℝ)) hr hq

variable {ι : Type*} [Fintype ι] (a : ℕ → ι → ℝ) (β w : ℕ → ℝ)

def term (k : ℕ) (x : ι → ℝ) : ℝ := w k*Real.cos (β k)*damping (variance (a k) x)
def value (x : ι → ℝ) : ℝ := ∑' k, term a β w k x

theorem term_bound (k : ℕ) (x : ι → ℝ) : ‖term a β w k x‖ ≤ |w k| := by
  rw [term,norm_mul,norm_mul,Real.norm_eq_abs]
  have hc : ‖Real.cos (β k)‖ ≤ 1 := Real.abs_cos_le_one _
  have hd := damping_bound (variance_nonneg (a k) x)
  have hcd := mul_le_mul hc hd (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hm := mul_le_mul_of_nonneg_left hcd (abs_nonneg (w k))
  nlinarith

theorem term_difference (k : ℕ) (x y : ι → ℝ) :
    ‖term a β w k x-term a β w k y‖ ≤
      (IBMFourierCylinderSeries.curvatureCost a w k/2)*‖x-y‖ := by
  rw [term,term,← mul_sub,norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  have hd := (damping_difference (variance_nonneg (a k) x) (variance_nonneg (a k) y)).trans
    (mul_le_mul_of_nonneg_left (variance_difference (a k) x y) (by norm_num : (0:ℝ) ≤ 1/2))
  have hh : |w k| * |Real.cos (β k)| ≤ |w k| := by
    simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (β k)) (abs_nonneg (w k))
  have hm := mul_le_mul hh hd (abs_nonneg _) (abs_nonneg (w k))
  simpa only [IBMFourierCylinderSeries.curvatureCost,mul_assoc,div_eq_mul_inv,mul_left_comm,mul_comm,one_mul,Real.norm_eq_abs] using hm

theorem value_difference (hv : Summable (fun k => |w k|))
    (hc : Summable (IBMFourierCylinderSeries.curvatureCost a w)) (x y : ι → ℝ) :
    ‖value a β w x-value a β w y‖ ≤
      ((∑' k, IBMFourierCylinderSeries.curvatureCost a w k)/2)*‖x-y‖ := by
  have hx : Summable (fun k => term a β w k x) := hv.of_norm_bounded (fun k => term_bound a β w k x)
  have hy : Summable (fun k => term a β w k y) := hv.of_norm_bounded (fun k => term_bound a β w k y)
  have hb : Summable (fun k => (IBMFourierCylinderSeries.curvatureCost a w k/2)*‖x-y‖) :=
    (hc.div_const 2).mul_right _
  have hn : Summable (fun k => ‖term a β w k x-term a β w k y‖) :=
    hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => term_difference a β w k x y)
  change ‖(∑' k, term a β w k x)-(∑' k, term a β w k y)‖ ≤ _
  rw [← hx.tsum_sub hy]
  apply (norm_tsum_le_tsum_norm hn).trans
  have ht := hn.tsum_le_tsum (fun k => term_difference a β w k x y) hb
  simpa only [tsum_mul_right,tsum_div_const] using ht

theorem sourceMean_eq (x : ι → ℝ) :
    IBMFourierSourceMeanCalculus.sourceMean a β w (fun i => direction (x i)) = value a β w x := by
  unfold IBMFourierSourceMeanCalculus.sourceMean value
  apply tsum_congr
  intro k
  rw [IBMFourierSourceMeanCalculus.meanTerm,IBMBoundedGaussianMeanDerivative.mean,
    IBMFourierRidgeCoefficients.mode_mean,IBMFourierSourceMeanCalculus.row_apply]
  simp only [term,damping,variance,mul_assoc]

theorem clockMean_actual (r : ι → ℝ≥0) (hv : Summable (fun k => |w k|)) :
    IBMFourierSourceMeanCalculus.clockMean a β w r =ᵐ[gaussianProduct]
      fun Y => value a β w (fun i => GaussianTimeProcess.process (r i) Y) := by
  filter_upwards [IBMFourierSourceMeanCalculus.clockMean_actual a β w r hv] with Y hY
  rw [hY,← sourceMean_eq a β w]
  rfl

theorem absolute_lipschitz : LipschitzWith 1 (fun x : ℝ => |x|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y

def absoluteDifference (s t : ℝ≥0) : GaussianL2 :=
  GaussianLipschitzIntegrands.composition absolute_lipschitz
    (GaussianTimeProcess.wienerL2 s-GaussianTimeProcess.wienerL2 t)

theorem absoluteDifference_actual (s t : ℝ≥0) : absoluteDifference s t =ᵐ[gaussianProduct]
    fun Y => |GaussianTimeProcess.process s Y-GaussianTimeProcess.process t Y| := by
  filter_upwards [GaussianLipschitzIntegrands.composition_coeFn absolute_lipschitz
    (GaussianTimeProcess.wienerL2 s-GaussianTimeProcess.wienerL2 t),
    Lp.coeFn_sub (GaussianTimeProcess.wienerL2 s) (GaussianTimeProcess.wienerL2 t)] with Y ha hs
  change absoluteDifference s t Y = _ at ha
  rw [ha,hs]
  rfl

theorem absoluteDifference_bound (s t : ℝ≥0) :
    ‖absoluteDifference s t‖ ≤ ‖GaussianTimeProcess.wienerL2 s-GaussianTimeProcess.wienerL2 t‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [absoluteDifference_actual s t,
    Lp.coeFn_sub (GaussianTimeProcess.wienerL2 s) (GaussianTimeProcess.wienerL2 t)] with Y ha hs
  rw [ha,hs]
  simp only [Pi.sub_apply,Real.norm_eq_abs,abs_abs,GaussianTimeProcess.process]
  exact le_rfl

theorem clockMean_stability (hv : Summable (fun k => |w k|))
    (hc : Summable (IBMFourierCylinderSeries.curvatureCost a w)) (r s : ι → ℝ≥0) :
    ‖IBMFourierSourceMeanCalculus.clockMean a β w r-IBMFourierSourceMeanCalculus.clockMean a β w s‖ ≤
      ((∑' k, IBMFourierCylinderSeries.curvatureCost a w k)/2)*
        ∑ i, ‖GaussianTimeProcess.wienerL2 (r i)-GaussianTimeProcess.wienerL2 (s i)‖ := by
  let L : ℝ := (∑' k, IBMFourierCylinderSeries.curvatureCost a w k)/2
  have hL : 0 ≤ L := div_nonneg (tsum_nonneg fun k => by
    dsimp [IBMFourierCylinderSeries.curvatureCost]; positivity) (by norm_num)
  have hb : ‖IBMFourierSourceMeanCalculus.clockMean a β w r-
      IBMFourierSourceMeanCalculus.clockMean a β w s‖ ≤
      L*‖∑ i, absoluteDifference (r i) (s i)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [clockMean_actual a β w r hv,clockMean_actual a β w s hv,
      Lp.coeFn_sub (IBMFourierSourceMeanCalculus.clockMean a β w r)
        (IBMFourierSourceMeanCalculus.clockMean a β w s),
      Lp.coeFn_finsetSum Finset.univ (fun i => absoluteDifference (r i) (s i)),
      ae_all_iff.mpr fun i => absoluteDifference_actual (r i) (s i)] with Y hr hs hd ht hi
    rw [hd,Pi.sub_apply,hr,hs]
    have hm : ‖(fun i => GaussianTimeProcess.process (r i) Y)-
        (fun i => GaussianTimeProcess.process (s i) Y)‖ ≤
        ∑ i, |GaussianTimeProcess.process (r i) Y-GaussianTimeProcess.process (s i) Y| := by
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).mpr
      intro i
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using
        Finset.single_le_sum (fun j _ => abs_nonneg
          (GaussianTimeProcess.process (r j) Y-GaussianTimeProcess.process (s j) Y)) (Finset.mem_univ i)
    have he : ‖(∑ i, absoluteDifference (r i) (s i)) Y‖ =
        ∑ i, |GaussianTimeProcess.process (r i) Y-GaussianTimeProcess.process (s i) Y| := by
      rw [ht]
      simp only [Finset.sum_apply,hi]
      exact Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
    rw [he]
    exact (value_difference a β w hv hc _ _).trans (mul_le_mul_of_nonneg_left hm hL)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hL
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => absoluteDifference_bound (r i) (s i))

theorem increment_norm (s t : ℝ≥0) :
    ‖GaussianTimeProcess.wienerL2 s-GaussianTimeProcess.wienerL2 t‖ = Real.sqrt |(s:ℝ)-t| := by
  have he : ‖GaussianTimeProcess.wienerL2 s-GaussianTimeProcess.wienerL2 t‖^2 = |(s:ℝ)-t| := by
    rcases le_total s t with h | h
    · rw [norm_sub_rev,GaussianTimeProcess.wienerL2_sub_norm_sq s t h,
        abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr h))]
      ring
    · rw [GaussianTimeProcess.wienerL2_sub_norm_sq t s h,
        abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))]
  rw [← he,Real.sqrt_sq (norm_nonneg _)]

theorem clockMean_halfHolder (hv : Summable (fun k => |w k|))
    (hc : Summable (IBMFourierCylinderSeries.curvatureCost a w)) (r s : ι → ℝ≥0) :
    ‖IBMFourierSourceMeanCalculus.clockMean a β w r-IBMFourierSourceMeanCalculus.clockMean a β w s‖ ≤
      ((∑' k, IBMFourierCylinderSeries.curvatureCost a w k)/2)*
        ∑ i, Real.sqrt |(r i:ℝ)-s i| := by
  simpa only [increment_norm] using clockMean_stability a β w hv hc r s

theorem folded_cosine_mean (x : ℝ) :
    (∫ X, Real.cos (firstChaosEmbedding (direction x) X) ∂gaussianProduct) = damping |x| := by
  have hn : ‖direction x‖^2 = |x| := by
    rw [direction,IBMActualQuarticMoment.sceneryDirection_norm_sq,abs_abs]
  simpa only [IBMFourierRidgeCoefficients.mode,zero_add,Real.cos_zero,one_mul,hn,damping] using
    IBMFourierRidgeCoefficients.mode_mean 0 (direction x)

theorem folded_damping_not_differentiable :
    ¬ DifferentiableAt ℝ (fun x : ℝ => damping |x|) 0 := by
  intro h
  have hn : damping |(0:ℝ)| ≠ 0 := by simp [damping]
  have hg := (h.log hn).const_mul (-2:ℝ)
  have he : (fun x : ℝ => (-2:ℝ)*Real.log (damping |x|)) = abs := by
    funext x
    rw [damping,Real.log_exp]
    ring
  change DifferentiableAt ℝ (fun x : ℝ => (-2:ℝ)*Real.log (damping |x|)) 0 at hg
  rw [he] at hg
  exact not_differentiableAt_abs_zero hg

theorem folded_cosine_not_differentiable :
    ¬ DifferentiableAt ℝ (fun x : ℝ =>
      ∫ X, Real.cos (firstChaosEmbedding (direction x) X) ∂gaussianProduct) 0 := by
  simpa only [folded_cosine_mean] using folded_damping_not_differentiable

end OperatorDerivativeRewrite.Foundation.IBMFourierClockMeanRegularity
