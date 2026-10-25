import Foundation.IBMMixedClockLimit

/-! Upgrade the actual random-observation mixed bracket from L1 to L2 using
the convergent ordinary Brownian quadratic-variation majorant. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMMixedClockStrongL2
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMMixedClockSelection IBMMixedClockLimit IBMClippedClockCrossing

theorem mixedSum_raw_bound (H R S : ℝ≥0) (N : ℕ) : ∀ᵐ Y ∂gaussianProduct,
    ‖mixedSum H R S N Y‖ ≤ ‖quadraticVariation (uniformTime H N) Y‖ := by
  filter_upwards [quadraticVariation_coeFn (uniformTime H N) (uniformTime_monotone H N)] with Y hY
  rw [hY,Real.norm_eq_abs]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum fun i _ =>
    IBMClippedClockCovariation.mixed_increment_bound (process R Y) (process S Y)
      (process (uniformTime H N i.castSucc) Y) (process (uniformTime H N i.succ) Y)).trans
  exact le_abs_self _

theorem mixedSum_memLp (H R S : ℝ≥0) (N : ℕ) :
    MemLp (mixedSum H R S N) 2 gaussianProduct :=
  (Lp.memLp (quadraticVariation (uniformTime H N))).norm.mono'
    (mixedSum_measurable H R S N).aestronglyMeasurable (mixedSum_raw_bound H R S N)

def mixedL2 (H R S : ℝ≥0) (N : ℕ) : GaussianL2 := (mixedSum_memLp H R S N).toLp _

theorem mixedL2_actual (H R S : ℝ≥0) (N : ℕ) :
    mixedL2 H R S N =ᵐ[gaussianProduct] mixedSum H R S N :=
  (mixedSum_memLp H R S N).coeFn_toLp

theorem occupation_bound (H R S : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct,
    ‖mixedOccupation H R S Y‖ ≤ H := by
  filter_upwards [selectedOccupation_actual H R S] with Y hY
  rw [← hY]
  unfold selectedOccupation select
  split_ifs <;> exact IBMObservedClockOccupation.occupation_norm_bound _ _ _

theorem occupation_memLp (H R S : ℝ≥0) : MemLp (mixedOccupation H R S) 2 gaussianProduct :=
  MemLp.of_bound (mixedOccupation_integrable H R S).aestronglyMeasurable H
    (occupation_bound H R S)

def occupationL2 (H R S : ℝ≥0) : GaussianL2 := (occupation_memLp H R S).toLp _

theorem occupationL2_actual (H R S : ℝ≥0) :
    occupationL2 H R S =ᵐ[gaussianProduct] mixedOccupation H R S :=
  (occupation_memLp H R S).coeFn_toLp

theorem scalar_error_bound (A q x y : ℝ) (hx : |x| ≤ q) (hy : |y| ≤ A) :
    (x-y)^2 ≤ 4*A*|x-y|+(q-A)^2 := by
  have he : |x-y| ≤ q+A := (abs_sub x y).trans (add_le_add hx hy)
  have hm := mul_le_mul_of_nonneg_right he (abs_nonneg (x-y))
  nlinarith [sq_nonneg (|x-y|-(q-A)),sq_abs (x-y)]

private theorem norm_sq_integral (u : GaussianL2) :
    ‖u‖^2 = ∫ Y, (u Y)^2 ∂gaussianProduct := by
  rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
  simp only [Real.inner_apply,pow_two]

theorem mixed_error_bound (H R S : ℝ≥0) (N : ℕ) :
    ‖mixedL2 H R S N-occupationL2 H R S‖^2 ≤
      4*(H:ℝ)*(∫ Y, |mixedSum H R S N Y-mixedOccupation H R S Y| ∂gaussianProduct)+
        2*(H:ℝ)^2/(N+1) := by
  let e := mixedL2 H R S N-occupationL2 H R S
  let q := quadraticVariation (uniformTime H N)-(H:ℝ) • gaussianOne
  have hea : e =ᵐ[gaussianProduct] fun Y => mixedSum H R S N Y-mixedOccupation H R S Y := by
    filter_upwards [Lp.coeFn_sub (mixedL2 H R S N) (occupationL2 H R S),
      mixedL2_actual H R S N,occupationL2_actual H R S] with Y he hf hg
    rw [he,Pi.sub_apply,hf,hg]
  have hq : q =ᵐ[gaussianProduct] fun Y => quadraticVariation (uniformTime H N) Y-H := by
    filter_upwards [Lp.coeFn_sub (quadraticVariation (uniformTime H N)) ((H:ℝ) • gaussianOne),
      Lp.coeFn_smul (H:ℝ) (gaussianOne:GaussianL2),gaussianOne_coeFn] with Y hs hm ho
    rw [hs,Pi.sub_apply,hm,Pi.smul_apply,ho,smul_eq_mul,mul_one]
  have hb : ∀ᵐ Y ∂gaussianProduct, (e Y)^2 ≤ 4*(H:ℝ)*|e Y|+(q Y)^2 := by
    filter_upwards [hea,hq,mixedSum_raw_bound H R S N,occupation_bound H R S,
      quadraticVariation_coeFn (uniformTime H N) (uniformTime_monotone H N)]
      with Y he hq' hm ho hvar
    have hpos : 0 ≤ quadraticVariation (uniformTime H N) Y := by
      rw [hvar]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [Real.norm_eq_abs,abs_of_nonneg hpos] at hm
    rw [Real.norm_eq_abs] at ho
    rw [he,hq']
    exact scalar_error_bound H _ _ _ hm ho
  have hi := integral_mono_ae (Lp.memLp e).integrable_sq
    (((Lp.memLp e).integrable (by norm_num)).abs.const_mul (4*(H:ℝ)) |>.add
      (Lp.memLp q).integrable_sq) hb
  simp only [Pi.add_apply] at hi
  rw [integral_add (((Lp.memLp e).integrable (by norm_num)).abs.const_mul (4*(H:ℝ)))
    (Lp.memLp q).integrable_sq,integral_const_mul,← norm_sq_integral e,
    ← norm_sq_integral q] at hi
  have hi' : (∫ Y, |e Y| ∂gaussianProduct) =
      ∫ Y, |mixedSum H R S N Y-mixedOccupation H R S Y| ∂gaussianProduct :=
    integral_congr_ae (hea.mono fun Y hY => congrArg abs hY)
  rw [hi',uniform_quadraticVariation_error] at hi
  exact hi

theorem mixedL2_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (mixedL2 H R S) atTop (𝓝 (occupationL2 H R S)) := by
  have hq : Tendsto (fun N : ℕ => 2*(H:ℝ)^2/(N+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have he := ((mixed_actual_absolute_tendsto H R S hH).const_mul (4*(H:ℝ))).add hq
  simp only [mul_zero,add_zero] at he
  have hs := squeeze_zero (fun N => sq_nonneg ‖mixedL2 H R S N-occupationL2 H R S‖)
    (mixed_error_bound H R S) he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using ht

end OperatorDerivativeRewrite.Foundation.IBMMixedClockStrongL2
