import Foundation.GaussianSmoothIto

/-! Genuine L2 quadratic variation of smooth clock functions. This is the
supporting clock theorem for compensated IBM quadratic-Wick tests; it is not
an assumption that the surviving IBM kernels converge strongly. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSmoothQuadraticVariation
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open GaussianTaylorRemainder GaussianLipschitzIntegrands

theorem function_lipschitz (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) : LipschitzWith A f :=
  lipschitzWith_of_nnnorm_deriv_le (hf.differentiable (by norm_num)) hA

theorem derivative_lipschitz (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (B : ℝ≥0)
    (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) : LipschitzWith B (deriv f) := by
  apply lipschitzWith_of_nnnorm_deriv_le _ hB
  simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)

theorem linear_error_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (B : ℝ≥0)
    (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (x y : ℝ) :
    ‖f y-f x-deriv f x*(y-x)‖ ≤ (B:ℝ)/2*|y-x|^2 := by
  by_cases hxy : x=y
  · subst y
    simp
  obtain ⟨z,_,hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) hxy hf.contDiffOn
  have hd : iteratedDerivWithin 1 f (uIcc x y) x = iteratedDeriv 1 f x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
      (hf.of_le (by norm_num)).contDiffAt (left_mem_uIcc)
  have he : taylorWithinEval f 1 (uIcc x y) x y = f x+deriv f x*(y-x) := by
    rw [taylorWithinEval_succ f 0, taylor_within_zero_eval, hd]
    norm_num [iteratedDeriv_one, smul_eq_mul] <;> ring
  rw [he] at hz
  have hr : f y-f x-deriv f x*(y-x) = deriv (deriv f) z*(y-x)^2/2 := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hz
    norm_num at hz
    linarith
  rw [hr,norm_div,norm_mul,norm_pow,Real.norm_eq_abs (y-x)]
  norm_num only [Real.norm_ofNat]
  have hb : ‖deriv (deriv f) z‖ ≤ (B:ℝ) := hB z
  nlinarith [sq_nonneg |y-x|]

def quadraticError (f : ℝ → ℝ) (x y : ℝ) : ℝ := (f y-f x)^2-(deriv f x)^2*(y-x)^2

theorem quadratic_error_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (x y : ℝ) :
    ‖quadraticError f x y‖ ≤ (A:ℝ)*B*|y-x|^3 := by
  have hlin := linear_error_bound f hf B hB x y
  have hinc : ‖f y-f x‖ ≤ (A:ℝ)*|y-x| := by
    simpa only [Real.norm_eq_abs] using (function_lipschitz f hf A hA).norm_sub_le y x
  have hd : ‖deriv f x*(y-x)‖ ≤ (A:ℝ)*|y-x| := by
    rw [norm_mul,Real.norm_eq_abs (y-x)]
    exact mul_le_mul_of_nonneg_right (show ‖deriv f x‖ ≤ (A:ℝ) from hA x) (abs_nonneg _)
  have hsum : ‖(f y-f x)+deriv f x*(y-x)‖ ≤ 2*(A:ℝ)*|y-x| :=
    (norm_add_le _ _).trans (by linarith)
  have he : quadraticError f x y =
      (f y-f x-deriv f x*(y-x))*((f y-f x)+deriv f x*(y-x)) := by
    unfold quadraticError
    ring
  rw [he,norm_mul]
  calc
    _ ≤ ((B:ℝ)/2*|y-x|^2)*(2*(A:ℝ)*|y-x|) :=
      mul_le_mul hlin hsum (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem square_derivative_lipschitz (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) : LipschitzWith (2*A*B) (fun x => (deriv f x)^2) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  have hd := (derivative_lipschitz f hf B hB).norm_sub_le x y
  have hx : ‖deriv f x‖ ≤ (A:ℝ) := hA x
  have hy : ‖deriv f y‖ ≤ (A:ℝ) := hA y
  have hs : ‖deriv f x+deriv f y‖ ≤ 2*(A:ℝ) := (norm_add_le _ _).trans (by linarith)
  rw [dist_eq_norm,dist_eq_norm]
  have he : (deriv f x)^2-(deriv f y)^2 = (deriv f x-deriv f y)*(deriv f x+deriv f y) := by ring
  rw [he,norm_mul]
  calc
    _ ≤ ((B:ℝ)*‖x-y‖)*(2*(A:ℝ)) := mul_le_mul hd hs (norm_nonneg _) (by positivity)
    _ = _ := by push_cast; ring

theorem error_memLp (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (s t : ℝ≥0) (hst : s ≤ t) :
    MemLp (fun Y => quadraticError f (process s Y) (process t Y)) 2 gaussianProduct := by
  have hm : Measurable (fun Y => quadraticError f (process s Y) (process t Y)) := by
    have hd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
    exact (((hf.continuous.measurable.comp (process_stronglyMeasurable t).measurable).sub
      (hf.continuous.measurable.comp (process_stronglyMeasurable s).measurable)).pow_const 2).sub
      (((hd.measurable.comp (process_stronglyMeasurable s).measurable).pow_const 2).mul
        (((process_stronglyMeasurable t).measurable.sub (process_stronglyMeasurable s).measurable).pow_const 2))
  apply (Lp.memLp (incrementCube s t)).of_le_mul hm.aestronglyMeasurable (c := (A:ℝ)*B)
  filter_upwards [incrementCube_coeFn s t hst] with Y hY
  simpa only [hY,norm_pow,Real.norm_eq_abs] using quadratic_error_bound f hf A B hA hB (process s Y) (process t Y)

def errorL2 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (s t : ℝ≥0) (hst : s ≤ t) : GaussianL2 :=
  (error_memLp f hf A B hA hB s t hst).toLp _

theorem errorL2_norm_sq (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (s t : ℝ≥0) (hst : s ≤ t) :
    ‖errorL2 f hf A B hA hB s t hst‖^2 ≤ ((A:ℝ)*B)^2*15*((t:ℝ)-s)^3 := by
  have hb : ‖errorL2 f hf A B hA hB s t hst‖ ≤ (A:ℝ)*B*‖incrementCube s t‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(error_memLp f hf A B hA hB s t hst).coeFn_toLp,
      incrementCube_coeFn s t hst] with Y he hc
    change errorL2 f hf A B hA hB s t hst Y = quadraticError f (process s Y) (process t Y) at he
    simpa only [he,hc,norm_pow,Real.norm_eq_abs] using quadratic_error_bound f hf A B hA hB (process s Y) (process t Y)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow,incrementCube_norm_sq s t hst,mul_assoc] using hs

def errorSum (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  ∑ i : Fin (N+1), errorL2 f hf A B hA hB (uniformTime T N i.castSucc)
    (uniformTime T N i.succ) (uniformTime_monotone T N (Fin.castSucc_le_succ i))

theorem errorSum_norm_sq (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (T : ℝ≥0) (N : ℕ) :
    ‖errorSum f hf A B hA hB T N‖^2 ≤ ((A:ℝ)*B)^2*15*(T:ℝ)^3/(N+1) := by
  calc
    _ ≤ (N+1:ℝ)*∑ i : Fin (N+1),
        ‖errorL2 f hf A B hA hB (uniformTime T N i.castSucc) (uniformTime T N i.succ)
          (uniformTime_monotone T N (Fin.castSucc_le_succ i))‖^2 := by
      simpa only [errorSum,Nat.cast_add,Nat.cast_one] using norm_sum_sq_le
        (fun i : Fin (N+1) => errorL2 f hf A B hA hB (uniformTime T N i.castSucc)
          (uniformTime T N i.succ) (uniformTime_monotone T N (Fin.castSucc_le_succ i)))
    _ ≤ (N+1:ℝ)*∑ _i : Fin (N+1), ((A:ℝ)*B)^2*15*((T:ℝ)/(N+1))^3 := by
      gcongr with i
      simpa only [uniformTime_step] using errorL2_norm_sq f hf A B hA hB
        (uniformTime T N i.castSucc) (uniformTime T N i.succ) (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      field_simp <;> ring

theorem errorSum_tendsto (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (T : ℝ≥0) : Tendsto (errorSum f hf A B hA hB T) atTop (𝓝 0) := by
  have hr : Tendsto (fun N : ℕ => ((A:ℝ)*B)^2*15*(T:ℝ)^3/(N+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hn := squeeze_zero (fun N => sq_nonneg _) (errorSum_norm_sq f hf A B hA hB T) hr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simp only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hs

theorem errorSum_coeFn (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (T : ℝ≥0) (N : ℕ) :
    errorSum f hf A B hA hB T N =ᵐ[gaussianProduct] fun Y => ∑ i : Fin (N+1),
      quadraticError f (process (uniformTime T N i.castSucc) Y) (process (uniformTime T N i.succ) Y) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (N+1) =>
      errorL2 f hf A B hA hB (uniformTime T N i.castSucc) (uniformTime T N i.succ)
        (uniformTime_monotone T N (Fin.castSucc_le_succ i))),
    ae_all_iff.mpr (fun i : Fin (N+1) => (error_memLp f hf A B hA hB
      (uniformTime T N i.castSucc) (uniformTime T N i.succ)
        (uniformTime_monotone T N (Fin.castSucc_le_succ i))).coeFn_toLp)] with Y hs hi
  change errorSum f hf A B hA hB T N Y = _ at hs
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hi i

def quadraticSum (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  (errorSum f hf A B hA hB T N +
    GaussianLipschitzQuadraticVariation.error (square_derivative_lipschitz f hf A B hA hB) T N) +
      GaussianSmoothIto.driftSum (square_derivative_lipschitz f hf A B hA hB) T N

theorem quadraticSum_actual (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (T : ℝ≥0) (N : ℕ) :
    quadraticSum f hf A B hA hB T N =ᵐ[gaussianProduct] fun Y => ∑ i : Fin (N+1),
      (f (process (uniformTime T N i.succ) Y)-f (process (uniformTime T N i.castSucc) Y))^2 := by
  let w := square_derivative_lipschitz f hf A B hA hB
  let R := errorSum f hf A B hA hB T N
  let E := GaussianLipschitzQuadraticVariation.error w T N
  let D := GaussianSmoothIto.driftSum w T N
  filter_upwards [Lp.coeFn_add (R+E) D,Lp.coeFn_add R E,
    errorSum_coeFn f hf A B hA hB T N,
    GaussianLipschitzQuadraticVariation.error_coeFn w T N,
    GaussianSmoothIto.driftSum_coeFn w T N] with Y h1 h2 hr he hd
  change ((R+E)+D) Y = _
  rw [h1,Pi.add_apply,h2,Pi.add_apply,hr,he,hd]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [quadraticError]
  ring

theorem quadraticSum_tendsto (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ≥0)
    (hA : ∀ x, ‖deriv f x‖₊ ≤ A) (hB : ∀ x, ‖deriv (deriv f) x‖₊ ≤ B) (T : ℝ≥0) :
    Tendsto (quadraticSum f hf A B hA hB T) atTop
      (𝓝 (∫ t in 0..(T:ℝ), valueL2 (square_derivative_lipschitz f hf A B hA hB) t.toNNReal)) := by
  have h := ((errorSum_tendsto f hf A B hA hB T).add
    (GaussianLipschitzQuadraticVariation.error_tendsto
      (square_derivative_lipschitz f hf A B hA hB) T)).add
        (GaussianLipschitzIntegrands.drift_sum_tendsto (square_derivative_lipschitz f hf A B hA hB) T)
  unfold quadraticSum GaussianSmoothIto.driftSum
  simpa only [zero_add] using h

end OperatorDerivativeRewrite.Foundation.GaussianSmoothQuadraticVariation
