import Foundation.StochasticCauchyStoppedCoefficients
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! Actual polynomial cell errors and conditional stopping masks. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedErrors
open InfiniteGaussian StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyComplexChannels StochasticCauchyPhysicalInput StochasticCauchyExponentialInput
open StochasticCauchyPolynomialInput StochasticCauchyPolynomialPrediction StochasticCauchyStoppedDomains
open StochasticCauchyContinuousPolynomials StochasticCauchyExitMoments StochasticCauchyBrownianRealization
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyComplexChannels.complexInput_complete
  StochasticCauchyParameterizedObstruction.predictableTime
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct

/-- Every deterministic polynomial martingale increment has zero conditional mean
on the SPECIFIED augmented joint past. -/
theorem polynomial_increment_condExp (s t : ℝ≥0) (hst : s≤t) (p : Polynomial ℂ) :
    μ[(fun w => p.eval (value t w)-p.eval (value s w)) | augmentedJoint s] =ᵐ[μ] fun _ => (0:ℂ) := by
  have ht := polynomialProcess_integrable p t
  have hs := polynomialProcess_integrable p s
  have ha := condExp_sub (μ := μ) ht hs (augmentedJoint s)
  have hb := (polynomialProcess_martingale p).2 s t hst
  have hc := condExp_of_aestronglyMeasurable' (augmented_joint_le s)
    (polynomialProcess_stronglyAdapted p s).aestronglyMeasurable hs
  filter_upwards [ha,hb,hc] with w ha hb hc
  change μ[polynomialProcess p t-polynomialProcess p s | augmentedJoint s] w=0
  rw [ha]
  simp only [Pi.sub_apply]
  rw [hb,hc,sub_self]

/-- Genuine existing native step class, including unbounded polynomial coefficients. -/
def stepClass (s t : ℝ≥0) (hst : s≤t) (p : Polynomial ℂ) : JointComplex :=
  channel t false (((Real.sqrt 2:ℝ):ℂ) • combineInput t
    (polynomialStep t s t hst le_rfl p false) (polynomialStep t s t hst le_rfl p true))

theorem stepClass_actual (s t : ℝ≥0) (hst : s≤t) (p : Polynomial ℂ) :
    stepClass s t hst p =ᵐ[μ] fun w => p.eval (value s w)*(value t w-value s w) := by
  filter_upwards [StochasticCauchyPolynomialSums.finite_step_ae t s t hst le_rfl p,
    continuous_value_ae s,continuous_value_ae t] with w hw hs ht
  change stepClass s t hst p w = _ at hw
  rw [hw,← hs,← ht]

theorem step_memLp (s t : ℝ≥0) (hst : s≤t) (p : Polynomial ℂ) :
    MemLp (fun w => p.eval (value s w)*(value t w-value s w)) 2 μ :=
  (Lp.memLp (stepClass s t hst p)).ae_eq (stepClass_actual s t hst p)

/-- Conditional mean zero uses genuine product integrability, not a boundedness
assumption on the polynomial coefficient or an unconditional mean identity. -/
theorem polynomial_step_condExp (s t : ℝ≥0) (hst : s≤t) (p : Polynomial ℂ) :
    μ[(fun w => p.eval (value s w)*(value t w-value s w)) | augmentedJoint s] =ᵐ[μ] fun _ => (0:ℂ) := by
  have hp : AEStronglyMeasurable[augmentedJoint s] (fun w => p.eval (value s w)) μ :=
    (polynomialProcess_stronglyAdapted p s).aestronglyMeasurable
  have hd : Integrable (fun w => value t w-value s w) μ := by
    have h := (polynomialProcess_integrable (Polynomial.X:Polynomial ℂ) t).sub
      (polynomialProcess_integrable (Polynomial.X:Polynomial ℂ) s)
    change Integrable (fun w => polynomialProcess Polynomial.X t w-polynomialProcess Polynomial.X s w) μ at h
    simpa only [polynomialProcess,Polynomial.eval_X] using h
  have hi := (step_memLp s t hst p).integrable (by norm_num)
  have hc := condExp_bilin_of_aestronglyMeasurable_left
    (ContinuousLinearMap.mul ℝ ℂ) hp hi hd
  have hz : μ[(fun w => value t w-value s w) | augmentedJoint s] =ᵐ[μ] fun _ => (0:ℂ) := by
    simpa only [Polynomial.eval_X] using polynomial_increment_condExp s t hst (Polynomial.X:Polynomial ℂ)
  filter_upwards [hc,hz] with w hc hz
  change μ[(fun w => p.eval (value s w)*(value t w-value s w)) | augmentedJoint s] w=
    p.eval (value s w)*μ[(fun w => value t w-value s w) | augmentedJoint s] w at hc
  rw [hc,hz,mul_zero]

/-- Actual L2 cell Taylor error; it is not asserted to vanish individually. -/
def cellError (s t : ℝ≥0) (hst : s≤t) (p : Polynomial ℂ) : JointComplex :=
  polynomialClass t p-polynomialClass s p-stepClass s t hst p.derivative

theorem cellError_actual (s t : ℝ≥0) (hst : s≤t) (p : Polynomial ℂ) :
    cellError s t hst p =ᵐ[μ] fun w => p.eval (value t w)-p.eval (value s w)-
      p.derivative.eval (value s w)*(value t w-value s w) := by
  filter_upwards [Lp.coeFn_sub (polynomialClass t p-polynomialClass s p) (stepClass s t hst p.derivative),
    Lp.coeFn_sub (polynomialClass t p) (polynomialClass s p),
    continuous_polynomial_ae t p,continuous_polynomial_ae s p,stepClass_actual s t hst p.derivative] with w h1 h2 h3 h4 h5
  change cellError s t hst p w=(polynomialClass t p-polynomialClass s p) w-stepClass s t hst p.derivative w at h1
  change (polynomialClass t p-polynomialClass s p) w=polynomialClass t p w-polynomialClass s p w at h2
  rw [h1,h2,h3,h4,h5]

theorem cellError_condExp (s t : ℝ≥0) (hst : s≤t) (p : Polynomial ℂ) :
    μ[cellError s t hst p | augmentedJoint s] =ᵐ[μ] fun _ => (0:ℂ) := by
  have he := condExp_congr_ae (m := augmentedJoint s) (cellError_actual s t hst p)
  have hi : Integrable (fun w => p.eval (value t w)-p.eval (value s w)) μ :=
    (polynomialProcess_integrable p t).sub (polynomialProcess_integrable p s)
  have hs := (step_memLp s t hst p.derivative).integrable (by norm_num)
  have hc := condExp_sub (μ := μ) hi hs (augmentedJoint s)
  filter_upwards [he,hc,polynomial_increment_condExp s t hst p,
    polynomial_step_condExp s t hst p.derivative] with w he hc h1 h2
  change μ[(fun w => p.eval (value t w)-p.eval (value s w)-p.derivative.eval (value s w)*(value t w-value s w)) | augmentedJoint s] w=
    μ[(fun w => p.eval (value t w)-p.eval (value s w)) | augmentedJoint s] w-
      μ[(fun w => p.derivative.eval (value s w)*(value t w-value s w)) | augmentedJoint s] w at hc
  rw [he,hc,h1,h2,sub_self]

theorem cellError_past (s t : ℝ≥0) (hst : s≤t) (p : Polynomial ℂ) :
    AEStronglyMeasurable[augmentedJoint t] (cellError s t hst p) μ := by
  have ht := polynomialProcess_stronglyAdapted p t
  have hs := (polynomialProcess_stronglyAdapted p s).mono (augmentedJoint.mono hst)
  have hd := (polynomialProcess_stronglyAdapted p.derivative s).mono (augmentedJoint.mono hst)
  have hvt := continuous_stronglyAdapted t
  have hvs := (continuous_stronglyAdapted s).mono (augmentedJoint.mono hst)
  exact (ht.sub hs |>.sub (hd.mul (hvt.sub hvs))).aestronglyMeasurable.congr
    (cellError_actual s t hst p).symm

/-- Actual L2 indicator restriction; positivity supplies its norm contraction. -/
def masked (A : Set Sample) (hA : MeasurableSet A) (F : JointComplex) : JointComplex :=
  ((Lp.memLp F).indicator hA).toLp (A.indicator F)

theorem masked_actual (A : Set Sample) (hA : MeasurableSet A) (F : JointComplex) :
    masked A hA F =ᵐ[μ] A.indicator F := MemLp.coeFn_toLp _

theorem masked_norm_le (A : Set Sample) (hA : MeasurableSet A) (F : JointComplex) :
    ‖masked A hA F‖≤‖F‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [masked_actual A hA F] with w hw
  rw [hw]
  by_cases ha : w∈A
  · simp only [indicator_of_mem ha,le_refl]
  · simp only [indicator_of_notMem ha,norm_zero,norm_nonneg]

theorem masked_condExp_zero (s : ℝ≥0) (A : Set Sample) (hA : MeasurableSet[augmentedJoint s] A)
    (F : JointComplex) (hF : μ[F | augmentedJoint s] =ᵐ[μ] fun _ => (0:ℂ)) :
    μ[masked A (augmented_joint_le s _ hA) F | augmentedJoint s] =ᵐ[μ] fun _ => (0:ℂ) := by
  have he := condExp_congr_ae (m := augmentedJoint s) (masked_actual A (augmented_joint_le s _ hA) F)
  have hc := condExp_indicator ((Lp.memLp F).integrable (by norm_num)) hA
  filter_upwards [he,hc,hF] with w he hc hF
  rw [he,hc]
  by_cases hw : w∈A
  · simp only [indicator_of_mem hw,hF]
  · simp only [indicator_of_notMem hw]

theorem masked_past (s t : ℝ≥0) (hst : s≤t) (A : Set Sample)
    (hA : MeasurableSet[augmentedJoint s] A) (F : JointComplex)
    (hF : AEStronglyMeasurable[augmentedJoint t] F μ) :
    AEStronglyMeasurable[augmentedJoint t] (masked A (augmented_joint_le s _ hA) F) μ :=
by
  apply (hF.stronglyMeasurable_mk.indicator (augmentedJoint.mono hst _ hA)).aestronglyMeasurable.congr
  filter_upwards [masked_actual A (augmented_joint_le s _ hA) F,hF.ae_eq_mk] with w hw hf
  by_cases ha : w∈A
  · rw [indicator_of_mem ha,hw,indicator_of_mem ha]
    exact hf.symm
  · rw [indicator_of_notMem ha,hw,indicator_of_notMem ha]

/-- Full conditional zero gives orthogonality against EVERY admissible past L2 test. -/
theorem inner_zero_of_condExp (s : ℝ≥0) (F G : JointComplex)
    (hF : μ[F | augmentedJoint s] =ᵐ[μ] fun _ => (0:ℂ))
    (hG : AEStronglyMeasurable[augmentedJoint s] G μ) : inner ℂ F G=0 := by
  have hp := Lp.memLp F
  have hto : hp.toLp F=F := Lp.ext hp.coeFn_toLp
  have hc := hp.condExpL2_ae_eq_condExp (𝕜 := ℂ) (augmented_joint_le s)
  rw [hto] at hc
  have hz : (condExpL2 ℂ ℂ (augmented_joint_le s) F : JointComplex)=0 :=
    Lp.ext (hc.trans (hF.trans (Lp.coeFn_zero ℂ 2 μ).symm))
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℂ) (augmented_joint_le s) F G hG
  rw [hz,inner_zero_left] at hi
  exact hi.symm

private theorem orthogonal_sum_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → JointComplex) (hF : ∀ i j,i≠j → inner ℂ (F i) (F j)=0) :
    ‖∑ i,F i‖^2=∑ i,‖F i‖^2 := by
  let : InnerProductSpace ℝ JointComplex := InnerProductSpace.rclikeToReal ℂ JointComplex
  rw [← real_inner_self_eq_norm_sq,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum,Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq (F i)
  · intro j _ hji
    change RCLike.re (inner ℂ (F i) (F j))=0
    rw [hF i j hji.symm]
    rfl
  · simp

/-- Adaptive stopping masks contract the total error of a chronological L2
martingale-difference family. Unconditional orthogonality alone is not assumed sufficient. -/
theorem mask_sum_contraction {n : ℕ} (grid : Fin (n+1) → ℝ≥0) (hg : Monotone grid)
    (F : Fin n → JointComplex)
    (hF : ∀ i,AEStronglyMeasurable[augmentedJoint (grid i.succ)] (F i) μ)
    (hCE : ∀ i,μ[F i | augmentedJoint (grid i.castSucc)] =ᵐ[μ] fun _ => (0:ℂ))
    (A : Fin n → Set Sample) (hA : ∀ i,MeasurableSet[augmentedJoint (grid i.castSucc)] (A i)) :
    ‖∑ i,masked (A i) (augmented_joint_le _ _ (hA i)) (F i)‖^2≤‖∑ i,F i‖^2 := by
  have horth (H : Fin n → JointComplex)
      (hH : ∀ i,AEStronglyMeasurable[augmentedJoint (grid i.succ)] (H i) μ)
      (hHC : ∀ i,μ[H i | augmentedJoint (grid i.castSucc)] =ᵐ[μ] fun _ => (0:ℂ)) :
      ∀ i j,i≠j → inner ℂ (H i) (H j)=0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · apply inner_eq_zero_symm.mpr
      apply inner_zero_of_condExp (grid j.castSucc) (H j) (H i) (hHC j)
      exact (hH i).mono (augmentedJoint.mono (hg (Fin.succ_le_castSucc_iff.mpr hlt)))
    · apply inner_zero_of_condExp (grid i.castSucc) (H i) (H j) (hHC i)
      exact (hH j).mono (augmentedJoint.mono (hg (Fin.succ_le_castSucc_iff.mpr hgt)))
  have hm (i : Fin n) := masked_past (grid i.castSucc) (grid i.succ)
    (hg (Fin.castSucc_le_succ i)) (A i) (hA i) (F i) (hF i)
  have hc (i : Fin n) := masked_condExp_zero (grid i.castSucc) (A i) (hA i) (F i) (hCE i)
  rw [orthogonal_sum_norm_sq _ (horth _ hm hc),orthogonal_sum_norm_sq _ (horth F hF hCE)]
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) (masked_norm_le (A i) _ (F i)) 2

open GaussianBrownianQuadraticVariation

def gridError (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) (i : Fin (n+1)) : JointComplex :=
  cellError (uniformTime T n i.castSucc) (uniformTime T n i.succ)
    (uniformTime_monotone T n (Fin.castSucc_le_succ i)) p

def errorSum (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) : JointComplex := ∑ i,gridError T p n i

variable (τ : Sample → ℝ≥0) (hτ : IsStoppingTime augmentedJoint (fun w => (τ w:WithTop ℝ≥0)))
include hτ in
private theorem survival_measurable (s : ℝ≥0) : MeasurableSet[augmentedJoint s] {w | s<τ w} := by
  simpa only [WithTop.coe_lt_coe] using hτ.measurableSet_gt s

def stoppedErrorSum (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) : JointComplex :=
  ∑ i : Fin (n+1),masked {w | uniformTime T n i.castSucc<τ w}
    (augmented_joint_le _ _ (survival_measurable τ hτ (uniformTime T n i.castSucc))) (gridError T p n i)

theorem stopped_error_contraction (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) :
    ‖stoppedErrorSum τ hτ T p n‖^2≤‖errorSum T p n‖^2 := by
  apply mask_sum_contraction (uniformTime T n) (uniformTime_monotone T n) (gridError T p n)
  · intro i
    exact cellError_past _ _ _ p
  · intro i
    exact cellError_condExp _ _ _ p
  · intro i
    exact survival_measurable τ hτ (uniformTime T n i.castSucc)

private theorem sum_complex_differences {m : ℕ} (a : Fin (m+1) → ℂ) :
    (∑ i : Fin m,(a i.succ-a i.castSucc))=a (Fin.last m)-a 0 := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ a
  have h2 := Fin.sum_univ_castSucc a
  linear_combination h2-h1

theorem errorSum_actual (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) :
    errorSum T p n =ᵐ[μ] fun w => p.eval (value T w)-p.eval 0-
      StochasticCauchyContinuousPolynomials.riemannSum T p n w := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (gridError T p n),
    ae_all_iff.mpr (fun i : Fin (n+1) => cellError_actual (uniformTime T n i.castSucc)
      (uniformTime T n i.succ) (uniformTime_monotone T n (Fin.castSucc_le_succ i)) p),value_zero_ae]
    with w hs he h0
  simp only [Finset.sum_apply] at hs
  change errorSum T p n w=∑ i : Fin (n+1),gridError T p n i w at hs
  rw [hs]
  have hh : (∑ i : Fin (n+1),gridError T p n i w)=
      (∑ i : Fin (n+1),(p.eval (value (uniformTime T n i.succ) w)-
        p.eval (value (uniformTime T n i.castSucc) w)))-
      StochasticCauchyContinuousPolynomials.riemannSum T p n w := by
    rw [StochasticCauchyContinuousPolynomials.riemannSum,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => he i
  have htel := sum_complex_differences (fun j : Fin (n+2) => p.eval (value (uniformTime T n j) w))
  simp only [(uniformTime_endpoints T n).1,(uniformTime_endpoints T n).2,h0] at htel
  rw [hh,htel]

theorem errorSum_norm_sq (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) :
    ‖errorSum T p n‖^2=∫ w,‖StochasticCauchyContinuousPolynomials.riemannSum T p n w-
      (p.eval (value T w)-p.eval 0)‖^2 ∂μ := by
  rw [BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [errorSum_actual T p n] with w hw
  rw [hw,norm_sub_rev]

theorem errorSum_norm_sq_tendsto (T : ℝ≥0) (p : Polynomial ℂ) :
    Tendsto (fun n => ‖errorSum T p n‖^2) atTop (𝓝 0) := by
  simpa only [errorSum_norm_sq] using StochasticCauchyContinuousPolynomials.mean_square_reconstruction T p

/-- ALL polynomial degrees inherit strong stopped remainder convergence from
the existing unweighted reconstruction, by conditional masking contraction. -/
theorem stopped_error_norm_sq_tendsto (T : ℝ≥0) (p : Polynomial ℂ) :
    Tendsto (fun n => ‖stoppedErrorSum τ hτ T p n‖^2) atTop (𝓝 0) :=
  squeeze_zero (fun _ => sq_nonneg _) (stopped_error_contraction τ hτ T p) (errorSum_norm_sq_tendsto T p)

def chronologicalRemainder (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) (w : Sample) : ℂ :=
  ∑ i : Fin (n+1),if uniformTime T n i.castSucc<τ w then
    p.eval (value (uniformTime T n i.succ) w)-p.eval (value (uniformTime T n i.castSucc) w)-
      p.derivative.eval (value (uniformTime T n i.castSucc) w)*
        (value (uniformTime T n i.succ) w-value (uniformTime T n i.castSucc) w) else 0

theorem stoppedErrorSum_actual (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) :
    stoppedErrorSum τ hτ T p n =ᵐ[μ] chronologicalRemainder τ T p n := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (n+1) =>
      masked {w | uniformTime T n i.castSucc<τ w}
        (augmented_joint_le _ _ (survival_measurable τ hτ (uniformTime T n i.castSucc))) (gridError T p n i)),
    ae_all_iff.mpr (fun i : Fin (n+1) => masked_actual {w | uniformTime T n i.castSucc<τ w}
      (augmented_joint_le _ _ (survival_measurable τ hτ (uniformTime T n i.castSucc))) (gridError T p n i)),
    ae_all_iff.mpr (fun i : Fin (n+1) => cellError_actual (uniformTime T n i.castSucc)
      (uniformTime T n i.succ) (uniformTime_monotone T n (Fin.castSucc_le_succ i)) p)] with w hs hm he
  change stoppedErrorSum τ hτ T p n w=_ at hs
  rw [hs]
  simp only [Finset.sum_apply,chronologicalRemainder]
  apply Finset.sum_congr rfl
  intro i _
  rw [hm i]
  by_cases hw : uniformTime T n i.castSucc<τ w
  · simp only [indicator_of_mem (show w∈{w | uniformTime T n i.castSucc<τ w} from hw),hw,ite_true]
    exact he i
  · simp only [indicator_of_notMem (show w∉{w | uniformTime T n i.castSucc<τ w} from hw),hw,ite_false]

include hτ in
theorem chronologicalRemainder_memLp (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) :
    MemLp (chronologicalRemainder τ T p n) 2 μ :=
  (Lp.memLp (stoppedErrorSum τ hτ T p n)).ae_eq (stoppedErrorSum_actual τ hτ T p n)

/- Actual source mean-square stopped Taylor remainder tends to0. The stopped Ito formula is not assumed. -/
include hτ in
theorem chronologicalRemainder_mean_square (T : ℝ≥0) (p : Polynomial ℂ) :
    Tendsto (fun n => ∫ w,‖chronologicalRemainder τ T p n w‖^2 ∂μ) atTop (𝓝 0) := by
  have he (n : ℕ) : ‖stoppedErrorSum τ hτ T p n‖^2=∫ w,‖chronologicalRemainder τ T p n w‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [stoppedErrorSum_actual τ hτ T p n] with w hw
    change ‖stoppedErrorSum τ hτ T p n w‖^2=‖chronologicalRemainder τ T p n w‖^2
    rw [hw]
  simpa only [he] using stopped_error_norm_sq_tendsto τ hτ T p

/-- Finite four-atom averages: centered, unconditionally orthogonal errors
can grow after an inadmissible mask. Conditional past hypotheses are essential. -/
theorem unconditional_mask_counterexample : ∃ F G : Fin 4 → ℝ,∃ A : Set (Fin 4),
    (∑ i,F i)=0 ∧ (∑ i,G i)=0 ∧ (∑ i,F i*G i)=0 ∧
      (∑ i,(F i+A.indicator G i)^2)/4>(∑ i,(F i+G i)^2)/4 := by
  classical
  refine ⟨(fun i => if i.val<2 then 1 else -1),
    (fun i => if i.val%2=0 then 1 else -1),{0,3},?_⟩
  norm_num [Fin.sum_univ_succ,Set.indicator]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedErrors
