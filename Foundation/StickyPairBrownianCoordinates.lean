import Foundation.StickyPairFiniteIncrementFourier
import Mathlib.Algebra.BigOperators.Pi

/-! Genuine Brownian coordinate processes for the constructed sticky two-point coupling. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyPairBrownianCoordinates
open InfiniteGaussian IBMConstructedSources StickyPairPaths StickyPairMarginals
open BrownianFiniteIncrementFourier StickyPairFiniteIncrementFourier IBMOneTimeFourier
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem map_fin_eq_of_fourier {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ)
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ p : Fin n → ℝ, (∫ w, ∏ i, observable (p i) (X w i) ∂μ)=
      ∫ w, ∏ i, observable (p i) (Y w i) ∂ν) : μ.map X=ν.map Y := by
  classical
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply,charFunDual_apply,
    integral_map hX.aemeasurable (by fun_prop),integral_map hY.aemeasurable (by fun_prop)]
  have hL (x : Fin n → ℝ) : L x=∑ i, L (Pi.single i 1)*x i := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul]
    simp only [smul_eq_mul]
    ring
  have he (x : Fin n → ℝ) : Complex.exp ((L x:ℂ)*Complex.I)=
      ∏ i, observable (L (Pi.single i 1)) (x i) := by
    rw [hL]
    simp only [observable]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  simp_rw [he]
  exact h (fun i => L (Pi.single i 1))

theorem half_increment_law (κ : ℝ≥0) (times : ℕ → ℝ≥0) (ht : Monotone times)
    (n : ℕ) (a b : ℝ) (ha : a^2=1/2) (hb : b^2=1/2) :
    HasLaw (fun w => fun i : Fin n => linearValue κ (times (i+1)) a b w-
      linearValue κ (times i) a b w)
      (gaussianProduct.map (fun w => fun i : Fin n =>
        clockPath w (times (i+1))-clockPath w (times i))) sourceMeasure := by
  have hm : Measurable (fun w => fun i : Fin n => linearValue κ (times (i+1)) a b w-
      linearValue κ (times i) a b w) :=
    Measurable.of_eval (fun i => (linear_measurable κ _ a b).sub (linear_measurable κ _ a b))
  have hmB : Measurable (fun w => fun i : Fin n => clockPath w (times (i+1))-
      clockPath w (times i)) := Measurable.of_eval fun i =>
    ((ContinuousMap.measurable_eval _).comp clockPath_measurable).sub
      ((ContinuousMap.measurable_eval _).comp clockPath_measurable)
  refine ⟨hm.aemeasurable,?_⟩
  apply map_fin_eq_of_fourier sourceMeasure gaussianProduct n _ _ hm hmB
  intro p
  let u (k : ℕ) : ℝ := if hk : k < n then p ⟨k,hk⟩ else 0
  have hf := half_matches_source κ times ht u n a b ha hb
  have hf' : (∫ w, ∏ i : Fin n, observable (u i)
      (linearValue κ (times (i+1)) a b w-linearValue κ (times i) a b w) ∂sourceMeasure)=
      ∫ w, ∏ i : Fin n, observable (u i)
        (clockPath w (times (i+1))-clockPath w (times i)) ∂gaussianProduct := by
    simpa only [← Fin.prod_univ_eq_prod_range,incrementProduct] using hf
  simpa [u] using hf'

theorem independence_of_vector_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (he : μ.map X=ν.map Y)
    (hi : iIndepFun (fun i w => Y w i) ν) : iIndepFun (fun i w => X w i) μ := by
  have hmX (i : Fin n) := (measurable_pi_apply i).comp hX
  have hmY (i : Fin n) := (measurable_pi_apply i).comp hY
  have hm (i : Fin n) : μ.map (fun w => X w i)=ν.map (fun w => Y w i) := by
    have h := congrArg (fun m : Measure (Fin n → ℝ) => m.map (fun x => x i)) he
    rw [Measure.map_map (measurable_pi_apply i) hX,
      Measure.map_map (measurable_pi_apply i) hY] at h
    exact h
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hmX i).aemeasurable)).2
  change μ.map X=Measure.pi (fun i => μ.map (fun w => X w i))
  have hi' := hi.map_fun_eq_pi_map (fun i => (hmY i).aemeasurable)
  change ν.map Y=Measure.pi (fun i => ν.map (fun w => Y w i)) at hi'
  rw [he,hi']
  congr 1
  funext i
  exact (hm i).symm

theorem half_prefix_independent (κ : ℝ≥0) (times : ℕ → ℝ≥0) (ht : Monotone times)
    (n : ℕ) (a b : ℝ) (ha : a^2=1/2) (hb : b^2=1/2) :
    iIndepFun (fun i : Fin n => fun w => linearValue κ (times (i+1)) a b w-
      linearValue κ (times i) a b w) sourceMeasure := by
  have hl := half_increment_law κ times ht n a b ha hb
  apply independence_of_vector_law sourceMeasure gaussianProduct n _ _
    (Measurable.of_eval fun i => (linear_measurable κ _ a b).sub (linear_measurable κ _ a b))
    (Measurable.of_eval fun i =>
      ((ContinuousMap.measurable_eval _).comp clockPath_measurable).sub
        ((ContinuousMap.measurable_eval _).comp clockPath_measurable)) hl.map_eq
  exact (clock_isBrownian.toIsPreBrownianReal.hasIndepIncrements.nat ht).precomp Fin.val_injective

theorem half_hasIndepIncrements (κ : ℝ≥0) (a b : ℝ) (ha : a^2=1/2) (hb : b^2=1/2) :
    HasIndepIncrements (fun r w => linearValue κ r a b w) sourceMeasure := by
  intro n times ht
  let times' (k : ℕ) : ℝ≥0 := times ⟨min n k,Nat.lt_succ_of_le (Nat.min_le_left n k)⟩
  have hmono : Monotone times' := by
    intro i j hij
    apply ht
    exact min_le_min_left n hij
  have hi := half_prefix_independent κ times' hmono n a b ha hb
  have he : (fun i : Fin n => fun w => linearValue κ (times' (i+1)) a b w-
      linearValue κ (times' i) a b w)=
      (fun i : Fin n => fun w => linearValue κ (times i.succ) a b w-
        linearValue κ (times i.castSucc) a b w) := by
    funext i w
    have h0 : (i:ℕ) ≤ n := Nat.le_of_lt i.isLt
    have h1 : (i:ℕ)+1 ≤ n := i.isLt
    change linearValue κ (times ⟨min n ((i:ℕ)+1),_⟩) a b w-
      linearValue κ (times ⟨min n (i:ℕ),_⟩) a b w=_
    simp only [Nat.min_eq_right h0,Nat.min_eq_right h1]
    rfl
  rw [he] at hi
  exact hi

theorem half_isBrownian (κ : ℝ≥0) (a b : ℝ) (ha : a^2=1/2) (hb : b^2=1/2) :
    IsBrownianReal (fun r w => linearValue κ r a b w) sourceMeasure where
  toIsPreBrownianReal := (half_hasIndepIncrements κ a b ha hb).isPreBrownianReal_of_hasLaw
    (fun r => half_law κ r a b ha hb)
  cont := Eventually.of_forall fun w =>
    ((centerPath κ w).continuous.const_mul a).add ((separationPath κ w).continuous.const_mul b)

theorem left_isBrownian (κ : ℝ≥0) :
    IsBrownianReal (fun r w => leftPath κ w r) sourceMeasure := by
  have he : (fun r w => leftPath κ w r)=
      (fun r w => linearValue κ r (1/Real.sqrt 2) (1/Real.sqrt 2) w) := by
    funext r w
    dsimp [leftPath,linearValue]
    ring
  rw [he]
  exact half_isBrownian κ _ _ reciprocal_sqrt_square reciprocal_sqrt_square

theorem right_isBrownian (κ : ℝ≥0) :
    IsBrownianReal (fun r w => rightPath κ w r) sourceMeasure := by
  have hb : (-1/Real.sqrt (2:ℝ))^2=1/2 := by
    rw [neg_div,neg_sq]
    exact reciprocal_sqrt_square
  have he : (fun r w => rightPath κ w r)=
      (fun r w => linearValue κ r (1/Real.sqrt 2) (-1/Real.sqrt 2) w) := by
    funext r w
    dsimp [rightPath,linearValue]
    ring
  rw [he]
  exact half_isBrownian κ _ _ reciprocal_sqrt_square hb

end OperatorDerivativeRewrite.Foundation.StickyPairBrownianCoordinates
