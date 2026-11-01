import Foundation.StochasticCauchyGaussianStein
import Foundation.StochasticCauchyExponentialPrediction
import Foundation.IndependentInnovationConditioning
import Foundation.ProductSourceShuffle
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-! Actual full-joint-past polynomial prediction via independent Gaussian
innovations, the existing product-source shuffle and native conditioning.
Chronological native-input identification remains a separate obligation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomialPrediction
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeDivergence
open StochasticCauchyGaussianStein StochasticCauchyPastReconstruction
attribute [local instance] timeHilbert_secondCountable

def timeDirection (t : ℝ≥0) : CoefficientSpace :=
  SeparableHilbertEmbedding.hilbertEmbedding TimeHilbert (timeVector t)

def past (S : ℝ≥0) (w : SampleSpace) : Iic S → ℝ := fun r => process r w

def fresh (S T : ℝ≥0) (w : SampleSpace) : ℝ :=
  firstChaosEmbedding (incrementDirection S T) w

theorem past_measurable (S : ℝ≥0) : Measurable (past S) :=
  measurable_pi_iff.mpr (fun r => (process_stronglyMeasurable r).measurable)

theorem fresh_measurable (S T : ℝ≥0) : Measurable (fresh S T) :=
  (Lp.stronglyMeasurable (firstChaosEmbedding (incrementDirection S T))).measurable

theorem fresh_independent_past (S T : ℝ≥0) (hST : S ≤ T) :
    IndepFun (past S) (fresh S T) gaussianProduct := by
  let features : Iic S ⊕ Unit → CoefficientSpace :=
    Sum.elim (fun r => timeDirection r) (fun _ => incrementDirection S T)
  have hG : IsGaussianProcess
      (Sum.elim (fun r : Iic S => process r) (fun _ : Unit => fresh S T)) gaussianProduct := by
    convert firstChaos_isGaussianProcess.comp_right features using 1
    funext i
    cases i <;> rfl
  have hi := hG.indepFun_of_covariance_eq_zero
    (fun r => (process_stronglyMeasurable r).measurable.aemeasurable)
    (fun _ => (fresh_measurable S T).aemeasurable) (fun r _ => ?_)
  · have hh := hi.comp measurable_id (measurable_pi_apply ())
    exact hh
  · change cov[firstChaosEmbedding (timeDirection r),
      firstChaosEmbedding (incrementDirection S T); gaussianProduct] = 0
    rw [firstChaos_covariance]
    exact pastDirection_inner_increment r S T r.property hST

private theorem paired_independent {P : Type*} [MeasurableSpace P]
    (A : SampleSpace → P) (B : SampleSpace → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hi : IndepFun A B gaussianProduct) :
    IndepFun (fun w : SampleSpace × SampleSpace => (A w.1,A w.2))
      (fun w => (B w.1,B w.2)) (gaussianProduct.prod gaussianProduct) := by
  let a := gaussianProduct.map A
  let b := gaussianProduct.map B
  have hm : MeasurePreserving (fun w => (A w,B w)) gaussianProduct (a.prod b) :=
    ⟨hA.prodMk hB,hi.map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable⟩
  have hs := ((ProductSourceShuffle.preserving a b a b).comp (hm.prod hm)).map_eq
  have hp : (gaussianProduct.prod gaussianProduct).map
      (fun w : SampleSpace × SampleSpace => (A w.1,A w.2)) = a.prod a :=
    (Measure.map_prod_map gaussianProduct gaussianProduct hA hA).symm
  have hf : (gaussianProduct.prod gaussianProduct).map
      (fun w : SampleSpace × SampleSpace => (B w.1,B w.2)) = b.prod b :=
    (Measure.map_prod_map gaussianProduct gaussianProduct hB hB).symm
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mpr
  rw [hp,hf]
  exact hs

def jointPastMap (S : ℝ≥0) (w : SampleSpace × SampleSpace) : (Iic S → ℝ) × (Iic S → ℝ) :=
  (past S w.1,past S w.2)

def innovation (S T : ℝ≥0) (w : SampleSpace × SampleSpace) : ℂ :=
  (fresh S T w.1 : ℂ) + Complex.I * (fresh S T w.2 : ℂ)

theorem jointPastMap_measurable (S : ℝ≥0) : Measurable (jointPastMap S) :=
  ((past_measurable S).comp measurable_fst).prodMk ((past_measurable S).comp measurable_snd)

theorem innovation_measurable (S T : ℝ≥0) : Measurable (innovation S T) := by
  have hf := fresh_measurable S T
  unfold innovation
  fun_prop

theorem innovation_independent_past (S T : ℝ≥0) (hST : S ≤ T) :
    IndepFun (jointPastMap S) (innovation S T) (gaussianProduct.prod gaussianProduct) := by
  have hi := paired_independent (past S) (fresh S T) (past_measurable S)
    (fresh_measurable S T) (fresh_independent_past S T hST)
  exact hi.comp measurable_id (by fun_prop : Measurable (fun q : ℝ × ℝ =>
    (q.1 : ℂ)+Complex.I*(q.2 : ℂ)))

theorem jointPastMap_sigma (S : ℝ≥0) :
    MeasurableSpace.comap (jointPastMap S) inferInstance = jointPast S := by
  change MeasurableSpace.comap (Prod.map (past S) (past S)) inferInstance =
    (naturalFiltration S).prod (naturalFiltration S)
  change MeasurableSpace.comap (Prod.map (past S) (past S))
    ((inferInstance : MeasurableSpace (Iic S → ℝ)).prod inferInstance) = _
  rw [MeasurableSpace.comap_prodMap]
  simp only [naturalFiltration,Filtration.natural_eq_comap]
  rfl

theorem shifted_polynomial_memLp (h : CoefficientSpace) (p : Polynomial ℂ) (z : ℂ) :
    MemLp (fun w => p.eval (z+zValue h w)) 2 (gaussianProduct.prod gaussianProduct) := by
  have hh := StochasticCauchyPolynomials.polynomial_memLp h
    (p.comp (Polynomial.C z+Polynomial.X))
  simp only [Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X] at hh
  exact hh

theorem shifted_polynomial_mean (h : CoefficientSpace) (p : Polynomial ℂ) (z : ℂ) :
    (∫ w, p.eval (z+zValue h w) ∂gaussianProduct.prod gaussianProduct) = p.eval z := by
  have hh := polynomial_mean h (p.comp (Polynomial.C z+Polynomial.X))
  simp only [Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,add_zero] at hh
  exact hh

def position (T : ℝ≥0) (w : SampleSpace × SampleSpace) : ℂ :=
  (process T w.1 : ℂ)+Complex.I*(process T w.2 : ℂ)

theorem position_eq (T : ℝ≥0) : position T = zValue (timeDirection T) := rfl

def current (S : ℝ≥0) (q : (Iic S → ℝ) × (Iic S → ℝ)) : ℂ :=
  (q.1 ⟨S,by simp⟩ : ℂ)+Complex.I*(q.2 ⟨S,by simp⟩ : ℂ)

theorem current_measurable (S : ℝ≥0) : Measurable (current S) := by
  unfold current
  fun_prop

theorem current_past (S : ℝ≥0) (w : SampleSpace × SampleSpace) :
    current S (jointPastMap S w) = position S w := rfl

theorem innovation_position (S T : ℝ≥0) (hST : S ≤ T) :
    (fun w => current S (jointPastMap S w)+innovation S T w)
      =ᵐ[gaussianProduct.prod gaussianProduct] position T := by
  have hf : fresh S T =ᵐ[gaussianProduct] fun w => process T w-process S w :=
    process_increment_ae S T hST
  have hx := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp hf
  have hy := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp hf
  filter_upwards [hx,hy] with w hx hy
  change fresh S T w.1 = process T w.1-process S w.1 at hx
  change fresh S T w.2 = process T w.2-process S w.2 at hy
  rw [current_past]
  simp only [position,innovation,hx,hy,Complex.ofReal_sub]
  ring

theorem conditional_polynomial (S T : ℝ≥0) (hST : S ≤ T) (p : Polynomial ℂ) :
    (gaussianProduct.prod gaussianProduct)[(fun w => p.eval (position T w)) | jointPast S]
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w => p.eval (position S w) := by
  let μ := gaussianProduct.prod gaussianProduct
  let F : (((Iic S → ℝ) × (Iic S → ℝ)) × ℂ) → ℂ :=
    fun q => p.eval (current S q.1+q.2)
  have hF : Measurable F := by
    have hc := current_measurable S
    dsimp only [F]
    fun_prop
  have he : (fun w => F (jointPastMap S w,innovation S T w))
      =ᵐ[μ] fun w => p.eval (position T w) :=
    (innovation_position S T hST).mono (fun w hw => congrArg (fun z => p.eval z) hw)
  have hi : Integrable (fun w => p.eval (position T w)) μ := by
    rw [position_eq]
    exact (StochasticCauchyPolynomials.polynomial_memLp (timeDirection T) p).integrable
      (by norm_num)
  have hiF : Integrable (fun w => F (jointPastMap S w,innovation S T w)) μ :=
    hi.congr he.symm
  have hcond := IndependentInnovationConditioning.conditional_integral μ
    (jointPastMap S) (innovation S T) (jointPastMap_measurable S)
    (innovation_measurable S T) (innovation_independent_past S T hST) F
    hF.stronglyMeasurable hiF
  rw [jointPastMap_sigma] at hcond
  have hm (q : (Iic S → ℝ) × (Iic S → ℝ)) :
      (∫ y, F (q,y) ∂μ.map (innovation S T)) = p.eval (current S q) := by
    have hfm : AEStronglyMeasurable (fun y : ℂ => F (q,y)) (μ.map (innovation S T)) :=
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have hmap := integral_map (innovation_measurable S T).aemeasurable hfm
    exact hmap.trans (shifted_polynomial_mean (incrementDirection S T) p (current S q))
  have hce := condExp_congr_ae (m := jointPast S) he
  refine hce.symm.trans (hcond.trans ?_)
  exact Filter.Eventually.of_forall (fun w => by
    change (∫ y, F (jointPastMap S w,y) ∂μ.map (innovation S T)) = p.eval (position S w)
    rw [hm,current_past])

theorem position_stronglyMeasurable (T : ℝ≥0) :
    StronglyMeasurable[jointPast T] (position T) := by
  have hs := process_stronglyAdapted T
  have hx : StronglyMeasurable[jointPast T]
      (fun w : SampleSpace × SampleSpace => process T w.1) :=
    hs.comp_measurable (show @Measurable (SampleSpace × SampleSpace) SampleSpace
      (jointPast T) (naturalFiltration T) Prod.fst from measurable_fst)
  have hy : StronglyMeasurable[jointPast T]
      (fun w : SampleSpace × SampleSpace => process T w.2) :=
    hs.comp_measurable (show @Measurable (SampleSpace × SampleSpace) SampleSpace
      (jointPast T) (naturalFiltration T) Prod.snd from measurable_snd)
  exact (Complex.continuous_ofReal.comp_stronglyMeasurable hx).add
    (stronglyMeasurable_const.mul (Complex.continuous_ofReal.comp_stronglyMeasurable hy))

theorem polynomial_position_memLp (T : ℝ≥0) (p : Polynomial ℂ) :
    MemLp (fun w => p.eval (position T w)) 2 (gaussianProduct.prod gaussianProduct) := by
  rw [position_eq]
  exact StochasticCauchyPolynomials.polynomial_memLp (timeDirection T) p

/-- The actual raw full-joint-past martingale predicate, for all polynomials. -/
theorem polynomial_martingale (p : Polynomial ℂ) :
    Martingale (fun T w => p.eval (position T w))
      StochasticCauchyExponentialPrediction.jointFiltration (gaussianProduct.prod gaussianProduct) := by
  refine ⟨?_,fun S T hST => conditional_polynomial S T hST p⟩
  intro T
  have hc : Continuous (fun z : ℂ => p.eval z) := by fun_prop
  exact hc.comp_stronglyMeasurable (position_stronglyMeasurable T)

/-- The already constructed original polynomial class, with time specialized. -/
def polynomialClass (T : ℝ≥0) (p : Polynomial ℂ) : StochasticCauchyComplexChannels.JointComplex :=
  StochasticCauchyPolynomials.polynomialValue (timeDirection T) p

theorem polynomialClass_ae (T : ℝ≥0) (p : Polynomial ℂ) :
    polynomialClass T p =ᵐ[gaussianProduct.prod gaussianProduct] fun w => p.eval (position T w) :=
  StochasticCauchyPolynomials.polynomial_value_ae (timeDirection T) p

/-- Actual bounded conditional projection on the existing L2 classes. -/
theorem polynomialClass_prediction (S T : ℝ≥0) (hST : S ≤ T) (p : Polynomial ℂ) :
    (condExpL2 ℂ ℂ (jointPast_le S) (polynomialClass T p) :
      StochasticCauchyComplexChannels.JointComplex) = polynomialClass S p := by
  have hp := polynomial_position_memLp T p
  have hto : hp.toLp (fun w => p.eval (position T w)) = polynomialClass T p :=
    Lp.ext (hp.coeFn_toLp.trans (polynomialClass_ae T p).symm)
  apply Lp.ext
  have hc := hp.condExpL2_ae_eq_condExp (𝕜 := ℂ) (jointPast_le S)
  rw [hto] at hc
  exact hc.trans ((conditional_polynomial S T hST p).trans (polynomialClass_ae S p).symm)

/-- Orthogonality against EVERY actual full-joint-past L2 test observable. -/
theorem polynomial_innovation_pairing (S T : ℝ≥0) (hST : S ≤ T) (p : Polynomial ℂ)
    (H : StochasticCauchyComplexChannels.JointComplex)
    (hH : AEStronglyMeasurable[jointPast S] H (gaussianProduct.prod gaussianProduct)) :
    inner ℂ (polynomialClass T p-polynomialClass S p) H = 0 := by
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℂ) (jointPast_le S) (polynomialClass T p) H hH
  rw [polynomialClass_prediction S T hST p] at hi
  rw [inner_sub_left,← hi,sub_self]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomialPrediction
