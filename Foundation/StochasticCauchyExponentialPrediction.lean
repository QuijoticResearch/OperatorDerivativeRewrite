import Foundation.StochasticCauchyExponential
import Foundation.GaussianBrownianConditionalTransition

/-! Conditional prediction of the actual exponential on the full joint past.
This does not identify its native temporal integrand. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyExponentialPrediction
open InfiniteGaussian GaussianTimeProcess StochasticCauchyPastReconstruction
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

theorem scalar_exponential_integrable (v : ℝ≥0) (c : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (c*(x:ℂ))) (gaussianReal 0 v) := by
  apply (integrable_exp_mul_gaussianReal (μ := 0) (v := v) c.re).mono' (by fun_prop)
  apply Eventually.of_forall
  intro x
  simp [Complex.norm_exp,Complex.mul_re]

theorem scalar_process_exponential_integrable (T : ℝ≥0) (c : ℂ) :
    Integrable (fun w => Complex.exp (c*(process T w:ℂ))) gaussianProduct :=
  (process_hasLaw T).integrable_comp (scalar_exponential_integrable T c)

/-- The entire raw history is retained; the Gaussian drift factor is explicit. -/
theorem scalar_conditional_exponential (S T : ℝ≥0) (hST : S ≤ T) (c : ℂ) :
    gaussianProduct[(fun w => Complex.exp (c*(process T w:ℂ))) | naturalFiltration S]
      =ᵐ[gaussianProduct] fun w => Complex.exp (c*(process S w:ℂ))*
        Complex.exp (((T-S:ℝ≥0):ℂ)*c^2/2) := by
  have hc := GaussianBrownianConditionalTransition.conditional_transition S T hST
    (fun x : ℝ => Complex.exp (c*(x:ℂ))) (by fun_prop)
    (scalar_process_exponential_integrable T c)
  refine hc.trans (Eventually.of_forall fun w => ?_)
  simp only [Complex.ofReal_add,mul_add,Complex.exp_add,integral_const_mul]
  congr 1
  simpa only [complexMGF,id_eq,Complex.ofReal_zero,mul_zero,zero_add] using
    (complexMGF_id_gaussianReal (μ := 0) (v := T-S) c)

/-- Independent-coordinate conditioning on the product of the two actual pasts.
Both candidates have their own past measurability and integrability checked. -/
theorem conditional_product (S : ℝ≥0) (f g u v : SampleSpace → ℂ)
    (hf : Integrable f gaussianProduct) (hg : Integrable g gaussianProduct)
    (hu : Integrable u gaussianProduct) (hv : Integrable v gaussianProduct)
    (hum : StronglyMeasurable[naturalFiltration S] u)
    (hvm : StronglyMeasurable[naturalFiltration S] v)
    (hfu : gaussianProduct[f | naturalFiltration S] =ᵐ[gaussianProduct] u)
    (hgv : gaussianProduct[g | naturalFiltration S] =ᵐ[gaussianProduct] v) :
    (gaussianProduct.prod gaussianProduct)[(fun w => f w.1*g w.2) | jointPast S]
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w => u w.1*v w.2 := by
  let μ := gaussianProduct.prod gaussianProduct
  have hi : Integrable (fun w : SampleSpace × SampleSpace =>
      f w.1*g w.2-u w.1*v w.2) μ := (hf.mul_prod hg).sub (hu.mul_prod hv)
  have hb (A B : Set SampleSpace) (hA : MeasurableSet[naturalFiltration S] A)
      (hB : MeasurableSet[naturalFiltration S] B) :
      (∫ w in A ×ˢ B, f w.1*g w.2-u w.1*v w.2 ∂μ)=0 := by
    have h1 := setIntegral_condExp (naturalFiltration.le S) hf hA
    have h2 := setIntegral_condExp (naturalFiltration.le S) hg hB
    rw [integral_congr_ae (ae_restrict_of_ae hfu)] at h1
    rw [integral_congr_ae (ae_restrict_of_ae hgv)] at h2
    rw [integral_sub (hf.mul_prod hg).integrableOn (hu.mul_prod hv).integrableOn,
      setIntegral_prod_mul,setIntegral_prod_mul,h1,h2,sub_self]
  have hu0 : (∫ w : SampleSpace × SampleSpace,
      f w.1*g w.2-u w.1*v w.2 ∂μ)=0 := by
    simpa only [univ_prod_univ,setIntegral_univ] using
      hb univ univ MeasurableSet.univ MeasurableSet.univ
  have hall : ∀ A : Set (SampleSpace × SampleSpace), MeasurableSet[jointPast S] A →
      (∫ w in A, f w.1*g w.2-u w.1*v w.2 ∂μ)=0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => (∫ w in A, f w.1*g w.2-u w.1*v w.2 ∂μ)=0)
      (@generateFrom_prod SampleSpace SampleSpace (naturalFiltration S)
        (naturalFiltration S)).symm
      (@isPiSystem_prod SampleSpace SampleSpace (naturalFiltration S)
        (naturalFiltration S)) (by simp) ?_ ?_ ?_
    · rintro A ⟨B,hB,C,hC,rfl⟩
      exact hb B C hB hC
    · intro A hA hz
      rw [setIntegral_compl (jointPast_le S A hA) hi,hu0,hz,sub_self]
    · intro A hd hm hz
      rw [integral_iUnion (fun n => jointPast_le S _ (hm n)) hd hi.integrableOn]
      simp only [hz,tsum_zero]
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (jointPast_le S) (hf.mul_prod hg)
    (fun _ _ _ => (hu.mul_prod hv).integrableOn)
  · intro A hA _
    have h := hall A hA
    rw [integral_sub (hf.mul_prod hg).integrableOn (hu.mul_prod hv).integrableOn] at h
    exact (sub_eq_zero.mp h).symm
  · exact ((hum.comp_measurable
      (show @Measurable (SampleSpace × SampleSpace) SampleSpace
        (jointPast S) (naturalFiltration S) Prod.fst from measurable_fst)).mul
      (hvm.comp_measurable
      (show @Measurable (SampleSpace × SampleSpace) SampleSpace
        (jointPast S) (naturalFiltration S) Prod.snd from measurable_snd))).aestronglyMeasurable

def value (T : ℝ≥0) (w : SampleSpace × SampleSpace) : ℂ :=
  Complex.exp ((process T w.1:ℂ)+Complex.I*(process T w.2:ℂ))

theorem value_memLp (T : ℝ≥0) : MemLp (value T) 2
    (gaussianProduct.prod gaussianProduct) :=
  StochasticCauchyExponential.exponential_memLp
    (SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector T))

/-- Actual exponential prediction on the ENTIRE independent joint Brownian past.
The two scalar Gaussian drift factors cancel, with no boundedness assumption. -/
theorem conditional_value (S T : ℝ≥0) (hST : S ≤ T) :
    (gaussianProduct.prod gaussianProduct)[value T | jointPast S]
      =ᵐ[gaussianProduct.prod gaussianProduct] value S := by
  let d : ℂ := ((T-S:ℝ≥0):ℂ)/2
  let u := fun w => Complex.exp (process S w:ℂ)*Complex.exp d
  let v := fun w => Complex.exp (Complex.I*(process S w:ℂ))*Complex.exp (-d)
  have hx := scalar_conditional_exponential S T hST 1
  have hy := scalar_conditional_exponential S T hST Complex.I
  have hs : StronglyMeasurable[naturalFiltration S] (process S) :=
    process_stronglyAdapted S
  have hu : Integrable u gaussianProduct := by
    simpa only [u,one_mul] using
      (scalar_process_exponential_integrable S 1).mul_const (Complex.exp d)
  have hv : Integrable v gaussianProduct :=
    (scalar_process_exponential_integrable S Complex.I).mul_const (Complex.exp (-d))
  have hum : StronglyMeasurable[naturalFiltration S] u := by
    exact ((Complex.continuous_exp.stronglyMeasurable.comp_measurable
      (Complex.measurable_ofReal.comp hs.measurable)).mul stronglyMeasurable_const)
  have hvm : StronglyMeasurable[naturalFiltration S] v := by
    exact ((Complex.continuous_exp.stronglyMeasurable.comp_measurable
      (measurable_const.mul (Complex.measurable_ofReal.comp hs.measurable))).mul
        stronglyMeasurable_const)
  have hux : gaussianProduct[(fun w => Complex.exp (process T w:ℂ)) |
      naturalFiltration S] =ᵐ[gaussianProduct] u := by
    simpa only [u,d,one_mul,one_pow,mul_one] using hx
  have hvy : gaussianProduct[(fun w => Complex.exp (Complex.I*(process T w:ℂ))) |
      naturalFiltration S] =ᵐ[gaussianProduct] v := by
    simpa only [v,d,Complex.I_sq,mul_neg_one,neg_div] using hy
  have hc := conditional_product S _ _ u v
    (by simpa only [one_mul] using scalar_process_exponential_integrable T 1)
    (scalar_process_exponential_integrable T Complex.I) hu hv hum hvm hux hvy
  have he : (fun w : SampleSpace × SampleSpace =>
      Complex.exp (process T w.1:ℂ)*Complex.exp (Complex.I*(process T w.2:ℂ)))=
        value T := by
    funext w
    exact (Complex.exp_add _ _).symm
  rw [he] at hc
  refine hc.trans (Eventually.of_forall fun w => ?_)
  change (Complex.exp (process S w.1:ℂ)*Complex.exp d)*
    (Complex.exp (Complex.I*(process S w.2:ℂ))*Complex.exp (-d))=value S w
  calc
    _ = (Complex.exp (process S w.1:ℂ)*Complex.exp (Complex.I*(process S w.2:ℂ)))*
      (Complex.exp d*Complex.exp (-d)) := by ring
    _ = value S w := by
      rw [← Complex.exp_add d (-d),add_neg_cancel,Complex.exp_zero,mul_one]
      exact (Complex.exp_add _ _).symm

theorem value_stronglyMeasurable (T : ℝ≥0) :
    StronglyMeasurable[jointPast T] (value T) := by
  have hs := process_stronglyAdapted T
  have hx : StronglyMeasurable[jointPast T]
      (fun w : SampleSpace × SampleSpace => process T w.1) :=
    hs.comp_measurable (show @Measurable (SampleSpace × SampleSpace) SampleSpace
      (jointPast T) (naturalFiltration T) Prod.fst from measurable_fst)
  have hy : StronglyMeasurable[jointPast T]
      (fun w : SampleSpace × SampleSpace => process T w.2) :=
    hs.comp_measurable (show @Measurable (SampleSpace × SampleSpace) SampleSpace
      (jointPast T) (naturalFiltration T) Prod.snd from measurable_snd)
  exact Complex.continuous_exp.comp_stronglyMeasurable
    ((Complex.continuous_ofReal.comp_stronglyMeasurable hx).add
      (stronglyMeasurable_const.mul
        (Complex.continuous_ofReal.comp_stronglyMeasurable hy)))

def jointFiltration : Filtration ℝ≥0
    (inferInstance : MeasurableSpace (SampleSpace × SampleSpace)) where
  seq := jointPast
  mono' := fun _ _ h => sup_le_sup
    (MeasurableSpace.comap_mono (naturalFiltration.mono h))
    (MeasurableSpace.comap_mono (naturalFiltration.mono h))
  le' := jointPast_le

theorem value_martingale : Martingale value jointFiltration
    (gaussianProduct.prod gaussianProduct) :=
  ⟨value_stronglyMeasurable,conditional_value⟩

def observable (T : ℝ≥0) : StochasticCauchyComplexChannels.JointComplex :=
  (value_memLp T).toLp (value T)

theorem observable_ae (T : ℝ≥0) : observable T
    =ᵐ[gaussianProduct.prod gaussianProduct] value T := (value_memLp T).coeFn_toLp

theorem observable_prediction (S T : ℝ≥0) (hST : S ≤ T) :
    (condExpL2 ℂ ℂ (jointPast_le S) (observable T) :
      StochasticCauchyComplexChannels.JointComplex)=observable S := by
  apply Lp.ext
  exact ((value_memLp T).condExpL2_ae_eq_condExp (jointPast_le S)).trans
    ((conditional_value S T hST).trans (observable_ae S).symm)

/-- Innovations are orthogonal to EVERY actual joint-past L2 test observable. -/
theorem observable_innovation_pairing (S T : ℝ≥0) (hST : S ≤ T)
    (H : StochasticCauchyComplexChannels.JointComplex)
    (hH : AEStronglyMeasurable[jointPast S] H
      (gaussianProduct.prod gaussianProduct)) :
    inner ℂ (observable T-observable S) H=0 := by
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℂ) (jointPast_le S)
    (observable T) H hH
  rw [observable_prediction S T hST] at hi
  rw [inner_sub_left,← hi,sub_self]

theorem observable_energy (T : ℝ≥0) : ‖observable T‖^2=Real.exp (2*(T:ℝ)) := by
  rw [BochnerL2Dominated.norm_sq_integral]
  have he : (∫ w,‖observable T w‖^2 ∂gaussianProduct.prod gaussianProduct)=
      ∫ w,Real.exp (2*process T w.1) ∂gaussianProduct.prod gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [observable_ae T] with w hw
    rw [hw]
    exact StochasticCauchyGaussianNormalization.exponential_norm_sq
      (process T w.1,process T w.2)
  rw [he,integral_fun_fst (fun w : SampleSpace => Real.exp (2*process T w))]
  simp only [probReal_univ,one_smul]
  have hl := (process_hasLaw T).integral_comp (f := fun x : ℝ => Real.exp (2*x))
    (by fun_prop)
  simp only [Function.comp_apply] at hl
  rw [hl]
  have hm := congrFun (mgf_id_gaussianReal (μ := 0) (v := T)) 2
  simp only [mgf,id_eq,mul_zero,zero_add] at hm
  convert hm using 1
  congr 1
  ring

/-- Exact source-law L2 time modulus, not only terminal variance. -/
theorem observable_increment_energy (S T : ℝ≥0) (hST : S ≤ T) :
    ‖observable T-observable S‖^2=Real.exp (2*(T:ℝ))-Real.exp (2*(S:ℝ)) := by
  have hs : AEStronglyMeasurable[jointPast S] (observable S)
      (gaussianProduct.prod gaussianProduct) :=
    (value_stronglyMeasurable S).aestronglyMeasurable.congr (observable_ae S).symm
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℂ) (jointPast_le S)
    (observable T) (observable S) hs
  rw [observable_prediction S T hST,inner_self_eq_norm_sq_to_K] at hi
  rw [@norm_sub_sq ℂ,← hi,RCLike.re_ofReal_pow,observable_energy,observable_energy]
  ring

theorem observable_distance_energy (S T : ℝ≥0) :
    ‖observable S-observable T‖^2=
      |Real.exp (2*(S:ℝ))-Real.exp (2*(T:ℝ))| := by
  rcases le_total S T with hST | hTS
  · have he : Real.exp (2*(S:ℝ)) ≤ Real.exp (2*(T:ℝ)) :=
      Real.exp_le_exp.mpr (by exact mul_le_mul_of_nonneg_left hST (by norm_num))
    rw [norm_sub_rev,observable_increment_energy S T hST,abs_of_nonpos (sub_nonpos.mpr he)]
    ring
  · have he : Real.exp (2*(T:ℝ)) ≤ Real.exp (2*(S:ℝ)) :=
      Real.exp_le_exp.mpr (by exact mul_le_mul_of_nonneg_left hTS (by norm_num))
    rw [observable_increment_energy T S hTS,abs_of_nonneg (sub_nonneg.mpr he)]

/-- Strong original-product L2 continuity of the running exponential. -/
theorem observable_continuous : Continuous observable := by
  apply continuous_iff_continuousAt.mpr
  intro T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun S : ℝ≥0 =>
      |Real.exp (2*(S:ℝ))-Real.exp (2*(T:ℝ))|) := by fun_prop
  have ht : Tendsto (fun S => ‖observable S-observable T‖^2) (𝓝 T) (𝓝 0) := by
    simpa only [observable_distance_energy,sub_self,abs_zero] using hc.tendsto T
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hs

end OperatorDerivativeRewrite.Foundation.StochasticCauchyExponentialPrediction
