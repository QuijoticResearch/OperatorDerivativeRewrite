import Foundation.StochasticCauchyFractionalDivergence
import Foundation.ContinuousFractionalPrediction
import Foundation.IndependentInitialConditioning

/-! Actual product-past conditioning for the Cauchy source audit.
The fractional forecasts retain their full observed past. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyFractionalConditioning

section ProductConditioning
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Restrict the independent other factor to its own past using the tower law. -/
theorem conditional_snd (nX : MeasurableSpace X) (nY : MeasurableSpace Y)
    (hx : nX ≤ mX) (hy : nY ≤ mY) (f : Y → ℝ) (hf : Integrable f ν) :
    (@Measure.prod X Y mX mY μ ν)[(fun w : X × Y => f w.2) | nX.prod nY] =ᵐ[@Measure.prod X Y mX mY μ ν]
      fun w => (ν[f | nY]) w.2 := by
  let : MeasurableSpace X := mX
  let : MeasurableSpace Y := mY
  have hsmall : nX.prod nY ≤ mX.prod nY :=
    sup_le_sup (MeasurableSpace.comap_mono hx) le_rfl
  have hlarge : mX.prod nY ≤ mX.prod mY :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono hy)
  have hce := IndependentInitialConditioning.conditional_snd μ ν nY hy f (ν[f | nY])
    hf integrable_condExp stronglyMeasurable_condExp Filter.EventuallyEq.rfl
  have ht := condExp_condExp_of_le (f := fun w : X × Y => f w.2)
    (μ := μ.prod ν) hsmall hlarge
  have hm : StronglyMeasurable[nX.prod nY] (fun w : X × Y => (ν[f | nY]) w.2) :=
    stronglyMeasurable_condExp.comp_measurable
      (show @Measurable (X × Y) Y (nX.prod nY) nY Prod.snd from measurable_snd)
  have hi : Integrable (fun w : X × Y => (ν[f | nY]) w.2) (@Measure.prod X Y mX mY μ ν) :=
    (measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable integrable_condExp
  exact ht.symm.trans ((condExp_congr_ae (m := nX.prod nY) hce).trans
    (Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (hsmall.trans hlarge) hm hi)))

/-- The first coordinate uses the same theorem with genuine measure-preserving
source exchange, rather than treating the two physical coordinates as equal. -/
theorem conditional_fst (nX : MeasurableSpace X) (nY : MeasurableSpace Y)
    (hx : nX ≤ mX) (hy : nY ≤ mY) (f : X → ℝ) (hf : Integrable f μ) :
    (@Measure.prod X Y mX mY μ ν)[(fun w : X × Y => f w.1) | nX.prod nY] =ᵐ[@Measure.prod X Y mX mY μ ν]
      fun w => (μ[f | nX]) w.1 := by
  let : MeasurableSpace X := mX
  let : MeasurableSpace Y := mY
  have hm : nX.prod nY ≤ mX.prod mY :=
    sup_le_sup (MeasurableSpace.comap_mono hx) (MeasurableSpace.comap_mono hy)
  have hf' := (measurePreserving_fst (μ := μ) (ν := ν)).integrable_comp_of_integrable hf
  have hg' : Integrable (fun w : X × Y => (μ[f | nX]) w.1) (@Measure.prod X Y mX mY μ ν) :=
    (measurePreserving_fst (μ := μ) (ν := ν)).integrable_comp_of_integrable integrable_condExp
  have hc := conditional_snd ν μ nY nX hy hx f hf
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf' (fun _ _ _ => hg'.integrableOn)
  · intro A hA _
    have hAs : MeasurableSet[nY.prod nX] (Prod.swap ⁻¹' A) :=
      (@measurable_swap Y X nY nX) hA
    have hint := setIntegral_condExp
      (show nY.prod nX ≤ mY.prod mX from
        sup_le_sup (MeasurableSpace.comap_mono hy) (MeasurableSpace.comap_mono hx))
      ((measurePreserving_snd (μ := ν) (ν := μ)).integrable_comp_of_integrable hf) hAs
    change (∫ w in Prod.swap ⁻¹' A, (ν.prod μ)[(fun z : Y × X => f z.2) | nY.prod nX] w ∂ν.prod μ) =
      ∫ w in Prod.swap ⁻¹' A, f w.2 ∂ν.prod μ at hint
    have he : (∫ w in Prod.swap ⁻¹' A, (ν.prod μ)[(fun z : Y × X => f z.2) | nY.prod nX] w ∂ν.prod μ) =
        ∫ w in Prod.swap ⁻¹' A, (μ[f | nX]) w.2 ∂ν.prod μ :=
      integral_congr_ae (ae_restrict_of_ae hc)
    rw [he] at hint
    have hs (g : X → ℝ) : (∫ w in Prod.swap ⁻¹' A, g w.2 ∂ν.prod μ) =
        ∫ w in A, g w.1 ∂μ.prod ν :=
      Measure.measurePreserving_swap.setIntegral_preimage_emb
        MeasurableEquiv.prodComm.measurableEmbedding (fun w : X × Y => g w.1) A
    rw [hs,hs] at hint
    exact hint
  · exact (stronglyMeasurable_condExp.comp_measurable
      (show @Measurable (X × Y) X (nX.prod nY) nX Prod.fst from measurable_fst)).aestronglyMeasurable
end ProductConditioning

open InfiniteGaussian GaussianTimeSpaceHermite IBMCubicFirstChaos
open ProductL2Curry ComplexL2Isometry StochasticCauchyParameterizedObstruction
open GaussianConditionalGraph GaussianWickConditionalProjection
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable

def properValue (h : CoefficientSpace) := combine (gaussianProduct.prod gaussianProduct)
  (productTensor gaussianProduct gaussianProduct (firstChaosEmbedding h) gaussianOne)
  (productTensor gaussianProduct gaussianProduct gaussianOne (firstChaosEmbedding h))

def conjugateValue (h : CoefficientSpace) := combine (gaussianProduct.prod gaussianProduct)
  (productTensor gaussianProduct gaussianProduct (firstChaosEmbedding h) gaussianOne)
  (-productTensor gaussianProduct gaussianProduct gaussianOne (firstChaosEmbedding h))

private theorem ofReal_inner (a b : JointL2) :
    inner ℂ (ofReal (gaussianProduct.prod gaussianProduct) a)
      (ofReal (gaussianProduct.prod gaussianProduct) b) = (inner ℝ a b : ℂ) := by
  rw [L2.inner_def,L2_inner_eq_integral,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL a,
    Complex.ofRealCLM.coeFn_compLpL b] with w ha hb
  change ofReal (gaussianProduct.prod gaussianProduct) a w = _ at ha
  change ofReal (gaussianProduct.prod gaussianProduct) b w = _ at hb
  rw [ha,hb]
  simp [RCLike.inner_apply]

theorem proper_pairing (h k : CoefficientSpace) :
    inner ℂ (properValue h) (conjugateValue k)=0 := by
  have hc (v : CoefficientSpace) : inner ℝ gaussianOne (firstChaosEmbedding v)=0 := by
    rw [← wick_one_eq_embedding]
    exact wick_centered v 0
  have hcr (v : CoefficientSpace) : inner ℝ (firstChaosEmbedding v) gaussianOne=0 := by
    rw [real_inner_comm]
    exact hc v
  simp only [properValue,conjugateValue,combine,map_neg,smul_neg,inner_add_left,
    inner_add_right,inner_neg_right,inner_smul_left,inner_smul_right,ofReal_inner,
    tensor_inner,firstChaosEmbedding.inner_map_map,
    GaussianDeterministicGraphCore.gaussianOne_inner_self,hc,hcr,
    mul_zero,zero_mul,mul_one,one_mul,Complex.ofReal_zero,add_zero,zero_add,Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

theorem properValue_ae (h : CoefficientSpace) : properValue h =ᵐ[gaussianProduct.prod gaussianProduct]
    fun w => (firstChaosEmbedding h w.1 : ℂ)+Complex.I*(firstChaosEmbedding h w.2 : ℂ) := by
  have hx := (Measure.quasiMeasurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).ae gaussianOne_coeFn
  have hy := (Measure.quasiMeasurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).ae gaussianOne_coeFn
  filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct)
      (productTensor gaussianProduct gaussianProduct (firstChaosEmbedding h) gaussianOne)
      (productTensor gaussianProduct gaussianProduct gaussianOne (firstChaosEmbedding h)),
    productTensor_coeFn gaussianProduct gaussianProduct (firstChaosEmbedding h) gaussianOne,
    productTensor_coeFn gaussianProduct gaussianProduct gaussianOne (firstChaosEmbedding h),hx,hy]
    with w hc hr hi hx hy
  change properValue h w=_ at hc
  rw [hc,hr,hi,hx,hy]
  simp [smul_eq_mul]

theorem conjugateValue_ae (h : CoefficientSpace) : conjugateValue h =ᵐ[gaussianProduct.prod gaussianProduct]
    fun w => star (properValue h w) := by
  filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct)
      (productTensor gaussianProduct gaussianProduct (firstChaosEmbedding h) gaussianOne)
      (-productTensor gaussianProduct gaussianProduct gaussianOne (firstChaosEmbedding h)),
    combine_ae (gaussianProduct.prod gaussianProduct)
      (productTensor gaussianProduct gaussianProduct (firstChaosEmbedding h) gaussianOne)
      (productTensor gaussianProduct gaussianProduct gaussianOne (firstChaosEmbedding h)),
    Lp.coeFn_neg (productTensor gaussianProduct gaussianProduct gaussianOne (firstChaosEmbedding h))]
    with w hc hp hn
  change conjugateValue h w=_ at hc
  change properValue h w=_ at hp
  rw [hc,hp,hn]
  simp

private theorem conditional_complex {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (n : MeasurableSpace Ω) (f g u v : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hu : μ[f | n] =ᵐ[μ] u) (hv : μ[g | n] =ᵐ[μ] v) :
    μ[(fun w => (f w : ℂ)+Complex.I*(g w : ℂ)) | n] =ᵐ[μ]
      fun w => (u w : ℂ)+Complex.I*(v w : ℂ) := by
  let : MeasurableSpace Ω := mΩ
  have hfr := Complex.ofRealCLM.integrable_comp hf
  have hgr := Complex.ofRealCLM.integrable_comp hg
  have ha := condExp_add hfr (hgr.smul Complex.I) n
  have hs := condExp_smul (μ := μ) Complex.I (fun w => (g w : ℂ)) n
  have hr := ContinuousLinearMap.comp_condExp_comm (m := n) hf Complex.ofRealCLM
  have hi := ContinuousLinearMap.comp_condExp_comm (m := n) hg Complex.ofRealCLM
  filter_upwards [ha,hs,hr,hi,hu,hv] with w ha hs hr hi hu hv
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Function.comp_def,Complex.ofRealCLM_apply] at *
  change μ[(fun w => (f w : ℂ)+Complex.I*(g w : ℂ)) | n] w = _ at ha
  rw [ha,hs,← hr,← hi,hu,hv]

variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

def jointPast (s : ℝ≥0) := (ContinuousFractionalPrediction.naturalPast H hH0 hH1 s).prod
  (ContinuousFractionalPrediction.naturalPast H hH0 hH1 s)

def forecastDirection (s : ℝ≥0) : CoefficientSpace :=
  sourceProjection (FractionalPredictionObstruction.pastDirections H hH0 hH1 s)
    (FractionalGaussianProcess.direction H hH0 hH1 1)

def forecastValue (s : ℝ≥0) := properValue (forecastDirection H hH0 hH1 s)

def terminalValue (w : SampleSpace × SampleSpace) : ℂ :=
  (ContinuousFractionalBrownian.process H hH0 hH1 1 w.1 : ℂ)+
    Complex.I*(ContinuousFractionalBrownian.process H hH0 hH1 1 w.2 : ℂ)

theorem forecast_direction_actual (s : ℝ≥0) :
    firstChaosEmbedding (forecastDirection H hH0 hH1 s) =ᵐ[gaussianProduct]
      gaussianProduct[ContinuousFractionalBrownian.process H hH0 hH1 1 |
        ContinuousFractionalPrediction.naturalPast H hH0 hH1 s] := by
  have he : FractionalPredictionObstruction.forecast H hH0 hH1 s=
      firstChaosEmbedding (forecastDirection H hH0 hH1 s) :=
    conditional_firstChaos_projection _ _
  rw [← he]
  exact ContinuousFractionalPrediction.terminal_forecast_actual_past H hH0 hH1 s

private theorem coordinate_integrable : Integrable (ContinuousFractionalBrownian.process H hH0 hH1 1) gaussianProduct :=
  ((Lp.memLp (FractionalGaussianProcess.value H hH0 hH1 1)).integrable (by norm_num)).congr
    (ContinuousFractionalBrownian.process_coordinate_ae H hH0 hH1 1).symm

/-- The complex forecast is the actual conditional expectation on BOTH
continuous observed component pasts, for every H in (0,1). -/
theorem forecast_actual (s : ℝ≥0) : forecastValue H hH0 hH1 s =ᵐ[gaussianProduct.prod gaussianProduct]
    (gaussianProduct.prod gaussianProduct)[terminalValue H hH0 hH1 | jointPast H hH0 hH1 s] := by
  have hm := (ContinuousFractionalPrediction.naturalPast H hH0 hH1).le s
  have hx := (conditional_fst gaussianProduct gaussianProduct _ _ hm hm _ (coordinate_integrable H hH0 hH1)).trans
    ((Measure.quasiMeasurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp
      (forecast_direction_actual H hH0 hH1 s).symm)
  have hy := (conditional_snd gaussianProduct gaussianProduct _ _ hm hm _ (coordinate_integrable H hH0 hH1)).trans
    ((Measure.quasiMeasurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).ae_eq_comp
      (forecast_direction_actual H hH0 hH1 s).symm)
  have hf := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).integrable_comp_of_integrable
    (coordinate_integrable H hH0 hH1)
  have hg := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).integrable_comp_of_integrable
    (coordinate_integrable H hH0 hH1)
  exact (properValue_ae _).trans (conditional_complex _ (jointPast H hH0 hH1 s) _ _ _ _ hf hg hx hy).symm

/-- The source's covariance-only integrand with its stated conjugations is
zero even for the actual full-past fractional forecasts. -/
theorem forecast_pseudocovariance_zero (s t : ℝ≥0) :
    (∫ w, star ((gaussianProduct.prod gaussianProduct)[terminalValue H hH0 hH1 | jointPast H hH0 hH1 s] w) *
      star ((gaussianProduct.prod gaussianProduct)[terminalValue H hH0 hH1 | jointPast H hH0 hH1 t] w)
      ∂gaussianProduct.prod gaussianProduct)=0 := by
  have he := proper_pairing (forecastDirection H hH0 hH1 s) (forecastDirection H hH0 hH1 t)
  rw [L2.inner_def] at he
  rw [← he]
  apply integral_congr_ae
  filter_upwards [forecast_actual H hH0 hH1 s,forecast_actual H hH0 hH1 t,
    conjugateValue_ae (forecastDirection H hH0 hH1 t)] with w hs ht hc
  change forecastValue H hH0 hH1 s w=_ at hs
  change forecastValue H hH0 hH1 t w=_ at ht
  rw [← hs,← ht,hc]
  simp [RCLike.inner_apply,forecastValue,mul_comm]

private theorem terminal_integrable : Integrable (terminalValue H hH0 hH1) (gaussianProduct.prod gaussianProduct) := by
  have hx := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).integrable_comp_of_integrable
    (coordinate_integrable H hH0 hH1)
  have hy := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).integrable_comp_of_integrable
    (coordinate_integrable H hH0 hH1)
  exact (Complex.ofRealCLM.integrable_comp hx).add ((Complex.ofRealCLM.integrable_comp hy).smul Complex.I)

/-- Commutation with conjugation is proved for actual conditional expectation,
not substituted into the source's divergence without a domain argument. -/
theorem conditional_conjugate (s : ℝ≥0) :
    (gaussianProduct.prod gaussianProduct)[(fun w => star (terminalValue H hH0 hH1 w)) | jointPast H hH0 hH1 s]
      =ᵐ[gaussianProduct.prod gaussianProduct]
    fun w => star ((gaussianProduct.prod gaussianProduct)[terminalValue H hH0 hH1 | jointPast H hH0 hH1 s] w) := by
  have he := (ContinuousLinearMap.comp_condExp_comm (m := jointPast H hH0 hH1 s)
    (terminal_integrable H hH0 hH1) (Complex.conjCLE : ℂ →L[ℝ] ℂ)).symm
  exact he

/-- The covariance-only integrand with EXACTLY the source's u and v is zero.
This does not identify the true divergence pairing, whose correction need not vanish. -/
theorem source_covariance_integrand_zero (s t : ℝ≥0) :
    (∫ w, ((gaussianProduct.prod gaussianProduct)[(fun z => star (terminalValue H hH0 hH1 z)) | jointPast H hH0 hH1 s] w) *
      star ((gaussianProduct.prod gaussianProduct)[terminalValue H hH0 hH1 | jointPast H hH0 hH1 t] w)
      ∂gaussianProduct.prod gaussianProduct)=0 := by
  rw [← forecast_pseudocovariance_zero H hH0 hH1 s t]
  apply integral_congr_ae
  filter_upwards [conditional_conjugate H hH0 hH1 s] with w hw
  rw [hw]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyFractionalConditioning
