import Foundation.CubeGroundUnitary

/-! Actual all-L2 normalized Haar operator intertwined with the native Wilson transfer. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeHaarOperator
open CubeTemporalSlab CubeWilsonSlab CubeSlabGround CubeSlabL2 CubeNativeL2Domain CubeGroundUnitary
attribute [local irreducible] CubeWilsonSlab.kernel boundaryHaar GroundData.stationary
variable {beta : ℝ} (d : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure d.stationary := d.stationary_probability
private instance kernel_markov : ProbabilityTheory.IsMarkovKernel d.transition := d.transition_markov

def rawKernel (beta : ℝ) (f : State → ℝ) (U : State) : ℝ :=
  ∫ V,kernel beta U V*f V ∂boundaryHaar

private theorem input_abs_integrable (F : HaarL2) : Integrable (fun V => |F V|) boundaryHaar := by
  simpa only [Real.norm_eq_abs] using (Lp.memLp F).norm.integrable (by norm_num : (1:ENNReal) ≤ 2)

theorem raw_measurable (F : HaarL2) : Measurable (rawKernel beta F) :=
  ((kernel_joint_measurable beta).mul ((Lp.stronglyMeasurable F).measurable.comp
    measurable_snd)).stronglyMeasurable.integral_prod_right.measurable

theorem raw_integrable (F : HaarL2) (U : State) :
    Integrable (fun V => kernel beta U V*F V) boundaryHaar := by
  apply ((input_abs_integrable F).const_mul (Real.exp (36*|beta|))).mono'
    (((Measurable.of_uncurry_left (kernel_joint_measurable beta)).mul
      (Lp.stronglyMeasurable F).measurable).aestronglyMeasurable) ?_
  filter_upwards with V
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (kernel_positive beta U V)]
  exact mul_le_mul_of_nonneg_right (kernel_bounds beta U V).2 (abs_nonneg _)

theorem raw_bound (F : HaarL2) (U : State) :
    |rawKernel beta F U| ≤ Real.exp (36*|beta|)*(∫ V,|F V| ∂boundaryHaar) := by
  have h := norm_integral_le_of_norm_le
    ((input_abs_integrable F).const_mul (Real.exp (36*|beta|)))
    (f := fun V => kernel beta U V*F V) (ae_of_all boundaryHaar (fun V => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (kernel_positive beta U V)]
      exact mul_le_mul_of_nonneg_right (kernel_bounds beta U V).2 (abs_nonneg _)))
  rw [integral_const_mul,Real.norm_eq_abs] at h
  exact h

theorem raw_memLp (F : HaarL2) : MemLp (rawKernel beta F) 2 boundaryHaar :=
  MemLp.of_bound (raw_measurable F).aestronglyMeasurable
    (Real.exp (36*|beta|)*(∫ V,|F V| ∂boundaryHaar))
    (ae_of_all boundaryHaar (fun U => by simpa only [Real.norm_eq_abs] using raw_bound F U))

theorem raw_pairing_integrable (F G : HaarL2) :
    Integrable (fun U => G U*rawKernel beta F U) boundaryHaar :=
  (Lp.memLp G).integrable_mul (raw_memLp F)

/-- The same actual native operator, transported by a fully proved unitary. -/
def haarOperator : HaarL2 →L[ℝ] HaarL2 :=
  (unitary d).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((operator d).comp (unitary d).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem haarOperator_apply (F : HaarL2) :
    haarOperator d F=unitary d (operator d ((unitary d).symm F)) := rfl

theorem haarOperator_inner (F G : HaarL2) :
    inner ℝ (haarOperator d F) G=inner ℝ (operator d ((unitary d).symm F)) ((unitary d).symm G) := by
  rw [haarOperator_apply,(unitary d).inner_map_eq_flip]

theorem haarOperator_contraction (F : HaarL2) : ‖haarOperator d F‖ ≤ ‖F‖ := by
  rw [haarOperator_apply,(unitary d).norm_map]
  exact (operator_contraction d _).trans_eq ((unitary d).symm.norm_map F)

theorem haarOperator_symmetric (F G : HaarL2) :
    inner ℝ (haarOperator d F) G=inner ℝ F (haarOperator d G) := by
  rw [← real_inner_comm F (haarOperator d G),haarOperator_inner,haarOperator_inner,operator_symmetric]
  exact real_inner_comm _ _

theorem haarOperator_selfadjoint : (haarOperator d).adjoint=haarOperator d :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr (haarOperator_symmetric d)).symm

/-- Literal transfer identity for every Haar L2 input, not a bounded-core statement. -/
theorem inverse_transfer (F : HaarL2) (U : State) :
    transfer d ((unitary d).symm F) U=
      (Real.sqrt d.normalizer/(d.value*d.function U))*rawKernel beta F U := by
  rw [transfer,d.transition_integral]
  have he : (∫ V,kernel beta U V*(d.function V*((unitary d).symm F) V) ∂boundaryHaar)=
      Real.sqrt d.normalizer*rawKernel beta F U := by
    rw [rawKernel,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(ae_iff d _).mp (unitary_symm_coe d F)] with V hV
    rw [hV]
    unfold inverse
    field_simp [(d.function_pos V).ne'] <;> ring
  rw [he]
  ring

/-- Genuine normalized Haar-kernel pairing on the ENTIRE Haar L2 quotient space.
Both inner and outer literal integrals have verified integrability. -/
theorem haarOperator_kernel_pairing (F G : HaarL2) :
    inner ℝ (haarOperator d F) G=
      (∫ U,G U*(∫ V,kernel beta U V*F V ∂boundaryHaar) ∂boundaryHaar)/d.value := by
  rw [haarOperator_inner,operator_kernel_pairing,d.stationary_integral]
  rw [← integral_div,← integral_div]
  apply integral_congr_ae
  filter_upwards [(ae_iff d _).mp (unitary_symm_coe d G)] with U hG
  rw [hG,inverse_transfer]
  change d.function U^2*(inverse d G U*
    ((Real.sqrt d.normalizer/(d.value*d.function U))*rawKernel beta F U))/d.normalizer=_
  calc
    _ = ((Real.sqrt d.normalizer)^2/d.normalizer)*(G U*rawKernel beta F U/d.value) := by
      unfold inverse
      field_simp [(d.function_pos U).ne',d.value_pos.ne',d.normalizer_pos.ne'] <;> ring
    _ = _ := by
      rw [Real.sq_sqrt d.normalizer_pos.le,div_self d.normalizer_pos.ne',one_mul]
      rfl


private theorem normalized_raw_memLp (F : HaarL2) :
    MemLp (fun U => rawKernel beta F U/d.value) 2 boundaryHaar := by
  have h := (raw_memLp (beta := beta) F).const_mul (1/d.value)
  convert h using 1
  funext U
  ring

def normalizedRaw (F : HaarL2) : HaarL2 :=
  (normalized_raw_memLp d F).toLp (fun U => rawKernel beta F U/d.value)

theorem normalizedRaw_coe (F : HaarL2) :
    normalizedRaw d F =ᵐ[boundaryHaar] (fun U => rawKernel beta F U/d.value) := MemLp.coeFn_toLp _

/-- Strong quotient-space equality with the actual literal normalized kernel. -/
theorem haarOperator_eq_normalizedRaw (F : HaarL2) : haarOperator d F=normalizedRaw d F := by
  apply ext_inner_right ℝ
  intro G
  rw [haarOperator_kernel_pairing,L2.inner_def,← integral_div]
  apply integral_congr_ae
  filter_upwards [normalizedRaw_coe d F] with U hU
  rw [hU,Real.inner_apply]
  change (G U*rawKernel beta F U)/d.value=(rawKernel beta F U/d.value)*G U
  ring

def oneClass : StateL2 d := (memLp_const (1:ℝ)).toLp (fun _ => 1)
theorem oneClass_coe : oneClass d =ᵐ[d.stationary] (fun _ => (1:ℝ)) := MemLp.coeFn_toLp _

def groundVector : HaarL2 := unitary d (oneClass d)

theorem groundVector_coe : groundVector d =ᵐ[boundaryHaar]
    (fun U => d.function U/Real.sqrt d.normalizer) := by
  filter_upwards [unitary_coe d (oneClass d),(ae_iff d _).mp (oneClass_coe d)] with U hU h1
  change unitary d (oneClass d) U=_
  rw [hU]
  unfold transport
  rw [h1,mul_one]

/-- The physical native mean-zero condition is the transported ground complement. -/
theorem centered_iff (f : StateL2 d) :
    (∫ U,f U ∂d.stationary)=0 ↔ inner ℝ (unitary d f) (groundVector d)=0 := by
  have hi : inner ℝ f (oneClass d)=(∫ U,f U ∂d.stationary) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [oneClass_coe d] with U hU
    simp [hU]
  change _ ↔ inner ℝ (unitary d f) (unitary d (oneClass d))=0
  rw [(unitary d).inner_map_map,hi]

private theorem native_one_fixed : operator d (oneClass d)=oneClass d := by
  unfold oneClass
  rw [operator_toLp d _ _ measurable_const 1 (fun _ => by norm_num)]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (transfer_memLp d (fun _ => (1:ℝ)) measurable_const 1
    (fun _ => by norm_num)),MemLp.coeFn_toLp (memLp_const (1:ℝ) (μ := d.stationary) (p := 2))] with U hU h1
  rw [hU,h1]
  simp [transfer,integral_const,probReal_univ]

theorem groundVector_fixed : haarOperator d (groundVector d)=groundVector d := by
  rw [haarOperator_apply]
  change unitary d (operator d ((unitary d).symm (unitary d (oneClass d))))=_
  rw [(unitary d).symm_apply_apply,native_one_fixed]
  rfl


theorem groundVector_norm : ‖groundVector d‖=1 := by
  rw [groundVector,(unitary d).norm_map]
  have hs := BochnerL2Dominated.norm_sq_integral (oneClass d)
  have he : (∫ U,‖oneClass d U‖^2 ∂d.stationary)=1 := by
    calc
      _ = ∫ _ : State,(1:ℝ) ∂d.stationary := by
        apply integral_congr_ae
        filter_upwards [oneClass_coe d] with U hU
        simp [hU]
      _ = 1 := by simp
  rw [he] at hs
  nlinarith [norm_nonneg (oneClass d)]

/-- Full operator norm is1 because the transported stationary vector is fixed.
A gap concerns its orthogonal complement and is not inferred here. -/
theorem haarOperator_norm : ‖haarOperator d‖=1 := by
  apply le_antisymm
  · apply (haarOperator d).opNorm_le_bound (by norm_num : (0:ℝ) ≤ 1)
    intro F
    simpa only [one_mul] using haarOperator_contraction d F
  · have h := (haarOperator d).le_opNorm (groundVector d)
    rw [groundVector_fixed,groundVector_norm,mul_one] at h
    exact h

end OperatorDerivativeRewrite.Foundation.CubeHaarOperator
