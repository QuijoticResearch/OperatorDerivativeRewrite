import Foundation.CubeNativeL2Domain

/-! Actual full-L2 ground half-density equivalence for the homogeneous Wilson slab. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeGroundUnitary
open CubeTemporalSlab CubeWilsonSlab CubeSlabGround CubeSlabL2 CubeNativeL2Domain
attribute [local irreducible] boundaryHaar GroundData.stationary
variable {beta : ℝ} (d : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure d.stationary := d.stationary_probability

abbrev HaarL2 := Lp ℝ 2 boundaryHaar

def transport (f : State → ℝ) (U : State) : ℝ := d.function U*f U/Real.sqrt d.normalizer
def inverse (f : State → ℝ) (U : State) : ℝ := Real.sqrt d.normalizer*f U/d.function U

theorem forward_memLp (u : StateL2 d) : MemLp (transport d u) 2 boundaryHaar := by
  have h := (weighted_memLp d u (Lp.stronglyMeasurable u).measurable (Lp.memLp u)).const_mul
    (1/Real.sqrt d.normalizer)
  convert h using 1
  funext U
  unfold transport
  ring

def forward (u : StateL2 d) : HaarL2 := (forward_memLp d u).toLp (transport d u)
theorem forward_coe (u : StateL2 d) : forward d u =ᵐ[boundaryHaar] transport d u := MemLp.coeFn_toLp _

theorem backward_memLp (v : HaarL2) : MemLp (inverse d v) 2 d.stationary := by
  have hm : Measurable (inverse d v) :=
    (measurable_const.mul (Lp.stronglyMeasurable v).measurable).div d.measurable
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (integrable_iff d _).mpr
  have hi := (Lp.memLp v).integrable_sq.const_mul d.normalizer
  convert hi using 1
  funext U
  unfold inverse
  rw [div_pow,mul_pow,Real.sq_sqrt d.normalizer_pos.le]
  field_simp [(d.function_pos U).ne']

def backward (v : HaarL2) : StateL2 d := (backward_memLp d v).toLp (inverse d v)
theorem backward_coe (v : HaarL2) : backward d v =ᵐ[d.stationary] inverse d v := MemLp.coeFn_toLp _

theorem forward_add (u v : StateL2 d) : forward d (u+v)=forward d u+forward d v := by
  apply Lp.ext
  filter_upwards [forward_coe d (u+v),forward_coe d u,forward_coe d v,
    (ae_iff d _).mp (Lp.coeFn_add u v),Lp.coeFn_add (forward d u) (forward d v)] with U h h1 h2 ha hb
  rw [h,hb]
  simp only [Pi.add_apply]
  rw [h1,h2]
  unfold transport
  rw [ha]
  simp only [Pi.add_apply]
  ring

theorem forward_smul (a : ℝ) (u : StateL2 d) : forward d (a • u)=a • forward d u := by
  apply Lp.ext
  filter_upwards [forward_coe d (a • u),forward_coe d u,
    (ae_iff d _).mp (Lp.coeFn_smul a u),Lp.coeFn_smul a (forward d u)] with U h h1 ha hb
  rw [h,hb]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [h1]
  unfold transport
  rw [ha]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

def forwardLinear : StateL2 d →ₗ[ℝ] HaarL2 where
  toFun := forward d
  map_add' := forward_add d
  map_smul' := forward_smul d

theorem backward_forward (u : StateL2 d) : backward d (forward d u)=u := by
  apply Lp.ext
  filter_upwards [backward_coe d (forward d u),(ae_iff d _).mpr (forward_coe d u)] with U hb hf
  rw [hb]
  unfold inverse
  rw [hf]
  unfold transport
  field_simp [(d.function_pos U).ne',(Real.sqrt_pos.mpr d.normalizer_pos).ne']

theorem forward_backward (v : HaarL2) : forward d (backward d v)=v := by
  apply Lp.ext
  filter_upwards [forward_coe d (backward d v),(ae_iff d _).mp (backward_coe d v)] with U hf hb
  rw [hf]
  unfold transport
  rw [hb]
  unfold inverse
  field_simp [(d.function_pos U).ne',(Real.sqrt_pos.mpr d.normalizer_pos).ne']

theorem forward_norm (u : StateL2 d) : ‖forward d u‖=‖u‖ := by
  have hs : ‖forward d u‖^2=‖u‖^2 := by
    calc
      _ = ∫ U,‖forward d u U‖^2 ∂boundaryHaar := BochnerL2Dominated.norm_sq_integral _
      _ = (∫ U,(d.function U*u U)^2 ∂boundaryHaar)/d.normalizer := by
        rw [← integral_div]
        apply integral_congr_ae
        filter_upwards [forward_coe d u] with U hU
        rw [hU]
        simp only [transport,Real.norm_eq_abs,sq_abs,div_pow,Real.sq_sqrt d.normalizer_pos.le]
      _ = ‖u‖^2 := by
        rw [weighted_square_integral d u (Lp.memLp u),Lp.toLp_coeFn]
        field_simp [d.normalizer_pos.ne']
  nlinarith [norm_nonneg (forward d u),norm_nonneg u]

/-- Genuine equivalence of the two actual L2 quotient spaces, on their full domains. -/
def unitary : StateL2 d ≃ₗᵢ[ℝ] HaarL2 where
  toLinearEquiv := LinearEquiv.ofBijective (forwardLinear d)
    ⟨(show Function.LeftInverse (backward d) (forward d) from backward_forward d).injective,
      (show Function.RightInverse (backward d) (forward d) from forward_backward d).surjective⟩
  norm_map' := forward_norm d

theorem unitary_coe (u : StateL2 d) : unitary d u =ᵐ[boundaryHaar] transport d u := forward_coe d u

theorem unitary_symm_apply (v : HaarL2) : (unitary d).symm v=backward d v := by
  apply (unitary d).injective
  change unitary d ((unitary d).symm v)=forward d (backward d v)
  rw [LinearIsometryEquiv.apply_symm_apply,forward_backward]

theorem unitary_symm_coe (v : HaarL2) : (unitary d).symm v =ᵐ[d.stationary] inverse d v := by
  rw [unitary_symm_apply]
  exact backward_coe d v

end OperatorDerivativeRewrite.Foundation.CubeGroundUnitary
