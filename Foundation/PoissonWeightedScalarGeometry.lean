import Foundation.PoissonDivergenceRecovery

/-! Actual rate-weighted field geometry and its complete spectral coordinates. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonWeightedScalarGeometry
open PoissonDifferenceCore PoissonDifferenceOperators PoissonWeightedDomains PoissonCoordinateEvaluation
open PoissonCharlierHilbertBasis PoissonDivergenceRecovery PoissonCharlierLadder

theorem unweighted_memLp (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) :
    MemLp (fun k => u k) 2 (poissonLaw rate) :=
  (memLp_two_iff_summable_weighted_sq rate _).mpr
    ((memLp_two_weighted_iff_summable_weighted_sq rate hr _).mp (Lp.memLp u))

def unweighted (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) : ScalarL2 rate :=
  (unweighted_memLp rate hr u).toLp (fun k => u k)

def weighted (rate : ℝ≥0) (f : ScalarL2 rate) : FieldL2 rate :=
  (scalar_memLp_weighted rate f).toLp (fun k => f k)

def toScalar (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) : ScalarL2 rate :=
  Real.sqrt (rate : ℝ) • unweighted rate hr u

def toField (rate : ℝ≥0) (f : ScalarL2 rate) : FieldL2 rate :=
  (Real.sqrt (rate : ℝ))⁻¹ • weighted rate f

theorem toScalar_apply (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) (k : ℕ) :
    toScalar rate hr u k=Real.sqrt (rate : ℝ)*u k := by
  rw [toScalar,scalar_smul_apply rate hr]
  congr 1
  exact ae_eq_implies_pointwise rate hr (MemLp.coeFn_toLp (unweighted_memLp rate hr u)) k

theorem toField_apply (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (k : ℕ) :
    toField rate f k=(Real.sqrt (rate : ℝ))⁻¹*f k := by
  rw [toField,field_smul_apply rate hr]
  congr 1
  exact weighted_ae_eq_implies_pointwise rate hr (MemLp.coeFn_toLp (scalar_memLp_weighted rate f)) k

def weightedScalarLinearEquiv (rate : ℝ≥0) (hr : 0 < rate) : FieldL2 rate ≃ₗ[ℝ] ScalarL2 rate where
  toFun := toScalar rate hr
  invFun := toField rate
  left_inv u := by
    apply Lp.ext
    filter_upwards [] with k
    rw [toField_apply rate hr,toScalar_apply rate hr]
    have hp := ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ)<rate from hr))
    field_simp
  right_inv f := by
    apply Lp.ext
    filter_upwards [] with k
    rw [toScalar_apply rate hr,toField_apply rate hr]
    have hp := ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ)<rate from hr))
    field_simp
  map_add' u v := by
    apply Lp.ext
    filter_upwards [] with k
    rw [toScalar_apply rate hr,scalar_add_apply rate hr,toScalar_apply rate hr,
      toScalar_apply rate hr,field_add_apply rate hr]
    ring
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [] with k
    change toScalar rate hr (c • u) k=(c • toScalar rate hr u) k
    rw [toScalar_apply rate hr,scalar_smul_apply rate hr,toScalar_apply rate hr,field_smul_apply rate hr]
    ring

theorem field_norm_sq (rate : ℝ≥0) (u : FieldL2 rate) :
    ‖u‖^2=(rate : ℝ)*(∫ k, (u k)^2 ∂poissonLaw rate) := by
  calc
    _ = ∫ k, (u k)^2 ∂((rate : ℝ≥0∞) • poissonLaw rate) := by
      rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun k => by
        simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    _ = _ := by rw [integral_smul_measure]; simp

theorem toScalar_norm (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) :
    ‖toScalar rate hr u‖=‖u‖ := by
  have he : ‖toScalar rate hr u‖^2=‖u‖^2 := by
    rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral,field_norm_sq]
    have hi : (fun k => inner ℝ (toScalar rate hr u k) (toScalar rate hr u k))=
        fun k => (rate : ℝ)*(u k)^2 := by
      funext k
      rw [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,toScalar_apply,mul_pow,
        Real.sq_sqrt rate.coe_nonneg]
    rw [hi,integral_const_mul]
  nlinarith [norm_nonneg (toScalar rate hr u),norm_nonneg u]

def weightedScalarEquiv (rate : ℝ≥0) (hr : 0 < rate) : FieldL2 rate ≃ₗᵢ[ℝ] ScalarL2 rate where
  __ := weightedScalarLinearEquiv rate hr
  norm_map' u := by
    change ‖toScalar rate hr u‖=‖u‖
    exact toScalar_norm rate hr u

theorem equiv_normalizedField (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    weightedScalarEquiv rate hr (normalizedField rate hr n)=normalized rate hr n := by
  apply Lp.ext
  filter_upwards [] with k
  change toScalar rate hr (normalizedField rate hr n) k=normalized rate hr n k
  rw [toScalar_apply,normalizedField,field_smul_apply rate hr,field_apply,
    normalized,scalar_smul_apply rate hr,scalar_apply]
  have hp := ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ)<rate from hr))
  have hn := ne_of_gt (normalizer_pos rate hr n)
  field_simp

def fieldBasis (rate : ℝ≥0) (hr : 0 < rate) : HilbertBasis ℕ ℝ (FieldL2 rate) :=
  HilbertBasis.ofRepr ((weightedScalarEquiv rate hr).trans (basis rate hr).repr)

theorem fieldBasis_apply (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    fieldBasis rate hr n=normalizedField rate hr n := by
  apply (weightedScalarEquiv rate hr).injective
  rw [← HilbertBasis.repr_symm_single (fieldBasis rate hr) n]
  change weightedScalarEquiv rate hr (((weightedScalarEquiv rate hr).trans
    (basis rate hr).repr).symm (lp.single 2 n (1 : ℝ)))= _
  rw [LinearIsometryEquiv.symm_trans,LinearIsometryEquiv.trans_apply]
  rw [LinearIsometryEquiv.apply_symm_apply,HilbertBasis.repr_symm_single,basis_apply,
    equiv_normalizedField]

theorem fieldBasis_hasSum (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) :
    HasSum (fun n => (inner ℝ (normalizedField rate hr n) u) • normalizedField rate hr n) u := by
  simpa only [HilbertBasis.repr_apply_apply,fieldBasis_apply] using (fieldBasis rate hr).hasSum_repr u

end OperatorDerivativeRewrite.Foundation.PoissonWeightedScalarGeometry
