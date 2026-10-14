import Foundation.PoissonCharlierHilbertBasis
import Foundation.PoissonPolynomialRecovery

/-! All-L2 Poisson source-divergence recovery from the proved complete ladder. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonDivergenceRecovery
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonCharlierLadder PoissonCharlierHilbertBasis

theorem normalizer_succ (rate : ℝ≥0) (n : ℕ) :
    normalizer rate (n+1)=Real.sqrt (n+1 : ℝ)*Real.sqrt (rate : ℝ)*normalizer rate n := by
  unfold normalizer
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  rw [show (n+1 : ℝ)*(n.factorial : ℝ)*((rate : ℝ)^n*rate)=
    (n+1 : ℝ)*(rate : ℝ)*((n.factorial : ℝ)*(rate : ℝ)^n) by ring]
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]

def normalizedField (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) : FieldL2 rate :=
  (Real.sqrt (rate : ℝ)*normalizer rate n)⁻¹ • field rate hr n

theorem normalizedField_orthonormal (rate : ℝ≥0) (hr : 0 < rate) :
    Orthonormal ℝ (normalizedField rate hr) := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalizedField,real_inner_smul_left,real_inner_smul_right,field_inner,scalar_inner]
  by_cases h : n=m
  · subst m
    simp only [ite_true]
    have hs : (normalizer rate n)^2=(n.factorial : ℝ)*(rate : ℝ)^n := Real.sq_sqrt (by positivity)
    have hRate := Real.sq_sqrt rate.coe_nonneg
    have hn := ne_of_gt (normalizer_pos rate hr n)
    have hp := ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ)<rate from hr))
    field_simp
    nlinarith
  · simp [h]

theorem normalized_raising_graph (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    (normalizedField rate hr n,Real.sqrt (n+1 : ℝ) • normalized rate hr (n+1)) ∈
      (maximalDivergence rate hr).graph := by
  have hg := (maximalDivergence rate hr).graph.smul_mem
    (Real.sqrt (rate : ℝ)*normalizer rate n)⁻¹ (raising_graph rate hr n)
  have hp := ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ)<n+1 by positivity))
  have he : Real.sqrt (n+1 : ℝ)*(normalizer rate (n+1))⁻¹=
      (Real.sqrt (rate : ℝ)*normalizer rate n)⁻¹ := by
    rw [normalizer_succ]
    field_simp
  simpa only [normalizedField,normalized,Prod.smul_mk,smul_smul,he] using hg

def coefficient (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (n : ℕ) : ℝ :=
  inner ℝ (normalized rate hr n) f

def inverseCoefficient (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (n : ℕ) : ℝ :=
  coefficient rate hr f (n+1)/Real.sqrt (n+1 : ℝ)

theorem coefficient_energy (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    HasSum (fun n => (coefficient rate hr f n)^2) (‖f‖^2) := by
  simpa only [HilbertBasis.repr_apply_apply,basis_apply,coefficient,real_inner_self_eq_norm_sq,
    real_inner_comm f,pow_two]
    using (basis rate hr).hasSum_inner_mul_inner f f

theorem inverseCoefficient_sq_le (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (n : ℕ) :
    (inverseCoefficient rate hr f n)^2 ≤ (coefficient rate hr f (n+1))^2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n+1 by positivity)
  have hp : 0 < Real.sqrt (n+1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have h1 : (1 : ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold inverseCoefficient
  rw [div_pow,hs]
  exact div_le_self (sq_nonneg _) h1

theorem recovery_summable (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    Summable (fun n => inverseCoefficient rate hr f n • normalizedField rate hr n) := by
  have hc : Summable (fun n => (coefficient rate hr f (n+1))^2) :=
    (coefficient_energy rate hr f).summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hi := hc.of_nonneg_of_le (fun n => sq_nonneg (inverseCoefficient rate hr f n))
    (inverseCoefficient_sq_le rate hr f)
  simpa only [LinearIsometry.toSpanSingleton_apply,Real.norm_eq_abs,sq_abs] using
    ((normalizedField_orthonormal rate hr).orthogonalFamily.summable_iff_norm_sq_summable
      (inverseCoefficient rate hr f)).mpr (by simpa only [Real.norm_eq_abs,sq_abs] using hi)

def recovery (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) : FieldL2 rate :=
  ∑' n, inverseCoefficient rate hr f n • normalizedField rate hr n

def centered (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) : ScalarL2 rate :=
  f-coefficient rate hr f 0 • normalized rate hr 0

theorem centered_hasSum (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    HasSum (fun n => coefficient rate hr f (n+1) • normalized rate hr (n+1))
      (centered rate hr f) := by
  have he := expansion_hasSum rate hr f
  apply (hasSum_nat_add_iff 1 (f := fun n => coefficient rate hr f n • normalized rate hr n)
    (g := centered rate hr f)).mpr
  simpa only [coefficient,Finset.sum_range_one,centered,sub_add_cancel] using he

theorem recovery_graph (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    (recovery rate hr f,centered rate hr f) ∈ (maximalDivergence rate hr).graph := by
  have hi := (recovery_summable rate hr f).hasSum
  change HasSum _ (recovery rate hr f) at hi
  apply (maximalDivergence_isClosed rate hr).mem_of_tendsto
    (hi.prodMk_nhds (centered_hasSum rate hr f))
  exact Eventually.of_forall fun s => by
    rw [prod_mk_sum]
    apply (maximalDivergence rate hr).graph.sum_mem
    intro n _
    have hg := (maximalDivergence rate hr).graph.smul_mem
      (inverseCoefficient rate hr f n) (normalized_raising_graph rate hr n)
    have hp := ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ)<n+1 by positivity))
    simpa only [Prod.smul_mk,smul_smul,inverseCoefficient,div_mul_cancel₀ _ hp] using hg

theorem recovery_unique (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate)
    (u : FieldL2 rate) (hu : (u,centered rate hr f) ∈ (maximalDivergence rate hr).graph) :
    u=recovery rate hr f := by
  have hz : (u-recovery rate hr f,0) ∈ (maximalDivergence rate hr).graph := by
    simpa only [Prod.mk_sub_mk,sub_self] using
      (maximalDivergence rate hr).graph.sub_mem hu (recovery_graph rate hr f)
  exact sub_eq_zero.mp ((DivergenceKernelContrast.poisson_divergence_zero_iff rate hr _).mp hz)

theorem recovery_energy (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    HasSum (fun n => (inverseCoefficient rate hr f n)^2) (‖recovery rate hr f‖^2) := by
  have ht := (recovery_summable rate hr f).hasSum.norm.pow 2
  change Tendsto (fun s : Finset ℕ => ‖∑ n ∈ s,
    inverseCoefficient rate hr f n • normalizedField rate hr n‖^2)
    atTop (𝓝 (‖recovery rate hr f‖^2)) at ht
  change Tendsto (fun s : Finset ℕ => ∑ n ∈ s, (inverseCoefficient rate hr f n)^2)
    atTop (𝓝 (‖recovery rate hr f‖^2))
  have he (s : Finset ℕ) :
      ‖∑ n ∈ s, inverseCoefficient rate hr f n • normalizedField rate hr n‖^2=
        ∑ n ∈ s, (inverseCoefficient rate hr f n)^2 := by
    simpa only [LinearIsometry.toSpanSingleton_apply,Real.norm_eq_abs,sq_abs] using
      (normalizedField_orthonormal rate hr).orthogonalFamily.norm_sum
        (inverseCoefficient rate hr f) s
  simpa only [he] using ht

theorem recovery_norm_le (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    ‖recovery rate hr f‖ ≤ ‖f‖ := by
  have hc := (coefficient_energy rate hr f).summable.comp_injective
    (fun a b (h : a+1=b+1) => Nat.add_right_cancel h)
  have he := hasSum_le (inverseCoefficient_sq_le rate hr f) (recovery_energy rate hr f) hc.hasSum
  simp only [Function.comp_apply] at he
  have hb : (∑' n, (coefficient rate hr f (n+1))^2) ≤ ‖f‖^2 := by
    rw [← (coefficient_energy rate hr f).tsum_eq]
    exact hc.tsum_le_tsum_of_inj (fun n => n+1) (fun _ _ h => Nat.add_right_cancel h)
      (fun _ _ => sq_nonneg _) (fun _ => le_rfl) (coefficient_energy rate hr f).summable
  nlinarith [norm_nonneg (recovery rate hr f),norm_nonneg f]

theorem zero_mode_difference_graph (rate : ℝ≥0) (hr : 0 < rate) :
    (normalized rate hr 0,0) ∈ (maximalDifference rate hr).graph := by
  rw [maximalDifference_graph]
  intro k
  simp only [normalized,normalizer,Nat.factorial_zero,Nat.cast_one,pow_zero,mul_one,
    Real.sqrt_one,inv_one,one_smul,PoissonCoordinateEvaluation.field_zero_apply rate hr,
    scalar_apply,value_zero,sub_self]

theorem exists_divergence_iff_zero_mode (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    (∃ u : FieldL2 rate, (u,f) ∈ (maximalDivergence rate hr).graph) ↔
      coefficient rate hr f 0=0 := by
  constructor
  · rintro ⟨u,hu⟩
    have hi := graph_duality rate hr (zero_mode_difference_graph rate hr) hu
    simpa only [inner_zero_left,coefficient] using hi.symm
  · intro hf
    refine ⟨recovery rate hr f, ?_⟩
    simpa only [centered,hf,zero_smul,sub_zero] using recovery_graph rate hr f

theorem coefficient_zero_integral (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    coefficient rate hr f 0=∫ k, f k ∂poissonLaw rate := by
  rw [coefficient,L2_inner_eq_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun k => by
    simp only [normalized,normalizer,Nat.factorial_zero,Nat.cast_one,pow_zero,mul_one,
      Real.sqrt_one,inv_one,one_smul,scalar_apply,value_zero]
    simp

theorem exists_divergence_iff_centered (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    (∃ u : FieldL2 rate, (u,f) ∈ (maximalDivergence rate hr).graph) ↔
      (∫ k, f k ∂poissonLaw rate)=0 := by
  rw [exists_divergence_iff_zero_mode,coefficient_zero_integral]

theorem recovery_add (rate : ℝ≥0) (hr : 0 < rate) (f g : ScalarL2 rate) :
    recovery rate hr (f+g)=recovery rate hr f+recovery rate hr g := by
  apply Eq.symm
  apply recovery_unique
  have hg := (maximalDivergence rate hr).graph.add_mem (recovery_graph rate hr f)
    (recovery_graph rate hr g)
  simpa only [Prod.mk_add_mk,centered,coefficient,inner_add_right,add_smul,add_sub_add_comm]
    using hg

theorem recovery_smul (rate : ℝ≥0) (hr : 0 < rate) (c : ℝ) (f : ScalarL2 rate) :
    recovery rate hr (c • f)=c • recovery rate hr f := by
  apply Eq.symm
  apply recovery_unique
  have hg := (maximalDivergence rate hr).graph.smul_mem c (recovery_graph rate hr f)
  simpa only [Prod.smul_mk,centered,coefficient,inner_smul_right,smul_sub,smul_smul]
    using hg

def recoveryOperator (rate : ℝ≥0) (hr : 0 < rate) : ScalarL2 rate →L[ℝ] FieldL2 rate :=
  ({ toFun := recovery rate hr, map_add' := recovery_add rate hr, map_smul' := recovery_smul rate hr } :
    ScalarL2 rate →ₗ[ℝ] FieldL2 rate).mkContinuous 1
      (fun f => by
        change ‖recovery rate hr f‖ ≤ 1*‖f‖
        simpa only [one_mul] using recovery_norm_le rate hr f)

end OperatorDerivativeRewrite.Foundation.PoissonDivergenceRecovery
