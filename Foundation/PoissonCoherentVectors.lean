import Foundation.PoissonMoments

/-! Genuine nonpolynomial Poisson coherent vectors, their finite L2 moments
and exact closed forward-difference graph. No polynomial density is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.PoissonCoherentVectors
open PoissonDifferenceCore PoissonDifferenceOperators PoissonWeightedDomains
open PoissonCoordinateEvaluation PoissonMaximalOperators

def exponential (θ : ℝ) (k : ℕ) : ℝ := Real.exp (θ*(k : ℝ))

theorem weighted_exponential_hasSum (rate : ℝ≥0) (θ : ℝ) :
    HasSum (fun k => poissonWeight rate k*exponential θ k)
      (Real.exp ((rate : ℝ)*(Real.exp θ-1))) := by
  have hs : HasSum (fun k : ℕ => ((rate : ℝ)*Real.exp θ)^k/(k.factorial : ℝ))
      (Real.exp ((rate : ℝ)*Real.exp θ)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp ((rate : ℝ)*Real.exp θ)
  have he : (fun k => poissonWeight rate k*exponential θ k) =
      (fun k : ℕ => Real.exp (-(rate : ℝ))*(((rate : ℝ)*Real.exp θ)^k/(k.factorial : ℝ))) := by
    funext k
    have hk : Real.exp (θ*(k : ℝ))=(Real.exp θ)^k := by
      rw [mul_comm,Real.exp_nat_mul]
    rw [exponential,hk,poissonWeight,poissonLaw,poissonMeasure_real_singleton,mul_pow]
    ring
  rw [he]
  have ht : Real.exp (-(rate : ℝ))*Real.exp ((rate : ℝ)*Real.exp θ) =
      Real.exp ((rate : ℝ)*(Real.exp θ-1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← ht]
  exact hs.mul_left _

theorem exponential_memLp (rate : ℝ≥0) (θ : ℝ) :
    MemLp (exponential θ) 2 (poissonLaw rate) := by
  rw [memLp_two_iff_summable_weighted_sq]
  have hs := (weighted_exponential_hasSum rate (2*θ)).summable
  convert hs using 1
  funext k
  simp only [exponential,pow_two,← Real.exp_add]
  congr 2
  ring

theorem exponential_integral (rate : ℝ≥0) (θ : ℝ) :
    (∫ k, exponential θ k ∂poissonLaw rate)=Real.exp ((rate : ℝ)*(Real.exp θ-1)) := by
  rw [integral_eq_weighted_tsum rate _ ((exponential_memLp rate θ).integrable (by norm_num))]
  exact (weighted_exponential_hasSum rate θ).tsum_eq

def scalar (rate : ℝ≥0) (θ : ℝ) : ScalarL2 rate :=
  (exponential_memLp rate θ).toLp (exponential θ)

def field (rate : ℝ≥0) (θ : ℝ) : FieldL2 rate :=
  ((exponential_memLp rate θ).smul_measure (by finiteness)).toLp (exponential θ)

theorem scalar_apply (rate : ℝ≥0) (hr : 0 < rate) (θ : ℝ) (k : ℕ) :
    scalar rate θ k=exponential θ k :=
  ae_eq_implies_pointwise rate hr (MemLp.coeFn_toLp (exponential_memLp rate θ)) k

theorem field_apply (rate : ℝ≥0) (hr : 0 < rate) (θ : ℝ) (k : ℕ) :
    field rate θ k=exponential θ k :=
  weighted_ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp ((exponential_memLp rate θ).smul_measure (by finiteness))) k

theorem scalar_inner (rate : ℝ≥0) (hr : 0 < rate) (θ η : ℝ) :
    inner ℝ (scalar rate θ) (scalar rate η)=
      Real.exp ((rate : ℝ)*(Real.exp (θ+η)-1)) := by
  rw [L2_inner_eq_integral]
  have he : (fun k => inner ℝ (scalar rate θ k) (scalar rate η k)) = exponential (θ+η) := by
    funext k
    rw [scalar_apply rate hr,scalar_apply rate hr]
    simp only [Real.inner_apply,exponential,← Real.exp_add]
    congr 1
    ring
  rw [he,exponential_integral]

def coherent (rate : ℝ≥0) (θ : ℝ) : ScalarL2 rate :=
  Real.exp (-(rate : ℝ)*(Real.exp θ-1)) • scalar rate θ

theorem coherent_inner (rate : ℝ≥0) (hr : 0 < rate) (θ η : ℝ) :
    inner ℝ (coherent rate θ) (coherent rate η)=
      Real.exp ((rate : ℝ)*(Real.exp θ-1)*(Real.exp η-1)) := by
  rw [coherent,coherent,real_inner_smul_left,inner_smul_right,scalar_inner rate hr]
  have he (a b c : ℝ) : Real.exp a*(Real.exp b*Real.exp c)=Real.exp (a+b+c) := by
    rw [Real.exp_add (a+b) c,Real.exp_add a b]
    ring
  calc
    _ = Real.exp (-(rate : ℝ)*(Real.exp θ-1) + -(rate : ℝ)*(Real.exp η-1) +
      (rate : ℝ)*(Real.exp (θ+η)-1)) := he _ _ _
    _ = _ := by rw [Real.exp_add θ η]; congr 1; ring

theorem scalar_integral (rate : ℝ≥0) (θ : ℝ) :
    (∫ k, scalar rate θ k ∂poissonLaw rate)=Real.exp ((rate : ℝ)*(Real.exp θ-1)) := by
  unfold scalar
  rw [integral_congr_ae (MemLp.coeFn_toLp (exponential_memLp rate θ)),exponential_integral]

theorem coherent_integral (rate : ℝ≥0) (θ : ℝ) :
    (∫ k, coherent rate θ k ∂poissonLaw rate)=1 := by
  unfold coherent
  rw [integral_congr_ae (Lp.coeFn_smul (Real.exp (-(rate : ℝ)*(Real.exp θ-1))) (scalar rate θ))]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [integral_const_mul,scalar_integral,← Real.exp_add]
  have he : -(rate : ℝ)*(Real.exp θ-1)+(rate : ℝ)*(Real.exp θ-1)=0 := by ring
  rw [he,Real.exp_zero]

theorem exponential_difference_graph (rate : ℝ≥0) (hr : 0 < rate) (θ : ℝ) :
    (scalar rate θ,(Real.exp θ-1) • field rate θ) ∈ (maximalDifference rate hr).graph := by
  rw [maximalDifference_graph]
  intro k
  rw [field_smul_apply rate hr,field_apply rate hr,scalar_apply rate hr,scalar_apply rate hr]
  simp only [exponential,Nat.cast_add,Nat.cast_one,mul_add,Real.exp_add]
  ring

theorem count_exponential_memLp (rate : ℝ≥0) (θ : ℝ) :
    MemLp (fun k : ℕ => (k : ℝ)*exponential θ k) 2 (poissonLaw rate) := by
  apply (exponential_memLp rate (θ+1)).of_le_mul (c := (1 : ℝ)) (by fun_prop)
  filter_upwards [] with k
  have hk : (k : ℝ) ≤ Real.exp (k : ℝ) := by linarith [Real.add_one_le_exp (k : ℝ)]
  have he : Real.exp (k : ℝ)*exponential θ k=exponential (θ+1) k := by
    unfold exponential
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Real.norm_eq_abs,one_mul]
  have hp : 0 < exponential θ k := Real.exp_pos _
  have hp' : 0 < exponential (θ+1) k := Real.exp_pos _
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) hp.le),abs_of_pos hp']
  exact (mul_le_mul_of_nonneg_right hk hp.le).trans_eq he

def divergenceValue (rate : ℝ≥0) (θ : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ)*Real.exp (-θ)-(rate : ℝ))*exponential θ k

theorem divergenceValue_memLp (rate : ℝ≥0) (θ : ℝ) :
    MemLp (divergenceValue rate θ) 2 (poissonLaw rate) := by
  have h1 := (count_exponential_memLp rate θ).const_mul (Real.exp (-θ))
  have h2 := (exponential_memLp rate θ).const_mul (rate : ℝ)
  convert h1.sub h2 using 1
  funext k
  simp only [divergenceValue,Pi.sub_apply]
  ring

def divergenceScalar (rate : ℝ≥0) (θ : ℝ) : ScalarL2 rate :=
  (divergenceValue_memLp rate θ).toLp (divergenceValue rate θ)

theorem exponential_divergence_graph (rate : ℝ≥0) (hr : 0 < rate) (θ : ℝ) :
    (field rate θ,divergenceScalar rate θ) ∈ (maximalDivergence rate hr).graph := by
  rw [maximalDivergence_graph]
  intro k
  have hd := ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp (divergenceValue_memLp rate θ)) k
  change divergenceScalar rate θ k=divergenceValue rate θ k at hd
  rw [hd]
  cases k with
  | zero => simp [divergenceValue,maximalDivergenceExpr,field_apply rate hr,exponential]
  | succ k =>
    have he : Real.exp (-θ)*exponential θ (k+1)=exponential θ k := by
      unfold exponential
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    simp only [divergenceValue,maximalDivergenceExpr,field_apply rate hr]
    rw [sub_mul,mul_assoc,he]
    simp only [Nat.cast_add,Nat.cast_one]

end OperatorDerivativeRewrite.Foundation.PoissonCoherentVectors
