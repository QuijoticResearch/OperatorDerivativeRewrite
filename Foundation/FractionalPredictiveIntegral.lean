import Foundation.FractionalCausalGridObstruction
import Foundation.GaussianLinearFieldDivergenceCompletion

/-! Constructing the actual dyadic predictive field and its divergence on the
existing closed linear-Gaussian domain. No global boundedness of divergence,
continuous pointwise-field identification or Cameron--Martin convention is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalPredictiveIntegral
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeFieldNorm
open StochasticCauchyFractionalDivergence FractionalGridProjection FractionalCausalGridObstruction
open GaussianConditionalGraph GaussianWickConditionalProjection GaussianLinearFieldDivergenceCompletion
variable (H : ℝ) (hH0 : 0<H) (hH1 : H<1)

private abbrev past (t : ℝ≥0) := sourceSpan (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)

private theorem past_mono {s t : ℝ≥0} (hst : s≤t) : past H hH0 hH1 s≤past H hH0 hH1 t := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro z ⟨r,rfl⟩
    apply (Submodule.span ℝ (range (FractionalPredictionObstruction.pastDirections H hH0 hH1 t))).le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨⟨r.val,r.property.trans hst⟩,rfl⟩
  · exact Submodule.isClosed_topologicalClosure _

private theorem forecast_mem (t : ℝ≥0) : predictionDirection H hH0 hH1 t ∈ past H hH0 hH1 t :=
  (past H hH0 hH1 t).starProjection_apply_mem _

private theorem forecast_pairing (t : ℝ≥0) (w : CoefficientSpace) (hw : w ∈ past H hH0 hH1 t) :
    inner ℝ (predictionDirection H hH0 hH1 t) w=inner ℝ (fractionalIncrement H hH0 hH1) w := by
  have ho := (past H hH0 hH1 t).starProjection_inner_eq_zero (fractionalIncrement H hH0 hH1) w hw
  change inner ℝ (fractionalIncrement H hH0 hH1-predictionDirection H hH0 hH1 t) w=0 at ho
  rw [inner_sub_left] at ho
  linarith

private theorem forecast_increment_orthogonal {a b c d : ℝ≥0}
    (hab : a≤b) (hbc : b≤c) (hcd : c≤d) :
    inner ℝ (predictionDirection H hH0 hH1 b-predictionDirection H hH0 hH1 a)
      (predictionDirection H hH0 hH1 d-predictionDirection H hH0 hH1 c)=0 := by
  let w := predictionDirection H hH0 hH1 b-predictionDirection H hH0 hH1 a
  have hwb : w ∈ past H hH0 hH1 b := (past H hH0 hH1 b).sub_mem
    (forecast_mem H hH0 hH1 b) (past_mono H hH0 hH1 hab (forecast_mem H hH0 hH1 a))
  have hwc := past_mono H hH0 hH1 hbc hwb
  have hwd := past_mono H hH0 hH1 hcd hwc
  have hc : inner ℝ w (predictionDirection H hH0 hH1 c)=inner ℝ (fractionalIncrement H hH0 hH1) w :=
    (real_inner_comm _ _).trans (forecast_pairing H hH0 hH1 c w hwc)
  have hd : inner ℝ w (predictionDirection H hH0 hH1 d)=inner ℝ (fractionalIncrement H hH0 hH1) w :=
    (real_inner_comm _ _).trans (forecast_pairing H hH0 hH1 d w hwd)
  change inner ℝ w (predictionDirection H hH0 hH1 d-predictionDirection H hH0 hH1 c)=0
  rw [inner_sub_right,hd,hc,sub_self]

private theorem forecast_increment_energy {a b : ℝ≥0} (hab : a≤b) :
    inner ℝ (fractionalIncrement H hH0 hH1)
      (predictionDirection H hH0 hH1 b-predictionDirection H hH0 hH1 a)=
        ‖predictionDirection H hH0 hH1 b-predictionDirection H hH0 hH1 a‖^2 := by
  have ha := forecast_pairing H hH0 hH1 a _ (forecast_mem H hH0 hH1 a)
  have hb := forecast_pairing H hH0 hH1 b _ (forecast_mem H hH0 hH1 b)
  have hba := forecast_pairing H hH0 hH1 b _
    (past_mono H hH0 hH1 hab (forecast_mem H hH0 hH1 a))
  rw [real_inner_self_eq_norm_sq] at ha hb
  rw [inner_sub_right]
  have hn := norm_sub_sq_real (predictionDirection H hH0 hH1 b) (predictionDirection H hH0 hH1 a)
  nlinarith

private theorem direction_norm (s t : ℝ≥0) :
    ‖FractionalGaussianProcess.direction H hH0 hH1 t-FractionalGaussianProcess.direction H hH0 hH1 s‖=
      |(t:ℝ)-s|^H := by
  have hn := FractionalGaussianProcess.value_increment_norm H hH0 hH1 s t
  rw [FractionalGaussianProcess.value,FractionalGaussianProcess.value,← map_sub,firstChaosEmbedding.norm_map] at hn
  exact hn

private theorem increment_norm : ‖fractionalIncrement H hH0 hH1‖=1 := by
  change ‖FractionalGaussianProcess.direction H hH0 hH1 2-FractionalGaussianProcess.direction H hH0 hH1 1‖=1
  rw [direction_norm]
  norm_num

private theorem orthogonal_sum_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : ℕ) (v : ℕ → E)
    (ho : ∀ i<N, ∀ j<N, i≠j → inner ℝ (v i) (v j)=0) :
    ‖∑ i ∈ Finset.range N, v i‖^2=∑ i ∈ Finset.range N, ‖v i‖^2 := by
  rw [← real_inner_self_eq_norm_sq,sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum,Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j hj hji
    exact ho i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hji.symm
  · exact fun h => (h hi).elim

private theorem forecast_energy_bound (N : ℕ) (a b : ℕ → ℝ≥0)
    (hab : ∀ i<N, a i≤b i) (hsep : ∀ i<N, ∀ j<N, i<j → b i≤a j) :
    (∑ i ∈ Finset.range N, ‖predictionDirection H hH0 hH1 (b i)-predictionDirection H hH0 hH1 (a i)‖^2)≤1 := by
  let v := fun i => predictionDirection H hH0 hH1 (b i)-predictionDirection H hH0 hH1 (a i)
  have ho : ∀ i<N, ∀ j<N, i≠j → inner ℝ (v i) (v j)=0 := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact forecast_increment_orthogonal H hH0 hH1 (hab i hi) (hsep i hi j hj hlt) (hab j hj)
    · exact (real_inner_comm _ _).trans
        (forecast_increment_orthogonal H hH0 hH1 (hab j hj) (hsep j hj i hi hgt) (hab i hi))
  have hs := orthogonal_sum_sq N v ho
  have hp : inner ℝ (fractionalIncrement H hH0 hH1) (∑ i ∈ Finset.range N, v i)=
      ∑ i ∈ Finset.range N, ‖v i‖^2 := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact forecast_increment_energy H hH0 hH1 (hab i (Finset.mem_range.mp hi))
  have hc := real_inner_mul_inner_self_le (fractionalIncrement H hH0 hH1) (∑ i ∈ Finset.range N, v i)
  rw [hp,real_inner_self_eq_norm_sq,increment_norm,one_pow,real_inner_self_eq_norm_sq,hs,one_mul] at hc
  change (∑ i ∈ Finset.range N, ‖v i‖^2)≤1
  nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.range N) => sq_nonneg ‖v i‖)]

private def rank (a b : CoefficientSpace) : GaussianVectorL2 := scalarTensor a (firstChaosEmbedding b)

private theorem rank_sub_left (a b c : CoefficientSpace) : rank (a-b) c=rank a c-rank b c :=
  (GaussianJointRecoveryIntertwining.sourceTensor (firstChaosEmbedding c)).map_sub a b
private theorem rank_sub_right (a b c : CoefficientSpace) : rank a (b-c)=rank a b-rank a c := by
  simp only [rank,map_sub]

private theorem rank_split (a b c q r : CoefficientSpace) :
    (2:ℝ) • rank (b-a) q+(2:ℝ) • rank (c-b) r-(2:ℝ) • rank (c-a) q=(2:ℝ) • rank (c-b) (r-q) := by
  simp only [rank_sub_left,rank_sub_right,smul_sub]
  module

private theorem rank_inner (a b c d : CoefficientSpace) :
    inner ℝ (rank a b) (rank c d)=inner ℝ b d*inner ℝ a c := by
  rw [rank,rank,scalarTensor_pair_inner,firstChaosEmbedding.inner_map_map]

def grid (n i : ℕ) : ℝ≥0 := 1+(i:ℝ≥0)/(2:ℝ≥0)^n
def times (n : ℕ) (i : Fin (2^n+1)) : ℝ≥0 := grid n i.val
def rate : ℝ := (1/2:ℝ)^H

theorem rate_pos : 0<rate H := by unfold rate; positivity
theorem rate_lt_one (hpos : 0<H) : rate H<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hpos

private theorem grid_mono (n : ℕ) {i j : ℕ} (hij : i≤j) : grid n i≤grid n j := by
  unfold grid
  gcongr

theorem times_monotone (n : ℕ) : Monotone (times n) := by
  intro i j hij
  exact grid_mono n hij

theorem times_endpoints (n : ℕ) : times n 0=1 ∧ times n (Fin.last (2^n))=2 := by
  norm_num [times,grid]

private theorem grid_even (n i : ℕ) : grid (n+1) (2*i)=grid n i := by
  unfold grid
  push_cast
  rw [pow_succ]
  field_simp

private theorem grid_right (n i : ℕ) : grid (n+1) (2*i+2)=grid n (i+1) := by
  have he := grid_even n (i+1)
  simpa only [Nat.mul_add,Nat.mul_one] using he

private theorem grid_half_le_next (n : ℕ) {i j : ℕ} (hij : i<j) :
    grid (n+1) (2*i+1)≤grid n j := by
  rw [← grid_even n j]
  exact grid_mono (n+1) (by omega)

private theorem grid_left_le_half (n i : ℕ) : grid n i≤grid (n+1) (2*i+1) := by
  rw [← grid_even n i]
  exact grid_mono (n+1) (by omega)

private theorem sum_double {E : Type*} [AddCommMonoid E] (N : ℕ) (f : ℕ → E) :
    (∑ j ∈ Finset.range (2*N), f j)=∑ i ∈ Finset.range N, (f (2*i)+f (2*i+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih]
    abel

private def term (n i : ℕ) : GaussianVectorL2 :=
  (2:ℝ) • rank (FractionalGaussianProcess.direction H hH0 hH1 (grid n (i+1))-
    FractionalGaussianProcess.direction H hH0 hH1 (grid n i))
    (predictionDirection H hH0 hH1 (grid n i))

def dyadicField (n : ℕ) : GaussianVectorL2 := ∑ i ∈ Finset.range (2^n), term H hH0 hH1 n i

private def rightDirection (n i : ℕ) : CoefficientSpace :=
  FractionalGaussianProcess.direction H hH0 hH1 (grid n (i+1))-
    FractionalGaussianProcess.direction H hH0 hH1 (grid (n+1) (2*i+1))
private def forecastIncrement (n i : ℕ) : CoefficientSpace :=
  predictionDirection H hH0 hH1 (grid (n+1) (2*i+1))-predictionDirection H hH0 hH1 (grid n i)

theorem field_as_conditioned (n : ℕ) : dyadicField H hH0 hH1 n=conditionedField H hH0 hH1 (times n) := by
  rw [dyadicField,conditionedField]
  change (∑ i ∈ Finset.range (2^n), term H hH0 hH1 n i)=∑ i : Fin (2^n), term H hH0 hH1 n i
  exact Finset.sum_range _

theorem field_mem_linear (n : ℕ) : dyadicField H hH0 hH1 n ∈ linearGaussianFields := by
  apply linearGaussianFields.sum_mem
  intro i _
  exact linearGaussianFields.smul_mem (2:ℝ) (linear_rank_mem _ _)

theorem finite_output (n : ℕ) :
    completedDivergence (dyadicField H hH0 hH1 n)=conditionedOutput H hH0 hH1 (times n) := by
  rw [field_as_conditioned]
  simp only [conditionedField,conditionedOutput,map_sum,map_smul,predictedValue,completedDivergence_rank]

private theorem term_split (n i : ℕ) :
    term H hH0 hH1 (n+1) (2*i)+term H hH0 hH1 (n+1) (2*i+1)-term H hH0 hH1 n i=
      (2:ℝ) • rank (rightDirection H hH0 hH1 n i) (forecastIncrement H hH0 hH1 n i) := by
  simp only [term,show 2*i+1+1=2*i+2 by omega,grid_right,grid_even,rightDirection,forecastIncrement]
  exact rank_split (FractionalGaussianProcess.direction H hH0 hH1 (grid n i))
    (FractionalGaussianProcess.direction H hH0 hH1 (grid (n+1) (2*i+1)))
    (FractionalGaussianProcess.direction H hH0 hH1 (grid n (i+1)))
    (predictionDirection H hH0 hH1 (grid n i))
    (predictionDirection H hH0 hH1 (grid (n+1) (2*i+1)))

theorem field_step (n : ℕ) :
    dyadicField H hH0 hH1 (n+1)-dyadicField H hH0 hH1 n=
      (2:ℝ) • ∑ i ∈ Finset.range (2^n), rank (rightDirection H hH0 hH1 n i) (forecastIncrement H hH0 hH1 n i) := by
  rw [dyadicField,dyadicField,pow_succ,Nat.mul_comm (2^n) 2,sum_double,← Finset.sum_sub_distrib,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact term_split H hH0 hH1 n i

private theorem right_norm (n i : ℕ) : ‖rightDirection H hH0 hH1 n i‖=(rate H)^(n+1) := by
  rw [rightDirection,direction_norm]
  have hs : (grid n (i+1):ℝ)-grid (n+1) (2*i+1)=(1/2:ℝ)^(n+1) := by
    rw [← grid_right n i]
    simp only [grid,NNReal.coe_add,NNReal.coe_one,NNReal.coe_div,NNReal.coe_pow,
      Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    norm_num only [show ((2:ℝ≥0):ℝ)=(2:ℝ) from rfl]
    rw [div_pow,one_pow]
    field_simp
    ring
  rw [hs,abs_of_nonneg (by positivity)]
  exact (Real.rpow_pow_comm (by norm_num : 0≤(1/2:ℝ)) H (n+1)).symm

private theorem coefficient_orthogonal (n i j : ℕ) (hij : i≠j) :
    inner ℝ (forecastIncrement H hH0 hH1 n i) (forecastIncrement H hH0 hH1 n j)=0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact forecast_increment_orthogonal H hH0 hH1 (grid_left_le_half n i)
      (grid_half_le_next n hlt) (grid_left_le_half n j)
  · exact (real_inner_comm _ _).trans (forecast_increment_orthogonal H hH0 hH1
      (grid_left_le_half n j) (grid_half_le_next n hgt) (grid_left_le_half n i))

private theorem coefficient_energy (n : ℕ) :
    (∑ i ∈ Finset.range (2^n), ‖forecastIncrement H hH0 hH1 n i‖^2)≤1 :=
  forecast_energy_bound H hH0 hH1 (2^n) (grid n) (fun i => grid (n+1) (2*i+1))
    (fun i _ => grid_left_le_half n i) (fun _i _ _j _ hij => grid_half_le_next n hij)

private theorem rank_norm_sq (a b : CoefficientSpace) : ‖rank a b‖^2=‖a‖^2*‖b‖^2 := by
  rw [← real_inner_self_eq_norm_sq,rank_inner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  ring

theorem field_step_sq_bound (n : ℕ) :
    ‖dyadicField H hH0 hH1 (n+1)-dyadicField H hH0 hH1 n‖^2≤4*((rate H)^(n+1))^2 := by
  let v := fun i => rank (rightDirection H hH0 hH1 n i) (forecastIncrement H hH0 hH1 n i)
  have ho : ∀ i<2^n, ∀ j<2^n, i≠j → inner ℝ (v i) (v j)=0 := by
    intro i _ j _ hij
    rw [rank_inner,coefficient_orthogonal H hH0 hH1 n i j hij,zero_mul]
  have hs := orthogonal_sum_sq (2^n) v ho
  have he : ‖dyadicField H hH0 hH1 (n+1)-dyadicField H hH0 hH1 n‖^2=
      4*((rate H)^(n+1))^2*(∑ i ∈ Finset.range (2^n), ‖forecastIncrement H hH0 hH1 n i‖^2) := by
    rw [field_step,norm_smul,mul_pow]
    norm_num only [Real.norm_eq_abs]
    change 4*‖∑ i ∈ Finset.range (2^n), v i‖^2=_
    rw [hs]
    simp only [v,rank_norm_sq,right_norm]
    rw [← Finset.mul_sum]
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left (coefficient_energy H hH0 hH1 n) (by positivity)).trans_eq (mul_one _)

theorem field_step_bound (n : ℕ) :
    ‖dyadicField H hH0 hH1 (n+1)-dyadicField H hH0 hH1 n‖≤2*(rate H)^(n+1) := by
  have hb := field_step_sq_bound H hH0 hH1 n
  have hp : 0≤(rate H)^(n+1) := pow_nonneg (rate_pos H).le _
  nlinarith [norm_nonneg (dyadicField H hH0 hH1 (n+1)-dyadicField H hH0 hH1 n)]

theorem field_cauchy : CauchySeq (dyadicField H hH0 hH1) := by
  have hg := summable_geometric_of_lt_one (rate_pos H).le (rate_lt_one H hH0)
  have hs : Summable (fun n : ℕ => 2*(rate H)^(n+1)) := by
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hg.mul_left (2*rate H)
  have hd : Summable (fun n => dist (dyadicField H hH0 hH1 n) (dyadicField H hH0 hH1 (n+1))) := by
    apply Summable.of_nonneg_of_le (fun _ => dist_nonneg) _ hs
    intro n
    rw [dist_eq_norm,norm_sub_rev]
    exact field_step_bound H hH0 hH1 n
  exact cauchySeq_of_summable_dist hd

def predictiveField : GaussianVectorL2 := Classical.choose (cauchySeq_tendsto_of_complete (field_cauchy H hH0 hH1))

theorem field_tendsto : Tendsto (dyadicField H hH0 hH1) atTop (𝓝 (predictiveField H hH0 hH1)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (field_cauchy H hH0 hH1))

theorem field_linear : predictiveField H hH0 hH1 ∈ linearGaussianFields :=
  (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (field_tendsto H hH0 hH1)
    (Filter.Eventually.of_forall (field_mem_linear H hH0 hH1))

def predictiveIntegral : GaussianL2 := completedDivergence (predictiveField H hH0 hH1)

theorem integral_graph :
    (predictiveField H hH0 hH1,predictiveIntegral H hH0 hH1) ∈ hilbertDivergence.graph :=
  full_divergence_graph (field_linear H hH0 hH1)

theorem output_tendsto :
    Tendsto (fun n => conditionedOutput H hH0 hH1 (times n)) atTop (𝓝 (predictiveIntegral H hH0 hH1)) := by
  have ht := (completedDivergence.continuous.tendsto (predictiveField H hH0 hH1)).comp (field_tendsto H hH0 hH1)
  simpa only [Function.comp_def,finite_output,predictiveIntegral] using ht

theorem integral_error_lower :
    2*(correlation H hH0 hH1)^4 ≤ ‖predictiveIntegral H hH0 hH1-squareTarget H hH0 hH1‖^2 := by
  have ht := ((output_tendsto H hH0 hH1).sub (tendsto_const_nhds (x := squareTarget H hH0 hH1))).norm.pow 2
  exact ge_of_tendsto ht (Filter.Eventually.of_forall fun n => error_lower H hH0 hH1 (times n)
    (times_monotone n) (times_endpoints n).1 (times_endpoints n).2)

theorem integral_not_target (hH : H≠1/2) : predictiveIntegral H hH0 hH1≠squareTarget H hH0 hH1 := by
  intro he
  have ht := output_tendsto H hH0 hH1
  rw [he] at ht
  exact no_chronological_reconstruction H hH0 hH1 (fun n => 2^n) times times_monotone
    (fun n => (times_endpoints n).1) (fun n => (times_endpoints n).2) hH ht

theorem integral_centered : (∫ w,predictiveIntegral H hH0 hH1 w ∂gaussianProduct)=0 := by
  have hc := (GaussianDivergenceRecovery.exists_divergence_iff_centered (predictiveIntegral H hH0 hH1)).mp
    ⟨_,integral_graph H hH0 hH1⟩
  rwa [gaussianOne_inner_eq_integral] at hc

theorem integral_second_chaos : predictiveIntegral H hH0 hH1 ∈ GaussianNumberSectors.sector 2 :=
  completedDivergence_mem_sector_two (field_linear H hH0 hH1)

theorem times_step (n : ℕ) (i : Fin (2^n)) :
    (times n i.succ:ℝ)-times n i.castSucc=(1/2:ℝ)^n := by
  simp only [times,grid,Fin.val_succ,Fin.val_castSucc,NNReal.coe_add,NNReal.coe_one,NNReal.coe_div,
    NNReal.coe_pow,Nat.cast_add,Nat.cast_one]
  norm_num only [show ((2:ℝ≥0):ℝ)=(2:ℝ) from rfl]
  rw [div_pow,one_pow]
  field_simp
  ring

theorem mesh_zero : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem integral_pairing : inner ℝ (predictiveIntegral H hH0 hH1) (pastSquare H hH0 hH1)=
    4*(correlation H hH0 hH1)^2 := by
  have ht : Tendsto (fun n => inner ℝ (conditionedOutput H hH0 hH1 (times n)) (pastSquare H hH0 hH1))
      atTop (𝓝 (inner ℝ (predictiveIntegral H hH0 hH1) (pastSquare H hH0 hH1))) :=
    (output_tendsto H hH0 hH1).inner (tendsto_const_nhds (x := pastSquare H hH0 hH1))
  have hp (n : ℕ) := conditioned_pairing H hH0 hH1 (times n) (times_monotone n)
    (times_endpoints n).1 (times_endpoints n).2
  simp_rw [hp] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Mean-square convergence of the actual finite divergence-output representatives.
This is not convergence to the manuscript's proposed squareTarget. -/
theorem mean_square_output :
    Tendsto (fun n => ∫ w,‖conditionedOutput H hH0 hH1 (times n) w-predictiveIntegral H hH0 hH1 w‖^2
      ∂gaussianProduct) atTop (𝓝 0) := by
  have he (n : ℕ) : ‖conditionedOutput H hH0 hH1 (times n)-predictiveIntegral H hH0 hH1‖^2=
      ∫ w,‖conditionedOutput H hH0 hH1 (times n) w-predictiveIntegral H hH0 hH1 w‖^2 ∂gaussianProduct := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (conditionedOutput H hH0 hH1 (times n)) (predictiveIntegral H hH0 hH1)] with w hw
    simp only [Pi.sub_apply] at hw
    rw [hw]
  have ht := ((output_tendsto H hH0 hH1).sub
    (tendsto_const_nhds (x := predictiveIntegral H hH0 hH1))).norm.pow 2
  simpa only [he,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using ht

private theorem direction_mem_past (t r : ℝ≥0) (hr : r≤t) :
    FractionalGaussianProcess.direction H hH0 hH1 r ∈ past H hH0 hH1 t := by
  apply (Submodule.span ℝ (range (FractionalPredictionObstruction.pastDirections H hH0 hH1 t))).le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨⟨r,hr⟩,rfl⟩

private theorem mixed_in_past (a b : CoefficientSpace)
    (ha : a∈past H hH0 hH1 2) (hb : b∈past H hH0 hH1 2) :
    GaussianQuadraticSourceHodge.mixedTarget a b ∈
      generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 2) := by
  have hx : AEStronglyMeasurable[MeasurableSpace.comap
      (firstChaosFamily (FractionalPredictionObstruction.pastDirections H hH0 hH1 2)) inferInstance]
      (firstChaosEmbedding a) gaussianProduct := firstChaos_mem_generated_of_sourceSpan _ a ha
  have hy : AEStronglyMeasurable[MeasurableSpace.comap
      (firstChaosFamily (FractionalPredictionObstruction.pastDirections H hH0 hH1 2)) inferInstance]
      (firstChaosEmbedding b) gaussianProduct := firstChaos_mem_generated_of_sourceSpan _ b hb
  exact ((hx.mul hy).sub aestronglyMeasurable_const).congr
    (GaussianQuadraticSourceHodge.mixedTarget_coeFn a b).symm

private theorem finite_output_past (n : ℕ) : conditionedOutput H hH0 hH1 (times n) ∈
    generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 2) := by
  apply (generated _).sum_mem
  intro i _
  apply (generated _).smul_mem (2:ℝ)
  apply mixed_in_past H hH0 hH1
  · change (FractionalGaussianProcess.direction H hH0 hH1 (times n i.succ)-
      FractionalGaussianProcess.direction H hH0 hH1 (times n i.castSucc))∈past H hH0 hH1 2
    exact (past H hH0 hH1 2).sub_mem
      (direction_mem_past H hH0 hH1 2 _ ((times_monotone n (Fin.le_last _)).trans_eq (times_endpoints n).2))
      (direction_mem_past H hH0 hH1 2 _ ((times_monotone n (Fin.le_last _)).trans_eq (times_endpoints n).2))
  · exact past_mono H hH0 hH1
      ((times_monotone n (Fin.le_last _)).trans_eq (times_endpoints n).2)
      (forecast_mem H hH0 hH1 _)

theorem integral_mem_past : predictiveIntegral H hH0 hH1 ∈
    generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 2) :=
  (generated_isClosed _).mem_of_tendsto (output_tendsto H hH0 hH1)
    (Filter.Eventually.of_forall (finite_output_past H hH0 hH1))

theorem integral_observed : predictiveIntegral H hH0 hH1 =ᵐ[gaussianProduct]
    gaussianProduct[predictiveIntegral H hH0 hH1 | ContinuousFractionalPrediction.naturalPast H hH0 hH1 2] :=
  FractionalGridProjection.generator_coefficient_actual H hH0 hH1 2 _ (integral_mem_past H hH0 hH1)

theorem integral_observed_measurable :
    AEStronglyMeasurable[ContinuousFractionalPrediction.naturalPast H hH0 hH1 2]
      (predictiveIntegral H hH0 hH1) gaussianProduct := by
  have hm : AEStronglyMeasurable[ContinuousFractionalPrediction.naturalPast H hH0 hH1 2]
      (gaussianProduct[predictiveIntegral H hH0 hH1 |
        ContinuousFractionalPrediction.naturalPast H hH0 hH1 2]) gaussianProduct :=
    stronglyMeasurable_condExp.aestronglyMeasurable
  exact hm.congr (integral_observed H hH0 hH1).symm

/-- Reusable actual forecast-increment orthogonality for chronological refinements. -/
theorem prediction_increment_orthogonal {a b c d : ℝ≥0}
    (hab : a≤b) (hbc : b≤c) (hcd : c≤d) :
    inner ℝ (predictionDirection H hH0 hH1 b-predictionDirection H hH0 hH1 a)
      (predictionDirection H hH0 hH1 d-predictionDirection H hH0 hH1 c)=0 :=
  forecast_increment_orthogonal H hH0 hH1 hab hbc hcd

/-- Reusable finite-energy bound on the SAME actual full-past forecasts. -/
theorem prediction_energy_bound (N : ℕ) (a b : ℕ → ℝ≥0)
    (hab : ∀ i<N, a i≤b i) (hsep : ∀ i<N, ∀ j<N, i<j → b i≤a j) :
    (∑ i ∈ Finset.range N, ‖predictionDirection H hH0 hH1 (b i)-predictionDirection H hH0 hH1 (a i)‖^2)≤1 :=
  forecast_energy_bound H hH0 hH1 N a b hab hsep
/-- The covariance of the actual Gaussian forecast is its increasing variance clock. -/
theorem prediction_time_pairing (s t : ℝ≥0) :
    inner ℝ (predictionDirection H hH0 hH1 s) (predictionDirection H hH0 hH1 t)=
      ‖predictionDirection H hH0 hH1 (min s t)‖^2 := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst,real_inner_comm]
    have ht := forecast_pairing H hH0 hH1 t _
      (past_mono H hH0 hH1 hst (forecast_mem H hH0 hH1 s))
    have hs := forecast_pairing H hH0 hH1 s _ (forecast_mem H hH0 hH1 s)
    rw [real_inner_self_eq_norm_sq] at hs
    exact ht.trans hs.symm
  · rw [min_eq_right hts]
    have hs := forecast_pairing H hH0 hH1 s _
      (past_mono H hH0 hH1 hts (forecast_mem H hH0 hH1 t))
    have ht := forecast_pairing H hH0 hH1 t _ (forecast_mem H hH0 hH1 t)
    rw [real_inner_self_eq_norm_sq] at ht
    exact hs.trans ht.symm
end OperatorDerivativeRewrite.Foundation.FractionalPredictiveIntegral
