import Foundation.FractionalPredictivePartitions

/-! Deterministic within-cell forecast tags in the original fractional divergence.
Finite tagged fields need not be left-adapted. All integrals below are the
existing full Gaussian divergence, not uncorrected path products. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalPredictiveTags
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeFieldNorm
open FractionalCausalGridObstruction FractionalPredictiveIntegral FractionalPredictivePartitions
open GaussianLinearFieldDivergenceCompletion GaussianQuadraticSourceHodge
open StochasticCauchyFractionalDivergence FractionalGridProjection
variable (H : ℝ) (hH0 : 0<H) (hH1 : H<1)

private abbrev q (t : ℝ≥0) := predictionDirection H hH0 hH1 t
private def rank (a b : CoefficientSpace) : GaussianVectorL2 := scalarTensor a (firstChaosEmbedding b)
private theorem rank_sub (a b c : CoefficientSpace) : rank a (b-c)=rank a b-rank a c := by
  simp only [rank,map_sub]
private theorem rank_inner (a b c e : CoefficientSpace) :
    inner ℝ (rank a b) (rank c e)=inner ℝ b e*inner ℝ a c := by
  rw [rank,rank,scalarTensor_pair_inner,firstChaosEmbedding.inner_map_map]

def taggedField {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0) : GaussianVectorL2 :=
  ∑ i : Fin n,(2:ℝ) • rank (cellDirection H hH0 hH1 τ i) (q H hH0 hH1 (ξ i))

def taggedOutput {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0) : GaussianL2 :=
  ∑ i : Fin n,(2:ℝ) • mixedTarget (cellDirection H hH0 hH1 τ i) (q H hH0 hH1 (ξ i))

/-- All selected chronological forecast subincrements together have energy at most1. -/
theorem tag_energy_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0)
    (hm : Monotone τ) (hl : ∀ i,τ i.castSucc≤ξ i) (hr : ∀ i,ξ i≤τ i.succ) :
    (∑ i : Fin n,‖q H hH0 hH1 (ξ i)-q H hH0 hH1 (τ i.castSucc)‖^2)≤1 := by
  let a : ℕ → ℝ≥0 := fun i => if hi : i<n then τ (Fin.castSucc ⟨i,hi⟩) else 0
  let b : ℕ → ℝ≥0 := fun i => if hi : i<n then ξ ⟨i,hi⟩ else 0
  have he := prediction_energy_bound H hH0 hH1 n a b
    (fun i hi => by simpa only [a,b,dite_eq_left hi] using hl ⟨i,hi⟩)
    (fun i hi j hj hij => by
      simp only [a,b,dite_eq_left hi,dite_eq_left hj]
      exact (hr ⟨i,hi⟩).trans (hm (Fin.succ_le_castSucc_iff.mpr hij)))
  rw [← Fin.sum_univ_eq_sum_range] at he
  simpa only [a,b,dite_eq_left,Fin.is_lt] using he

private theorem tag_orthogonal {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0)
    (hm : Monotone τ) (hl : ∀ i,τ i.castSucc≤ξ i) (hr : ∀ i,ξ i≤τ i.succ)
    (i j : Fin n) (hij : i≠j) :
    inner ℝ (q H hH0 hH1 (ξ i)-q H hH0 hH1 (τ i.castSucc))
      (q H hH0 hH1 (ξ j)-q H hH0 hH1 (τ j.castSucc))=0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact prediction_increment_orthogonal H hH0 hH1 (hl i)
      ((hr i).trans (hm (Fin.succ_le_castSucc_iff.mpr hlt))) (hl j)
  · exact (real_inner_comm _ _).trans (prediction_increment_orthogonal H hH0 hH1 (hl j)
      ((hr j).trans (hm (Fin.succ_le_castSucc_iff.mpr hgt))) (hl i))

private theorem field_difference {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0) :
    taggedField H hH0 hH1 τ ξ-conditionedField H hH0 hH1 τ=
      (2:ℝ) • (∑ i : Fin n,rank (cellDirection H hH0 hH1 τ i)
        (q H hH0 hH1 (ξ i)-q H hH0 hH1 (τ i.castSucc))) := by
  simp only [taggedField,conditionedField,predictedValue,rank,q,map_sub,
    Finset.smul_sum,smul_sub,Finset.sum_sub_distrib]

theorem tag_difference_sq {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0)
    (hm : Monotone τ) (hl : ∀ i,τ i.castSucc≤ξ i) (hr : ∀ i,ξ i≤τ i.succ) :
    ‖taggedField H hH0 hH1 τ ξ-conditionedField H hH0 hH1 τ‖^2=
      4*(∑ i : Fin n,‖cellDirection H hH0 hH1 τ i‖^2*
        ‖q H hH0 hH1 (ξ i)-q H hH0 hH1 (τ i.castSucc)‖^2) := by
  rw [field_difference,norm_smul,mul_pow]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2),show (2:ℝ)^2=4 by norm_num]
  congr 1
  rw [← real_inner_self_eq_norm_sq,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum,Finset.sum_eq_single i]
  · rw [rank_inner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,mul_comm]
  · intro j _ hji
    rw [rank_inner,tag_orthogonal H hH0 hH1 τ ξ hm hl hr i j hji.symm,zero_mul]
  · simp

private theorem cell_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hm : Monotone τ)
    (ε : ℝ) (hε : 0≤ε) (hmesh : ∀ i : Fin n,(τ i.succ:ℝ)-τ i.castSucc≤ε) (i : Fin n) :
    ‖cellDirection H hH0 hH1 τ i‖≤ε^H := by
  have he := FractionalGaussianProcess.value_increment_norm H hH0 hH1 (τ i.castSucc) (τ i.succ)
  rw [FractionalGaussianProcess.value,FractionalGaussianProcess.value,← map_sub,firstChaosEmbedding.norm_map] at he
  rw [cellDirection,he,abs_of_nonneg (sub_nonneg.mpr (show (τ i.castSucc:ℝ)≤τ i.succ from hm (Fin.castSucc_le_succ i)))]
  exact Real.rpow_le_rpow (sub_nonneg.mpr (show (τ i.castSucc:ℝ)≤τ i.succ from hm (Fin.castSucc_le_succ i))) (hmesh i) hH0.le

theorem tag_distance_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0)
    (hm : Monotone τ) (hl : ∀ i,τ i.castSucc≤ξ i) (hr : ∀ i,ξ i≤τ i.succ)
    (ε : ℝ) (hε : 0≤ε) (hmesh : ∀ i : Fin n,(τ i.succ:ℝ)-τ i.castSucc≤ε) :
    ‖taggedField H hH0 hH1 τ ξ-conditionedField H hH0 hH1 τ‖≤2*ε^H := by
  have hs : (∑ i : Fin n,‖cellDirection H hH0 hH1 τ i‖^2*
      ‖q H hH0 hH1 (ξ i)-q H hH0 hH1 (τ i.castSucc)‖^2)≤(ε^H)^2 := by
    calc
      _≤∑ i : Fin n,(ε^H)^2*‖q H hH0 hH1 (ξ i)-q H hH0 hH1 (τ i.castSucc)‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hε H)).mpr (cell_bound H hH0 hH1 τ hm ε hε hmesh i)) (sq_nonneg _)
      _=(ε^H)^2*(∑ i : Fin n,‖q H hH0 hH1 (ξ i)-q H hH0 hH1 (τ i.castSucc)‖^2) := by rw [Finset.mul_sum]
      _≤(ε^H)^2*1 := mul_le_mul_of_nonneg_left (tag_energy_bound H hH0 hH1 τ ξ hm hl hr) (sq_nonneg _)
      _=(ε^H)^2 := mul_one _
  have he := tag_difference_sq H hH0 hH1 τ ξ hm hl hr
  nlinarith [Real.rpow_nonneg hε H,norm_nonneg (taggedField H hH0 hH1 τ ξ-conditionedField H hH0 hH1 τ)]

theorem tagged_field_linear {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0) :
    taggedField H hH0 hH1 τ ξ∈linearGaussianFields := by
  apply linearGaussianFields.sum_mem
  intro i _
  exact linearGaussianFields.smul_mem (2:ℝ) (linear_rank_mem _ _)

theorem tagged_output_identity {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0) :
    completedDivergence (taggedField H hH0 hH1 τ ξ)=taggedOutput H hH0 hH1 τ ξ := by
  simp only [taggedField,taggedOutput,rank,map_sum,map_smul,completedDivergence_rank]

theorem tagged_graph {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0) :
    (taggedField H hH0 hH1 τ ξ,taggedOutput H hH0 hH1 τ ξ)∈hilbertDivergence.graph := by
  have he := full_divergence_graph (tagged_field_linear H hH0 hH1 τ ξ)
  rwa [tagged_output_identity] at he

theorem tag_field_limit_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0)
    (hm : Monotone τ) (hl : ∀ i,τ i.castSucc≤ξ i) (hr : ∀ i,ξ i≤τ i.succ)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) (ε : ℝ) (hε : 0≤ε)
    (hmesh : ∀ i : Fin n,(τ i.succ:ℝ)-τ i.castSucc≤ε) :
    ‖taggedField H hH0 hH1 τ ξ-predictiveField H hH0 hH1‖≤4*ε^H := by
  calc
    _=‖(taggedField H hH0 hH1 τ ξ-conditionedField H hH0 hH1 τ)+
        (conditionedField H hH0 hH1 τ-predictiveField H hH0 hH1)‖ := by congr 1; abel
    _≤‖taggedField H hH0 hH1 τ ξ-conditionedField H hH0 hH1 τ‖+
        ‖conditionedField H hH0 hH1 τ-predictiveField H hH0 hH1‖ := norm_add_le _ _
    _≤4*ε^H := by linarith [tag_distance_bound H hH0 hH1 τ ξ hm hl hr ε hε hmesh,
      field_limit_bound H hH0 hH1 τ hm h0 hT ε hε hmesh]

theorem tag_output_limit_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0)
    (hm : Monotone τ) (hl : ∀ i,τ i.castSucc≤ξ i) (hr : ∀ i,ξ i≤τ i.succ)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) (ε : ℝ) (hε : 0≤ε)
    (hmesh : ∀ i : Fin n,(τ i.succ:ℝ)-τ i.castSucc≤ε) :
    ‖taggedOutput H hH0 hH1 τ ξ-predictiveIntegral H hH0 hH1‖≤4*Real.sqrt 2*ε^H := by
  have hb := completed_norm_bound (linearGaussianFields.sub_mem
    (tagged_field_linear H hH0 hH1 τ ξ) (field_linear H hH0 hH1))
  rw [map_sub,tagged_output_identity] at hb
  change ‖taggedOutput H hH0 hH1 τ ξ-predictiveIntegral H hH0 hH1‖≤
    Real.sqrt 2*‖taggedField H hH0 hH1 τ ξ-predictiveField H hH0 hH1‖ at hb
  calc
    _≤Real.sqrt 2*‖taggedField H hH0 hH1 τ ξ-predictiveField H hH0 hH1‖ := hb
    _≤Real.sqrt 2*(4*ε^H) := mul_le_mul_of_nonneg_left
      (tag_field_limit_bound H hH0 hH1 τ ξ hm hl hr h0 hT ε hε hmesh) (Real.sqrt_nonneg 2)
    _=4*Real.sqrt 2*ε^H := by ring

theorem tagged_field_tendsto (N : ℕ → ℕ) (τ : (j : ℕ) → Fin (N j+1) → ℝ≥0)
    (ξ : (j : ℕ) → Fin (N j) → ℝ≥0) (hm : ∀ j,Monotone (τ j))
    (hl : ∀ j i,τ j i.castSucc≤ξ j i) (hr : ∀ j i,ξ j i≤τ j i.succ)
    (h0 : ∀ j,τ j 0=1) (hT : ∀ j,τ j (Fin.last (N j))=2)
    (ε : ℕ → ℝ) (hε : ∀ j,0≤ε j) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ j (i : Fin (N j)),(τ j i.succ:ℝ)-τ j i.castSucc≤ε j) :
    Tendsto (fun j => taggedField H hH0 hH1 (τ j) (ξ j)) atTop (𝓝 (predictiveField H hH0 hH1)) := by
  have hp : Tendsto (fun j => (ε j)^H) atTop (𝓝 0) := by
    have hh := (Real.continuous_rpow_const hH0.le).continuousAt.tendsto.comp hlim
    simpa only [Function.comp_def,Real.zero_rpow (ne_of_gt hH0)] using hh
  have hc : Tendsto (fun j => 4*(ε j)^H) atTop (𝓝 0) := by simpa only [mul_zero] using hp.const_mul 4
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun j => tag_field_limit_bound H hH0 hH1 (τ j) (ξ j)
    (hm j) (hl j) (hr j) (h0 j) (hT j) (ε j) (hε j) (hmesh j)) hc

theorem tagged_output_tendsto (N : ℕ → ℕ) (τ : (j : ℕ) → Fin (N j+1) → ℝ≥0)
    (ξ : (j : ℕ) → Fin (N j) → ℝ≥0) (hm : ∀ j,Monotone (τ j))
    (hl : ∀ j i,τ j i.castSucc≤ξ j i) (hr : ∀ j i,ξ j i≤τ j i.succ)
    (h0 : ∀ j,τ j 0=1) (hT : ∀ j,τ j (Fin.last (N j))=2)
    (ε : ℕ → ℝ) (hε : ∀ j,0≤ε j) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ j (i : Fin (N j)),(τ j i.succ:ℝ)-τ j i.castSucc≤ε j) :
    Tendsto (fun j => taggedOutput H hH0 hH1 (τ j) (ξ j)) atTop (𝓝 (predictiveIntegral H hH0 hH1)) := by
  have ht := (completedDivergence.continuous.tendsto (predictiveField H hH0 hH1)).comp
    (tagged_field_tendsto H hH0 hH1 N τ ξ hm hl hr h0 hT ε hε hlim hmesh)
  simpa only [Function.comp_def,tagged_output_identity,predictiveIntegral] using ht

theorem tagged_left_field {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    taggedField H hH0 hH1 τ (fun i => τ i.castSucc)=conditionedField H hH0 hH1 τ := rfl

theorem tagged_left_output {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    taggedOutput H hH0 hH1 τ (fun i => τ i.castSucc)=conditionedOutput H hH0 hH1 τ := rfl

/-- Actual finite Wick-compensated stochastic sums, before any limiting argument. -/
theorem tagged_output_actual {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0) :
    taggedOutput H hH0 hH1 τ ξ =ᵐ[gaussianProduct] fun w =>
      ∑ i : Fin n,2*(firstChaosEmbedding (cellDirection H hH0 hH1 τ i) w*
        predictedValue H hH0 hH1 (ξ i) w-
        inner ℝ (cellDirection H hH0 hH1 τ i) (q H hH0 hH1 (ξ i))) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n => (2:ℝ) •
      mixedTarget (cellDirection H hH0 hH1 τ i) (q H hH0 hH1 (ξ i))),
    ae_all_iff.mpr (fun i : Fin n => Lp.coeFn_smul (2:ℝ)
      (mixedTarget (cellDirection H hH0 hH1 τ i) (q H hH0 hH1 (ξ i)))),
    ae_all_iff.mpr (fun i : Fin n => mixedTarget_coeFn (cellDirection H hH0 hH1 τ i)
      (q H hH0 hH1 (ξ i)))] with w hsum hsm hm
  change taggedOutput H hH0 hH1 τ ξ w=_ at hsum
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsm i]
  simp only [Pi.smul_apply,smul_eq_mul,hm i,predictedValue,q]

/-- The coefficients really are conditional expectations in the constructed
continuous fBM observed past at the DETERMINISTIC selected tags. -/
theorem tagged_output_conditional {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0) :
    taggedOutput H hH0 hH1 τ ξ =ᵐ[gaussianProduct] fun w =>
      ∑ i : Fin n,2*(firstChaosEmbedding (cellDirection H hH0 hH1 τ i) w*
        gaussianProduct[firstChaosEmbedding (StochasticCauchyFractionalDivergence.fractionalIncrement H hH0 hH1) |
          ContinuousFractionalPrediction.naturalPast H hH0 hH1 (ξ i)] w-
        inner ℝ (cellDirection H hH0 hH1 τ i) (q H hH0 hH1 (ξ i))) := by
  refine (tagged_output_actual H hH0 hH1 τ ξ).trans ?_
  filter_upwards [ae_all_iff.mpr (fun i : Fin n => predictedValue_actual H hH0 hH1 (ξ i))] with w hw
  apply Finset.sum_congr rfl
  intro i _
  rw [hw i]

theorem tagged_mean_square (N : ℕ → ℕ) (τ : (j : ℕ) → Fin (N j+1) → ℝ≥0)
    (ξ : (j : ℕ) → Fin (N j) → ℝ≥0) (hm : ∀ j,Monotone (τ j))
    (hl : ∀ j i,τ j i.castSucc≤ξ j i) (hr : ∀ j i,ξ j i≤τ j i.succ)
    (h0 : ∀ j,τ j 0=1) (hT : ∀ j,τ j (Fin.last (N j))=2)
    (ε : ℕ → ℝ) (hε : ∀ j,0≤ε j) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ j (i : Fin (N j)),(τ j i.succ:ℝ)-τ j i.castSucc≤ε j) :
    Tendsto (fun j => ∫ w,‖taggedOutput H hH0 hH1 (τ j) (ξ j) w-predictiveIntegral H hH0 hH1 w‖^2
      ∂gaussianProduct) atTop (𝓝 0) := by
  have he (j : ℕ) : ‖taggedOutput H hH0 hH1 (τ j) (ξ j)-predictiveIntegral H hH0 hH1‖^2=
      ∫ w,‖taggedOutput H hH0 hH1 (τ j) (ξ j) w-predictiveIntegral H hH0 hH1 w‖^2 ∂gaussianProduct := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (taggedOutput H hH0 hH1 (τ j) (ξ j)) (predictiveIntegral H hH0 hH1)] with w hw
    simp only [Pi.sub_apply] at hw
    rw [hw]
  have ht := ((tagged_output_tendsto H hH0 hH1 N τ ξ hm hl hr h0 hT ε hε hlim hmesh).sub
    (tendsto_const_nhds (x := predictiveIntegral H hH0 hH1))).norm.pow 2
  simpa only [he,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using ht

/-- Every tag at or after1 retains the same nonzero past-square defect;
no chronological mesh assumption is needed for this finite obstruction. -/
theorem tagged_pairing {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) (hξ : ∀ i,1≤ξ i) :
    inner ℝ (taggedOutput H hH0 hH1 τ ξ) (pastSquare H hH0 hH1)=
      4*(correlation H hH0 hH1)^2 := by
  have hp (i : Fin n) : inner ℝ (predictionDirection H hH0 hH1 (ξ i))
      (fractionalPast H hH0 hH1)=correlation H hH0 hH1 :=
    prediction_pairing H hH0 hH1 _ (hξ i)
  rw [taggedOutput,sum_inner,pastSquare]
  simp only [real_inner_smul_left,mixed_square_pairing,q,hp]
  have hs : (∑ i : Fin n, inner ℝ (cellDirection H hH0 hH1 τ i) (fractionalPast H hH0 hH1))=
      correlation H hH0 hH1 := by
    rw [← sum_inner,cells_telescope H hH0 hH1 τ h0 hT]
    exact real_inner_comm _ _
  calc
    (∑ i : Fin n, 2*(2*inner ℝ (cellDirection H hH0 hH1 τ i) (fractionalPast H hH0 hH1)*correlation H hH0 hH1))=
        4*correlation H hH0 hH1*(∑ i : Fin n, inner ℝ (cellDirection H hH0 hH1 τ i) (fractionalPast H hH0 hH1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=4*(correlation H hH0 hH1)^2 := by rw [hs]; ring

theorem tagged_error_lower {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ξ : Fin n → ℝ≥0)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) (hξ : ∀ i,1≤ξ i) :
    2*(correlation H hH0 hH1)^4 ≤ ‖taggedOutput H hH0 hH1 τ ξ-squareTarget H hH0 hH1‖^2 := by
  have hp : inner ℝ (taggedOutput H hH0 hH1 τ ξ-squareTarget H hH0 hH1) (pastSquare H hH0 hH1)=
      2*(correlation H hH0 hH1)^2 := by
    rw [inner_sub_left,tagged_pairing H hH0 hH1 τ ξ h0 hT hξ,target_pairing]
    ring
  have hb := real_inner_mul_inner_self_le
    (taggedOutput H hH0 hH1 τ ξ-squareTarget H hH0 hH1) (pastSquare H hH0 hH1)
  rw [hp,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,pastSquare_energy] at hb
  nlinarith

end OperatorDerivativeRewrite.Foundation.FractionalPredictiveTags
