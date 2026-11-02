import Foundation.FractionalAdaptedAdjointObstruction
import Foundation.GaussianBrownianQuadraticVariation

/-! Actual conditional left-grid divergence outputs fail to reconstruct a
fractional centered square. This is a chronological L2 obstruction, not a
claim that an arbitrary continuous conditional map has been constructed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalCausalGridObstruction
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeFieldNorm
open StochasticCauchyFractionalDivergence FractionalGridProjection
open GaussianConditionalGraph GaussianWickConditionalProjection GaussianQuadraticSourceHodge
variable (H : ℝ) (hH0 : 0<H) (hH1 : H<1)

def predictionDirection (t : ℝ≥0) : CoefficientSpace :=
  sourceProjection (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)
    (fractionalIncrement H hH0 hH1)
def predictedValue (t : ℝ≥0) : GaussianL2 := firstChaosEmbedding (predictionDirection H hH0 hH1 t)
def cellDirection {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (i : Fin n) : CoefficientSpace :=
  FractionalGaussianProcess.direction H hH0 hH1 (τ i.succ)-
    FractionalGaussianProcess.direction H hH0 hH1 (τ i.castSucc)
def conditionedField {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : GaussianVectorL2 :=
  ∑ i : Fin n, (2:ℝ) • scalarTensor (cellDirection H hH0 hH1 τ i)
    (predictedValue H hH0 hH1 (τ i.castSucc))
def conditionedOutput {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : GaussianL2 :=
  ∑ i : Fin n, (2:ℝ) • mixedTarget (cellDirection H hH0 hH1 τ i)
    (predictionDirection H hH0 hH1 (τ i.castSucc))
def squareTarget : GaussianL2 := mixedTarget (fractionalIncrement H hH0 hH1) (fractionalIncrement H hH0 hH1)
def pastSquare : GaussianL2 := mixedTarget (fractionalPast H hH0 hH1) (fractionalPast H hH0 hH1)

private theorem past_unit : inner ℝ (fractionalPast H hH0 hH1) (fractionalPast H hH0 hH1)=1 := by
  simp only [fractionalPast,FractionalWickCovariance.direction_inner,FractionalSpectralGeometry.covariance]
  norm_num [Real.zero_rpow (by linarith : 2*H≠0)]
private theorem increment_unit :
    inner ℝ (fractionalIncrement H hH0 hH1) (fractionalIncrement H hH0 hH1)=1 := by
  simp only [fractionalIncrement,fractionalPast,inner_sub_left,inner_sub_right,
    FractionalWickCovariance.direction_inner,FractionalSpectralGeometry.covariance]
  norm_num [Real.zero_rpow (by linarith : 2*H≠0)]
  ring

/-- Generic exact mixed-second-chaos/square pairing from the ORIGINAL adjoint graphs. -/
theorem mixed_square_pairing (a b h : CoefficientSpace) :
    inner ℝ (mixedTarget a b) (mixedTarget h h)=2*inner ℝ a h*inner ℝ b h := by
  have hd := GaussianNumberSectors.graph_duality (mixed_derivative_graph h h) (mixed_divergence_graph a b)
  simp only [inner_add_left,scalarTensor_pair_inner,firstChaosEmbedding.inner_map_map] at hd
  have ha : inner ℝ h a=inner ℝ a h := real_inner_comm _ _
  have hb : inner ℝ h b=inner ℝ b h := real_inner_comm _ _
  rw [ha,hb] at hd
  calc
    inner ℝ (mixedTarget a b) (mixedTarget h h)=inner ℝ (mixedTarget h h) (mixedTarget a b) := real_inner_comm _ _
    _=2*inner ℝ a h*inner ℝ b h := by rw [← hd]; ring

theorem square_derivative_graph :
    (squareTarget H hH0 hH1,(2:ℝ) • scalarTensor (fractionalIncrement H hH0 hH1)
      (firstChaosEmbedding (fractionalIncrement H hH0 hH1))) ∈ closedCylindricalDerivative.graph := by
  simpa only [two_smul,squareTarget] using mixed_derivative_graph
    (fractionalIncrement H hH0 hH1) (fractionalIncrement H hH0 hH1)

theorem square_target_actual : squareTarget H hH0 hH1 =ᵐ[gaussianProduct]
    fun w => (firstChaosEmbedding (fractionalIncrement H hH0 hH1) w)^2-1 := by
  filter_upwards [mixedTarget_coeFn (fractionalIncrement H hH0 hH1) (fractionalIncrement H hH0 hH1)] with w hw
  change mixedTarget _ _ w= _
  rw [hw,increment_unit]
  ring

theorem predictedValue_actual (t : ℝ≥0) : predictedValue H hH0 hH1 t =ᵐ[gaussianProduct]
    gaussianProduct[firstChaosEmbedding (fractionalIncrement H hH0 hH1) |
      ContinuousFractionalPrediction.naturalPast H hH0 hH1 t] := by
  rw [predictedValue,predictionDirection,← conditional_firstChaos_projection]
  exact ContinuousFractionalPrediction.conditionalProjection_actual_past H hH0 hH1 t _

theorem prediction_pairing (t : ℝ≥0) (ht : 1≤t) :
    inner ℝ (predictionDirection H hH0 hH1 t) (fractionalPast H hH0 hH1)=correlation H hH0 hH1 := by
  have hp := sourceProjection_pairing (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)
    (fractionalIncrement H hH0 hH1) (⟨1,ht⟩ : Iic t)
  change inner ℝ (predictionDirection H hH0 hH1 t) (fractionalPast H hH0 hH1)=
    inner ℝ (fractionalIncrement H hH0 hH1) (fractionalPast H hH0 hH1) at hp
  exact hp.trans (real_inner_comm _ _)

/-- Every finite candidate is already in the EXISTING full divergence domain. -/
theorem conditioned_graph {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    (conditionedField H hH0 hH1 τ,conditionedOutput H hH0 hH1 τ) ∈ hilbertDivergence.graph := by
  have hg (i : Fin n) :
      ((2:ℝ) • scalarTensor (cellDirection H hH0 hH1 τ i) (predictedValue H hH0 hH1 (τ i.castSucc)),
        (2:ℝ) • mixedTarget (cellDirection H hH0 hH1 τ i)
          (predictionDirection H hH0 hH1 (τ i.castSucc))) ∈ hilbertDivergence.graph := by
    simpa only [Prod.smul_mk,predictedValue] using
      hilbertDivergence.graph.smul_mem (2:ℝ)
        (mixed_divergence_graph (cellDirection H hH0 hH1 τ i)
          (predictionDirection H hH0 hH1 (τ i.castSucc)))
  simpa only [conditionedField,conditionedOutput,prod_mk_sum] using
    hilbertDivergence.graph.sum_mem (t := Finset.univ) (fun i _ => hg i)

theorem cells_telescope {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (h0 : τ 0=1) (hT : τ (Fin.last n)=2) :
    ∑ i : Fin n, cellDirection H hH0 hH1 τ i=fractionalIncrement H hH0 hH1 := by
  let d : Fin (n+1) → CoefficientSpace := fun i => FractionalGaussianProcess.direction H hH0 hH1 (τ i)
  have hs := Fin.sum_univ_succ d
  have hc := Fin.sum_univ_castSucc d
  have hsucc : (∑ i : Fin n, d i.succ)=(∑ i, d i)-d 0 :=
    eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact hs.symm)
  have hcast : (∑ i : Fin n, d i.castSucc)=(∑ i, d i)-d (Fin.last n) :=
    eq_sub_iff_add_eq.mpr hc.symm
  simp only [cellDirection,Finset.sum_sub_distrib]
  change (∑ i : Fin n, d i.succ)-(∑ i : Fin n, d i.castSucc)=_
  rw [hsucc,hcast]
  simp only [d,h0,hT,fractionalIncrement,fractionalPast]
  abel

/-- Before conditioning, these are exact finite decompositions of D(squareTarget). -/
theorem raw_derivative_partition {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) :
    (∑ i : Fin n, (2:ℝ) • scalarTensor (cellDirection H hH0 hH1 τ i)
      (firstChaosEmbedding (fractionalIncrement H hH0 hH1)))=
      (2:ℝ) • scalarTensor (fractionalIncrement H hH0 hH1)
        (firstChaosEmbedding (fractionalIncrement H hH0 hH1)) := by
  rw [← Finset.smul_sum]
  congr 1
  apply Lp.ext
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n =>
      scalarTensor (cellDirection H hH0 hH1 τ i) (firstChaosEmbedding (fractionalIncrement H hH0 hH1))),
    ae_all_iff.mpr (fun i : Fin n => scalarTensor_coeFn (cellDirection H hH0 hH1 τ i)
      (firstChaosEmbedding (fractionalIncrement H hH0 hH1))),
    scalarTensor_coeFn (fractionalIncrement H hH0 hH1)
      (firstChaosEmbedding (fractionalIncrement H hH0 hH1))] with w hs ht hk
  rw [hs,hk]
  simp only [Finset.sum_apply]
  change (∑ i : Fin n, scalarTensor (cellDirection H hH0 hH1 τ i)
    (firstChaosEmbedding (fractionalIncrement H hH0 hH1)) w)=_
  calc
    (∑ i : Fin n, scalarTensor (cellDirection H hH0 hH1 τ i)
        (firstChaosEmbedding (fractionalIncrement H hH0 hH1)) w)=
      ∑ i : Fin n, firstChaosEmbedding (fractionalIncrement H hH0 hH1) w • cellDirection H hH0 hH1 τ i := by
        apply Finset.sum_congr rfl
        intro i _
        exact ht i
    _=_ := by rw [← Finset.smul_sum,cells_telescope H hH0 hH1 τ h0 hT]

theorem target_pairing : inner ℝ (squareTarget H hH0 hH1) (pastSquare H hH0 hH1)=
    2*(correlation H hH0 hH1)^2 := by
  rw [squareTarget,pastSquare,mixed_square_pairing]
  have hc : inner ℝ (fractionalIncrement H hH0 hH1) (fractionalPast H hH0 hH1)=correlation H hH0 hH1 :=
    real_inner_comm _ _
  rw [hc]
  ring

theorem pastSquare_energy : ‖pastSquare H hH0 hH1‖^2=2 := by
  rw [← real_inner_self_eq_norm_sq,pastSquare,mixed_square_pairing,past_unit]
  norm_num

/-- Exact mismatch for EVERY chronological partition, not just one coarse grid. -/
theorem conditioned_pairing {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) :
    inner ℝ (conditionedOutput H hH0 hH1 τ) (pastSquare H hH0 hH1)=
      4*(correlation H hH0 hH1)^2 := by
  have hp (i : Fin n) : inner ℝ (predictionDirection H hH0 hH1 (τ i.castSucc))
      (fractionalPast H hH0 hH1)=correlation H hH0 hH1 :=
    prediction_pairing H hH0 hH1 _ (h0 ▸ hτ (Fin.zero_le _))
  rw [conditionedOutput,sum_inner,pastSquare]
  simp only [real_inner_smul_left,mixed_square_pairing,hp]
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

theorem error_lower {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) :
    2*(correlation H hH0 hH1)^4 ≤ ‖conditionedOutput H hH0 hH1 τ-squareTarget H hH0 hH1‖^2 := by
  have hp : inner ℝ (conditionedOutput H hH0 hH1 τ-squareTarget H hH0 hH1) (pastSquare H hH0 hH1)=
      2*(correlation H hH0 hH1)^2 := by
    rw [inner_sub_left,conditioned_pairing H hH0 hH1 τ hτ h0 hT,target_pairing]
    ring
  have hb := real_inner_mul_inner_self_le
    (conditionedOutput H hH0 hH1 τ-squareTarget H hH0 hH1) (pastSquare H hH0 hH1)
  rw [hp,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,pastSquare_energy] at hb
  nlinarith

theorem no_chronological_reconstruction (N : ℕ → ℕ) (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0)
    (hτ : ∀ m, Monotone (τ m)) (h0 : ∀ m, τ m 0=1) (hT : ∀ m, τ m (Fin.last (N m))=2)
    (hH : H≠1/2) :
    ¬ Tendsto (fun m => conditionedOutput H hH0 hH1 (τ m)) atTop (𝓝 (squareTarget H hH0 hH1)) := by
  intro ht
  have hz : Tendsto (fun m => ‖conditionedOutput H hH0 hH1 (τ m)-squareTarget H hH0 hH1‖^2)
      atTop (𝓝 (0:ℝ)) := by
    simpa using
      (ht.sub (tendsto_const_nhds (x := squareTarget H hH0 hH1))).norm.pow 2
  have hb : 2*(correlation H hH0 hH1)^4≤0 :=
    ge_of_tendsto hz (Filter.Eventually.of_forall (fun m => error_lower H hH0 hH1 (τ m) (hτ m) (h0 m) (hT m)))
  have hc : correlation H hH0 hH1≠0 := fun he => hH ((correlation_zero_iff H hH0 hH1).mp he)
  have hp : 0<2*(correlation H hH0 hH1)^4 := by positivity
  linarith

def uniformGrid (n : ℕ) : Fin (n+2) → ℝ≥0 :=
  fun i => 1+GaussianBrownianQuadraticVariation.uniformTime 1 n i

theorem uniformGrid_monotone (n : ℕ) : Monotone (uniformGrid n) := by
  intro i j hij
  simpa only [uniformGrid,add_comm] using
    add_le_add_left (GaussianBrownianQuadraticVariation.uniformTime_monotone 1 n hij) 1

theorem uniformGrid_endpoints (n : ℕ) : uniformGrid n 0=1 ∧ uniformGrid n (Fin.last (n+1))=2 := by
  simp only [uniformGrid,(GaussianBrownianQuadraticVariation.uniformTime_endpoints 1 n).1,
    (GaussianBrownianQuadraticVariation.uniformTime_endpoints 1 n).2]
  norm_num

theorem uniformGrid_step (n : ℕ) (i : Fin (n+1)) :
    (uniformGrid n i.succ : ℝ)-uniformGrid n i.castSucc=1/((n:ℝ)+1) := by
  have hs := GaussianBrownianQuadraticVariation.uniformTime_step 1 n i
  simp only [uniformGrid,NNReal.coe_add,NNReal.coe_one]
  norm_num only [NNReal.coe_one] at hs
  linarith

theorem uniformGrid_mesh_zero : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem uniform_no_reconstruction (hH : H≠1/2) :
    ¬ Tendsto (fun n => conditionedOutput H hH0 hH1 (uniformGrid n)) atTop (𝓝 (squareTarget H hH0 hH1)) :=
  no_chronological_reconstruction H hH0 hH1 (fun n => n+1) uniformGrid uniformGrid_monotone
    (fun n => (uniformGrid_endpoints n).1) (fun n => (uniformGrid_endpoints n).2) hH

/-- The factor2 is retained inside the ACTUAL conditional coefficient. -/
theorem conditioned_coefficient_actual (t : ℝ≥0) :
    ((2:ℝ) • predictedValue H hH0 hH1 t : GaussianL2) =ᵐ[gaussianProduct]
      gaussianProduct[((2:ℝ) • firstChaosEmbedding (fractionalIncrement H hH0 hH1) : GaussianL2) |
        ContinuousFractionalPrediction.naturalPast H hH0 hH1 t] := by
  have ha := ContinuousFractionalPrediction.conditionalProjection_actual_past H hH0 hH1 t
    ((2:ℝ) • firstChaosEmbedding (fractionalIncrement H hH0 hH1))
  rw [map_smul,conditional_firstChaos_projection] at ha
  exact ha

theorem target_centered : (∫ w,squareTarget H hH0 hH1 w ∂gaussianProduct)=0 := by
  have hc := (GaussianDivergenceRecovery.exists_divergence_iff_centered (squareTarget H hH0 hH1)).mp
    ⟨_,mixed_divergence_graph (fractionalIncrement H hH0 hH1) (fractionalIncrement H hH0 hH1)⟩
  rwa [gaussianOne_inner_eq_integral] at hc

/-- Y is the existing genuine process increment, not merely a new Gaussian variable. -/
theorem increment_actual : firstChaosEmbedding (fractionalIncrement H hH0 hH1) =ᵐ[gaussianProduct]
    fun w => FractionalGaussianProcess.process H hH0 hH1 2 w-FractionalGaussianProcess.process H hH0 hH1 1 w := by
  have he : firstChaosEmbedding (fractionalIncrement H hH0 hH1)=
      FractionalGaussianProcess.value H hH0 hH1 2-FractionalGaussianProcess.value H hH0 hH1 1 := by
    rw [fractionalIncrement,map_sub]
    rfl
  rw [he]
  exact Lp.coeFn_sub _ _

/-- A single fixed legitimate L2 probe already rules out weak reconstruction.
No existence of a completed continuous conditional operator is assumed. -/
theorem no_test_reconstruction (N : ℕ → ℕ) (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0)
    (hτ : ∀ m, Monotone (τ m)) (h0 : ∀ m, τ m 0=1) (hT : ∀ m, τ m (Fin.last (N m))=2)
    (hH : H≠1/2) :
    ¬ Tendsto (fun m => inner ℝ (conditionedOutput H hH0 hH1 (τ m)) (pastSquare H hH0 hH1))
      atTop (𝓝 (inner ℝ (squareTarget H hH0 hH1) (pastSquare H hH0 hH1))) := by
  intro ht
  have hp (m : ℕ) := conditioned_pairing H hH0 hH1 (τ m) (hτ m) (h0 m) (hT m)
  simp_rw [hp,target_pairing] at ht
  have he : 4*(correlation H hH0 hH1)^2=2*(correlation H hH0 hH1)^2 :=
    tendsto_nhds_unique tendsto_const_nhds ht
  have hc : correlation H hH0 hH1≠0 := fun hh => hH ((correlation_zero_iff H hH0 hH1).mp hh)
  nlinarith [sq_pos_of_ne_zero hc]

theorem pastSquare_actual : pastSquare H hH0 hH1 =ᵐ[gaussianProduct]
    fun w => (FractionalGaussianProcess.process H hH0 hH1 1 w)^2-1 := by
  filter_upwards [mixedTarget_coeFn (fractionalPast H hH0 hH1) (fractionalPast H hH0 hH1)] with w hw
  change mixedTarget (fractionalPast H hH0 hH1) (fractionalPast H hH0 hH1) w=
    (firstChaosEmbedding (fractionalPast H hH0 hH1) w)^2-1
  rw [hw,past_unit]
  ring

end OperatorDerivativeRewrite.Foundation.FractionalCausalGridObstruction
