import Foundation.FractionalPredictiveIntegral
import Foundation.GaussianTimeHilbert

/-! Partition consistency in the actual fractional native field norm.
The Brownian min-clock model applies ONLY to forecast coefficients, not to
the fractional driver. No driver independent-increment assumption is made. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalPredictivePartitions
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeFieldNorm
open StochasticCauchyFractionalDivergence FractionalGridProjection FractionalCausalGridObstruction
open FractionalPredictiveIntegral GaussianLinearFieldDivergenceCompletion
variable (H : ℝ) (hH0 : 0<H) (hH1 : H<1)

private abbrev d (t : ℝ≥0) := FractionalGaussianProcess.direction H hH0 hH1 t
private abbrev q (t : ℝ≥0) := predictionDirection H hH0 hH1 t
private def rank (a b : CoefficientSpace) : GaussianVectorL2 := scalarTensor a (firstChaosEmbedding b)
private theorem rank_sub_left (a b c : CoefficientSpace) : rank (a-b) c=rank a c-rank b c :=
  (GaussianJointRecoveryIntertwining.sourceTensor (firstChaosEmbedding c)).map_sub a b
private theorem rank_sub_right (a b c : CoefficientSpace) : rank a (b-c)=rank a b-rank a c := by
  simp only [rank,map_sub]
private theorem rank_inner (a b c e : CoefficientSpace) :
    inner ℝ (rank a b) (rank c e)=inner ℝ b e*inner ℝ a c := by
  rw [rank,rank,scalarTensor_pair_inner,firstChaosEmbedding.inner_map_map]

def forecastClock (t : ℝ≥0) : ℝ≥0 := ⟨‖q H hH0 hH1 t‖^2,sq_nonneg _⟩

theorem forecastClock_monotone : Monotone (forecastClock H hH0 hH1) := by
  intro s t hst
  change ‖q H hH0 hH1 s‖^2≤‖q H hH0 hH1 t‖^2
  have hp := prediction_time_pairing H hH0 hH1 t s
  rw [min_eq_right hst] at hp
  have hn := norm_sub_sq_real (q H hH0 hH1 t) (q H hH0 hH1 s)
  nlinarith [sq_nonneg ‖q H hH0 hH1 t-q H hH0 hH1 s‖]

/-- The actual coefficient Gram kernel equals the existing time-Hilbert min kernel. -/
theorem forecast_clock_gram (s t : ℝ≥0) :
    inner ℝ (q H hH0 hH1 s) (q H hH0 hH1 t)=
      inner ℝ (GaussianTimeHilbert.timeVector (forecastClock H hH0 hH1 s))
        (GaussianTimeHilbert.timeVector (forecastClock H hH0 hH1 t)) := by
  rw [prediction_time_pairing,GaussianTimeHilbert.timeVector_inner]
  change (forecastClock H hH0 hH1 (min s t):ℝ)=
    min (forecastClock H hH0 hH1 s:ℝ) (forecastClock H hH0 hH1 t:ℝ)
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst,min_eq_left (show (forecastClock H hH0 hH1 s:ℝ)≤forecastClock H hH0 hH1 t from
      forecastClock_monotone H hH0 hH1 hst)]
  · rw [min_eq_right hts,min_eq_right (show (forecastClock H hH0 hH1 t:ℝ)≤forecastClock H hH0 hH1 s from
      forecastClock_monotone H hH0 hH1 hts)]

theorem forecast_increment_gram {a b c e : ℝ≥0} (hab : a≤b) (hce : c≤e) :
    inner ℝ (q H hH0 hH1 b-q H hH0 hH1 a) (q H hH0 hH1 e-q H hH0 hH1 c)=
      volume.real (Ioc (forecastClock H hH0 hH1 a:ℝ) (forecastClock H hH0 hH1 b:ℝ) ∩
        Ioc (forecastClock H hH0 hH1 c:ℝ) (forecastClock H hH0 hH1 e:ℝ)) := by
  calc
    _=inner ℝ
        (GaussianTimeHilbert.timeVector (forecastClock H hH0 hH1 b)-GaussianTimeHilbert.timeVector (forecastClock H hH0 hH1 a))
        (GaussianTimeHilbert.timeVector (forecastClock H hH0 hH1 e)-GaussianTimeHilbert.timeVector (forecastClock H hH0 hH1 c)) := by
      simp only [inner_sub_left,inner_sub_right,forecast_clock_gram]
    _=_ := by
      rw [GaussianTimeHilbert.timeVector_sub _ _ (forecastClock_monotone H hH0 hH1 hab),
        GaussianTimeHilbert.timeVector_sub _ _ (forecastClock_monotone H hH0 hH1 hce),
        GaussianTimeHilbert.intervalVector_inner]

private def increment {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (i : Fin n) : CoefficientSpace :=
  q H hH0 hH1 (τ i.succ)-q H hH0 hH1 (τ i.castSucc)

def weight {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0) (i : Fin n) (j : Fin m) : ℝ :=
  inner ℝ (increment H hH0 hH1 τ i) (increment H hH0 hH1 σ j)

theorem weight_nonneg {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (i : Fin n) (j : Fin m) :
    0≤weight H hH0 hH1 τ σ i j := by
  rw [weight,increment,increment,forecast_increment_gram H hH0 hH1
    (hτ (Fin.castSucc_le_succ i)) (hσ (Fin.castSucc_le_succ j))]
  exact ENNReal.toReal_nonneg

private theorem increment_orthogonal {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (i j : Fin n) (hij : i≠j) : inner ℝ (increment H hH0 hH1 τ i) (increment H hH0 hH1 τ j)=0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact prediction_increment_orthogonal H hH0 hH1 (hτ (Fin.castSucc_le_succ i))
      (hτ (Fin.succ_le_castSucc_iff.mpr hlt)) (hτ (Fin.castSucc_le_succ j))
  · exact (real_inner_comm _ _).trans
      (prediction_increment_orthogonal H hH0 hH1 (hτ (Fin.castSucc_le_succ j))
        (hτ (Fin.succ_le_castSucc_iff.mpr hgt)) (hτ (Fin.castSucc_le_succ i)))

private theorem sum_successive {E : Type*} [AddCommGroup E] {n : ℕ} (f : Fin (n+1) → E) :
    (∑ i : Fin n, (f i.succ-f i.castSucc))=f (Fin.last n)-f 0 := by
  have hs := Fin.sum_univ_succ f
  have hc := Fin.sum_univ_castSucc f
  have hsucc : (∑ i : Fin n, f i.succ)=(∑ i,f i)-f 0 :=
    eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact hs.symm)
  have hcast : (∑ i : Fin n, f i.castSucc)=(∑ i,f i)-f (Fin.last n) := eq_sub_iff_add_eq.mpr hc.symm
  rw [Finset.sum_sub_distrib,hsucc,hcast]
  abel

private theorem increment_total {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) :
    (∑ i : Fin n, increment H hH0 hH1 τ i)=q H hH0 hH1 2-q H hH0 hH1 1 := by
  simpa only [increment,h0,hT] using sum_successive (fun i => q H hH0 hH1 (τ i))

private theorem weight_row {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (h0 : τ 0=1) (hT : τ (Fin.last n)=2)
    (s0 : σ 0=1) (sT : σ (Fin.last m)=2) (i : Fin n) :
    (∑ j : Fin m,weight H hH0 hH1 τ σ i j)=‖increment H hH0 hH1 τ i‖^2 := by
  have hs := (increment_total H hH0 hH1 σ s0 sT).trans (increment_total H hH0 hH1 τ h0 hT).symm
  simp only [weight]
  rw [← inner_sum,hs,inner_sum,Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j _ hji
    exact increment_orthogonal H hH0 hH1 τ hτ i j hji.symm
  · simp

private theorem weight_col {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hσ : Monotone σ) (h0 : τ 0=1) (hT : τ (Fin.last n)=2)
    (s0 : σ 0=1) (sT : σ (Fin.last m)=2) (j : Fin m) :
    (∑ i : Fin n,weight H hH0 hH1 τ σ i j)=‖increment H hH0 hH1 σ j‖^2 := by
  calc
    _=∑ i : Fin n,weight H hH0 hH1 σ τ j i := by
      apply Finset.sum_congr rfl
      intro i _
      exact real_inner_comm _ _
    _=_ := weight_row H hH0 hH1 σ τ hσ s0 sT h0 hT j

theorem weight_mass_bound {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) (s0 : σ 0=1) (sT : σ (Fin.last m)=2) :
    (∑ i : Fin n, ∑ j : Fin m,weight H hH0 hH1 τ σ i j)≤1 := by
  have hb := prediction_energy_bound H hH0 hH1 1 (fun _ => 1) (fun _ => 2)
    (fun i hi => by norm_num) (fun i hi j hj hij => by omega)
  simp only [Finset.sum_range_one] at hb
  simp only [weight]
  simp_rw [← inner_sum]
  rw [← sum_inner]
  rw [increment_total H hH0 hH1 τ h0 hT,increment_total H hH0 hH1 σ s0 sT,
    real_inner_self_eq_norm_sq]
  exact hb

private def rightSum {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : GaussianVectorL2 :=
  ∑ i : Fin n, rank (d H hH0 hH1 (τ i.succ)) (increment H hH0 hH1 τ i)

private theorem rank_difference (a b c e : CoefficientSpace) :
    rank (b-a) c=(rank b e-rank a c)-rank b (e-c) := by
  rw [rank_sub_left,rank_sub_right]
  abel

private theorem parts {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    conditionedField H hH0 hH1 τ=(2:ℝ) •
      (rank (d H hH0 hH1 (τ (Fin.last n))) (q H hH0 hH1 (τ (Fin.last n)))-
        rank (d H hH0 hH1 (τ 0)) (q H hH0 hH1 (τ 0))-rightSum H hH0 hH1 τ) := by
  rw [conditionedField,← Finset.smul_sum]
  congr 1
  change (∑ i : Fin n,rank (d H hH0 hH1 (τ i.succ)-d H hH0 hH1 (τ i.castSucc))
    (q H hH0 hH1 (τ i.castSucc)))=_
  have ht (i : Fin n) : rank (d H hH0 hH1 (τ i.succ)-d H hH0 hH1 (τ i.castSucc))
      (q H hH0 hH1 (τ i.castSucc))=
        (rank (d H hH0 hH1 (τ i.succ)) (q H hH0 hH1 (τ i.succ))-
          rank (d H hH0 hH1 (τ i.castSucc)) (q H hH0 hH1 (τ i.castSucc)))-
        rank (d H hH0 hH1 (τ i.succ)) (q H hH0 hH1 (τ i.succ)-q H hH0 hH1 (τ i.castSucc)) :=
    rank_difference _ _ _ _
  simp_rw [ht,Finset.sum_sub_distrib]
  have hs := sum_successive (fun i => rank (d H hH0 hH1 (τ i)) (q H hH0 hH1 (τ i)))
  rw [Finset.sum_sub_distrib] at hs
  rw [hs]
  rfl

private theorem right_energy {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    ‖rightSum H hH0 hH1 τ‖^2=
      ∑ i : Fin n, ‖d H hH0 hH1 (τ i.succ)‖^2*‖increment H hH0 hH1 τ i‖^2 := by
  rw [← real_inner_self_eq_norm_sq,rightSum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum,Finset.sum_eq_single i]
  · rw [rank_inner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,mul_comm]
  · intro j _ hji
    rw [rank_inner,increment_orthogonal H hH0 hH1 τ hτ i j hji.symm,zero_mul]
  · simp

private theorem right_pairing {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0) :
    inner ℝ (rightSum H hH0 hH1 τ) (rightSum H hH0 hH1 σ)=
      ∑ i : Fin n,∑ j : Fin m,weight H hH0 hH1 τ σ i j*
        inner ℝ (d H hH0 hH1 (τ i.succ)) (d H hH0 hH1 (σ j.succ)) := by
  simp only [rightSum,sum_inner,inner_sum,rank_inner,weight]
  rw [Finset.sum_comm]

/-- Positive coefficient-overlap weights give an exact comparison of the two
actual tensor quadratures; no common-refinement construction is required. -/
private theorem quadrature_difference_sq {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (h0 : τ 0=1) (hT : τ (Fin.last n)=2)
    (s0 : σ 0=1) (sT : σ (Fin.last m)=2) :
    ‖rightSum H hH0 hH1 τ-rightSum H hH0 hH1 σ‖^2=
      ∑ i : Fin n,∑ j : Fin m,weight H hH0 hH1 τ σ i j*
        ‖d H hH0 hH1 (τ i.succ)-d H hH0 hH1 (σ j.succ)‖^2 := by
  have hr : (∑ i : Fin n,∑ j : Fin m,weight H hH0 hH1 τ σ i j*‖d H hH0 hH1 (τ i.succ)‖^2)=
      ‖rightSum H hH0 hH1 τ‖^2 := by
    rw [right_energy H hH0 hH1 τ hτ]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul,weight_row H hH0 hH1 τ σ hτ h0 hT s0 sT i,mul_comm]
  have hc : (∑ i : Fin n,∑ j : Fin m,weight H hH0 hH1 τ σ i j*‖d H hH0 hH1 (σ j.succ)‖^2)=
      ‖rightSum H hH0 hH1 σ‖^2 := by
    rw [Finset.sum_comm,right_energy H hH0 hH1 σ hσ]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul,weight_col H hH0 hH1 τ σ hσ h0 hT s0 sT j,mul_comm]
  have hp (i : Fin n) (j : Fin m) :
      weight H hH0 hH1 τ σ i j*‖d H hH0 hH1 (τ i.succ)-d H hH0 hH1 (σ j.succ)‖^2=
        weight H hH0 hH1 τ σ i j*‖d H hH0 hH1 (τ i.succ)‖^2+
        weight H hH0 hH1 τ σ i j*‖d H hH0 hH1 (σ j.succ)‖^2-
        2*(weight H hH0 hH1 τ σ i j*inner ℝ (d H hH0 hH1 (τ i.succ)) (d H hH0 hH1 (σ j.succ))) := by
    rw [norm_sub_sq_real]
    ring
  simp_rw [hp,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hr,hc,← right_pairing]
  rw [norm_sub_sq_real]
  ring

private theorem driver_norm (s t : ℝ≥0) : ‖d H hH0 hH1 s-d H hH0 hH1 t‖=|(s:ℝ)-t|^H := by
  have hn := FractionalGaussianProcess.value_increment_norm H hH0 hH1 t s
  rw [FractionalGaussianProcess.value,FractionalGaussianProcess.value,← map_sub,firstChaosEmbedding.norm_map] at hn
  exact hn

private theorem weight_zero {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (i : Fin n) (j : Fin m) (hij : τ i.succ≤σ j.castSucc) :
    weight H hH0 hH1 τ σ i j=0 :=
  prediction_increment_orthogonal H hH0 hH1 (hτ (Fin.castSucc_le_succ i)) hij
    (hσ (Fin.castSucc_le_succ j))

private theorem weighted_distance_bound {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (ε : ℝ) (hε : 0≤ε)
    (hmesh : ∀ i : Fin n,(τ i.succ:ℝ)-τ i.castSucc≤ε)
    (smesh : ∀ j : Fin m,(σ j.succ:ℝ)-σ j.castSucc≤ε) (i : Fin n) (j : Fin m) :
    weight H hH0 hH1 τ σ i j*‖d H hH0 hH1 (τ i.succ)-d H hH0 hH1 (σ j.succ)‖^2≤
      weight H hH0 hH1 τ σ i j*(ε^H)^2 := by
  by_cases hleft : τ i.succ≤σ j.castSucc
  · rw [weight_zero H hH0 hH1 τ σ hτ hσ i j hleft,zero_mul,zero_mul]
  by_cases hright : σ j.succ≤τ i.castSucc
  · have hz : weight H hH0 hH1 τ σ i j=0 := (real_inner_comm _ _).trans
      (weight_zero H hH0 hH1 σ τ hσ hτ j i hright)
    rw [hz,zero_mul,zero_mul]
  have hl : (σ j.castSucc:ℝ)<τ i.succ := lt_of_not_ge hleft
  have hr : (τ i.castSucc:ℝ)<σ j.succ := lt_of_not_ge hright
  have hab : |(τ i.succ:ℝ)-σ j.succ|≤ε := by
    rw [abs_le]
    constructor <;> linarith [hmesh i,smesh j]
  have hn : ‖d H hH0 hH1 (τ i.succ)-d H hH0 hH1 (σ j.succ)‖≤ε^H := by
    rw [driver_norm]
    exact Real.rpow_le_rpow (abs_nonneg _) hab hH0.le
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hε H)).mpr hn)
    (weight_nonneg H hH0 hH1 τ σ hτ hσ i j)

/-- Exact positive-weight comparison in the ORIGINAL fractional field norm. -/
theorem field_difference_sq {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (h0 : τ 0=1) (hT : τ (Fin.last n)=2)
    (s0 : σ 0=1) (sT : σ (Fin.last m)=2) :
    ‖conditionedField H hH0 hH1 τ-conditionedField H hH0 hH1 σ‖^2=
      4*(∑ i : Fin n,∑ j : Fin m,weight H hH0 hH1 τ σ i j*
        ‖d H hH0 hH1 (τ i.succ)-d H hH0 hH1 (σ j.succ)‖^2) := by
  have he : conditionedField H hH0 hH1 τ-conditionedField H hH0 hH1 σ=
      (-2:ℝ) • (rightSum H hH0 hH1 τ-rightSum H hH0 hH1 σ) := by
    rw [parts,parts,h0,hT,s0,sT]
    module
  rw [he,norm_smul,mul_pow,quadrature_difference_sq H hH0 hH1 τ σ hτ hσ h0 hT s0 sT]
  norm_num

theorem field_distance_bound {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (h0 : τ 0=1) (hT : τ (Fin.last n)=2)
    (s0 : σ 0=1) (sT : σ (Fin.last m)=2) (ε : ℝ) (hε : 0≤ε)
    (hmesh : ∀ i : Fin n,(τ i.succ:ℝ)-τ i.castSucc≤ε)
    (smesh : ∀ j : Fin m,(σ j.succ:ℝ)-σ j.castSucc≤ε) :
    ‖conditionedField H hH0 hH1 τ-conditionedField H hH0 hH1 σ‖≤2*ε^H := by
  have hs : (∑ i : Fin n,∑ j : Fin m,weight H hH0 hH1 τ σ i j*
      ‖d H hH0 hH1 (τ i.succ)-d H hH0 hH1 (σ j.succ)‖^2)≤(ε^H)^2 := by
    calc
      _≤∑ i : Fin n,∑ j : Fin m,weight H hH0 hH1 τ σ i j*(ε^H)^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact weighted_distance_bound H hH0 hH1 τ σ hτ hσ ε hε hmesh smesh i j
      _=(∑ i : Fin n,∑ j : Fin m,weight H hH0 hH1 τ σ i j)*(ε^H)^2 := by
        simp_rw [← Finset.sum_mul]
      _≤1*(ε^H)^2 := mul_le_mul_of_nonneg_right (weight_mass_bound H hH0 hH1 τ σ h0 hT s0 sT) (sq_nonneg _)
      _=(ε^H)^2 := one_mul _
  have hf := field_difference_sq H hH0 hH1 τ σ hτ hσ h0 hT s0 sT
  have hp := Real.rpow_nonneg hε H
  nlinarith [norm_nonneg (conditionedField H hH0 hH1 τ-conditionedField H hH0 hH1 σ)]

theorem field_limit_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) (ε : ℝ) (hε : 0≤ε)
    (hmesh : ∀ i : Fin n,(τ i.succ:ℝ)-τ i.castSucc≤ε) :
    ‖conditionedField H hH0 hH1 τ-predictiveField H hH0 hH1‖≤2*ε^H := by
  have hb (N : ℕ) : ‖conditionedField H hH0 hH1 τ-dyadicField H hH0 hH1 N‖≤2*(ε+(1/2:ℝ)^N)^H := by
    rw [field_as_conditioned]
    apply field_distance_bound H hH0 hH1 τ (times N) hτ (times_monotone N) h0 hT
      (times_endpoints N).1 (times_endpoints N).2 (ε+(1/2:ℝ)^N) (by positivity)
    · intro i
      linarith [hmesh i,pow_nonneg (by norm_num : 0≤(1/2:ℝ)) N]
    · intro i
      rw [times_step]
      linarith
  have hl := ((tendsto_const_nhds (x := conditionedField H hH0 hH1 τ)).sub (field_tendsto H hH0 hH1)).norm
  have hr : Tendsto (fun N : ℕ => 2*(ε+(1/2:ℝ)^N)^H) atTop (𝓝 (2*ε^H)) := by
    have hh := (Real.continuous_rpow_const hH0.le).continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := ε)).add mesh_zero)
    simpa only [Function.comp_def,add_zero] using hh.const_mul 2
  exact le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall hb)

/-- Every chronological mesh-zero family converges to the SAME already
constructed field, including nonnested and nonuniform families. -/
theorem partition_field_tendsto (N : ℕ → ℕ) (τ : (j : ℕ) → Fin (N j+1) → ℝ≥0)
    (hτ : ∀ j,Monotone (τ j)) (h0 : ∀ j,τ j 0=1) (hT : ∀ j,τ j (Fin.last (N j))=2)
    (ε : ℕ → ℝ) (hε : ∀ j,0≤ε j) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ j (i : Fin (N j)),(τ j i.succ:ℝ)-τ j i.castSucc≤ε j) :
    Tendsto (fun j => conditionedField H hH0 hH1 (τ j)) atTop (𝓝 (predictiveField H hH0 hH1)) := by
  have hp : Tendsto (fun j => (ε j)^H) atTop (𝓝 0) := by
    have hh := (Real.continuous_rpow_const hH0.le).continuousAt.tendsto.comp hlim
    simpa only [Function.comp_def,Real.zero_rpow (ne_of_gt hH0)] using hh
  have hc : Tendsto (fun j => 2*(ε j)^H) atTop (𝓝 0) := by simpa only [mul_zero] using hp.const_mul 2
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun j => field_limit_bound H hH0 hH1 (τ j)
    (hτ j) (h0 j) (hT j) (ε j) (hε j) (hmesh j)) hc

theorem finite_field_linear {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    conditionedField H hH0 hH1 τ∈linearGaussianFields := by
  apply linearGaussianFields.sum_mem
  intro i _
  exact linearGaussianFields.smul_mem (2:ℝ) (linear_rank_mem _ _)

theorem finite_output_identity {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    completedDivergence (conditionedField H hH0 hH1 τ)=conditionedOutput H hH0 hH1 τ := by
  simp only [conditionedField,conditionedOutput,predictedValue,map_sum,map_smul,completedDivergence_rank]

theorem output_limit_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (h0 : τ 0=1) (hT : τ (Fin.last n)=2) (ε : ℝ) (hε : 0≤ε)
    (hmesh : ∀ i : Fin n,(τ i.succ:ℝ)-τ i.castSucc≤ε) :
    ‖conditionedOutput H hH0 hH1 τ-predictiveIntegral H hH0 hH1‖≤2*Real.sqrt 2*ε^H := by
  have hb := completed_norm_bound (linearGaussianFields.sub_mem
    (finite_field_linear H hH0 hH1 τ) (field_linear H hH0 hH1))
  rw [map_sub,finite_output_identity] at hb
  change ‖conditionedOutput H hH0 hH1 τ-predictiveIntegral H hH0 hH1‖≤
    Real.sqrt 2*‖conditionedField H hH0 hH1 τ-predictiveField H hH0 hH1‖ at hb
  calc
    _≤Real.sqrt 2*‖conditionedField H hH0 hH1 τ-predictiveField H hH0 hH1‖ := hb
    _≤Real.sqrt 2*(2*ε^H) := mul_le_mul_of_nonneg_left
      (field_limit_bound H hH0 hH1 τ hτ h0 hT ε hε hmesh) (Real.sqrt_nonneg 2)
    _=2*Real.sqrt 2*ε^H := by ring

theorem partition_output_tendsto (N : ℕ → ℕ) (τ : (j : ℕ) → Fin (N j+1) → ℝ≥0)
    (hτ : ∀ j,Monotone (τ j)) (h0 : ∀ j,τ j 0=1) (hT : ∀ j,τ j (Fin.last (N j))=2)
    (ε : ℕ → ℝ) (hε : ∀ j,0≤ε j) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ j (i : Fin (N j)),(τ j i.succ:ℝ)-τ j i.castSucc≤ε j) :
    Tendsto (fun j => conditionedOutput H hH0 hH1 (τ j)) atTop (𝓝 (predictiveIntegral H hH0 hH1)) := by
  have ht := (completedDivergence.continuous.tendsto (predictiveField H hH0 hH1)).comp
    (partition_field_tendsto H hH0 hH1 N τ hτ h0 hT ε hε hlim hmesh)
  simpa only [Function.comp_def,finite_output_identity,predictiveIntegral] using ht

theorem partition_mean_square (N : ℕ → ℕ) (τ : (j : ℕ) → Fin (N j+1) → ℝ≥0)
    (hτ : ∀ j,Monotone (τ j)) (h0 : ∀ j,τ j 0=1) (hT : ∀ j,τ j (Fin.last (N j))=2)
    (ε : ℕ → ℝ) (hε : ∀ j,0≤ε j) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ j (i : Fin (N j)),(τ j i.succ:ℝ)-τ j i.castSucc≤ε j) :
    Tendsto (fun j => ∫ w,‖conditionedOutput H hH0 hH1 (τ j) w-predictiveIntegral H hH0 hH1 w‖^2
      ∂gaussianProduct) atTop (𝓝 0) := by
  have he (j : ℕ) : ‖conditionedOutput H hH0 hH1 (τ j)-predictiveIntegral H hH0 hH1‖^2=
      ∫ w,‖conditionedOutput H hH0 hH1 (τ j) w-predictiveIntegral H hH0 hH1 w‖^2 ∂gaussianProduct := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (conditionedOutput H hH0 hH1 (τ j)) (predictiveIntegral H hH0 hH1)] with w hw
    simp only [Pi.sub_apply] at hw
    rw [hw]
  have ht := ((partition_output_tendsto H hH0 hH1 N τ hτ h0 hT ε hε hlim hmesh).sub
    (tendsto_const_nhds (x := predictiveIntegral H hH0 hH1))).norm.pow 2
  simpa only [he,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using ht

end OperatorDerivativeRewrite.Foundation.FractionalPredictivePartitions
