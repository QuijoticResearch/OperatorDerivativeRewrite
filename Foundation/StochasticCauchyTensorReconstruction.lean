import Foundation.StochasticCauchyComplexChannels
import Foundation.GaussianSmallTimeCutoff

/-! Actual conditional-martingale tensor sums toward common-past reconstruction.
All products below are across independent Gaussian factors. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyTensorReconstruction
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2
open GaussianPredictableFull GaussianPredictableCutoff GaussianConditionalIto
open GaussianConditionalClarkOcone GaussianPredictableAdjoint GaussianBrownianGeneratedSpace
open StochasticCauchyParameterizedObstruction
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent

/-- Strong cutoff continuity at EVERY finite time, from either side. -/
theorem cut_time_tendsto (U : TimeProbabilityL2) (T : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hτ : Tendsto τ atTop (𝓝 T)) :
    Tendsto (fun n => cut (τ n) U) atTop (𝓝 (cut T U)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ U
  · intro n
    filter_upwards [cut_coeFn (τ n) U] with z hz
    rw [hz]
    by_cases hm : z ∈ PredictableRealL2.horizon (τ n) <;> simp [hm]
  · filter_upwards [cut_coeFn T U] with z hz
    rw [hz]
    by_cases hm : z ∈ PredictableRealL2.horizon T <;> simp [hm]
  · have hr := NNReal.continuous_coe.continuousAt.tendsto.comp hτ
    have hne : ∀ᵐ r : ℝ ∂volume, r ≠ (T : ℝ) := by
      apply ae_iff.mpr
      simp
    have hp := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae hne
    filter_upwards [ae_all_iff.mpr (fun n => cut_coeFn (τ n) U),cut_coeFn T U,hp]
      with z hz ht hne
    by_cases hpos : 0 < z.1
    · by_cases hlt : z.1 < (T : ℝ)
      · apply tendsto_const_nhds.congr'
        filter_upwards [hr.eventually (lt_mem_nhds hlt)] with n hn
        have hm : z ∈ PredictableRealL2.horizon (τ n) := ⟨⟨hpos,hn.le⟩,mem_univ _⟩
        have hmT : z ∈ PredictableRealL2.horizon T := ⟨⟨hpos,hlt.le⟩,mem_univ _⟩
        exact ((hz n).trans (by rw [indicator_of_mem hm,ht,indicator_of_mem hmT])).symm
      · have hgt : (T : ℝ) < z.1 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
        apply tendsto_const_nhds.congr'
        filter_upwards [hr.eventually (gt_mem_nhds hgt)] with n hn
        have hm : z ∉ PredictableRealL2.horizon (τ n) := fun h => (not_le_of_gt hn) h.1.2
        have hmT : z ∉ PredictableRealL2.horizon T := fun h => (not_le_of_gt hgt) h.1.2
        exact ((hz n).trans (by rw [indicator_of_notMem hm,ht,indicator_of_notMem hmT])).symm
    · have hmT : z ∉ PredictableRealL2.horizon T := fun h => hpos h.1.1
      have he (n : ℕ) : cut (τ n) U z=cut T U z := by
        rw [hz n,ht,indicator_of_notMem (fun h => hpos h.1.1),indicator_of_notMem hmT]
      simpa only [he] using tendsto_const_nhds (x := cut T U z)

theorem cut_time_continuous (U : TimeProbabilityL2) : Continuous (fun T : ℝ≥0 => cut T U) := by
  apply continuous_iff_seqContinuous.mpr
  intro τ T hτ
  exact cut_time_tendsto U T τ hτ

/-- Actual conditional-expectation curves are norm-continuous, not merely weakly so. -/
theorem past_time_continuous (F : GaussianL2) (hF : F ∈ brownianL2) :
    Continuous (fun T : ℝ≥0 => pastProjection T F) := by
  have he (T : ℝ≥0) : GaussianContinuousRigidity.integralExtension
      (cut T (predictableAdjoint F)) =
        pastProjection T F-(∫ w, F w ∂gaussianProduct) • gaussianOne := by
    change GaussianContinuousRigidity.integralExtension (predictableCut T (predictableAdjoint F)) = _
    rw [GaussianContinuousRigidity.integralExtension_eq,past_representation T F hF]
  have hc := (GaussianContinuousRigidity.integralExtension.continuous.comp
    (cut_time_continuous (predictableAdjoint F))).add
      (continuous_const (y := (∫ w, F w ∂gaussianProduct) • gaussianOne))
  apply hc.congr
  intro T
  change GaussianContinuousRigidity.integralExtension (cut T (predictableAdjoint F))+
    (∫ w, F w ∂gaussianProduct) • gaussianOne=pastProjection T F
  rw [he,sub_add_cancel]

theorem past_inner_difference (s t : ℝ≥0) (hst : s ≤ t) (A F : GaussianL2)
    (hA : A ∈ pastL2 s) : inner ℝ A (pastProjection t F-pastProjection s F)=0 := by
  have hs : (pastL2 s).starProjection A=A := Submodule.starProjection_eq_self_iff.mpr hA
  have ht : (pastL2 t).starProjection A=A :=
    Submodule.starProjection_eq_self_iff.mpr (hA.mono (naturalFiltration.mono hst))
  have h1 := (pastL2 s).inner_starProjection_left_eq_right A F
  have h2 := (pastL2 t).inner_starProjection_left_eq_right A F
  rw [hs] at h1
  rw [ht] at h2
  change inner ℝ A ((pastL2 t).starProjection F-(pastL2 s).starProjection F)=0
  rw [inner_sub_right,h1.symm,h2.symm,sub_self]

def cell (τ : ℕ → ℝ≥0) (F : GaussianL2) (i : ℕ) : GaussianL2 :=
  pastProjection (τ (i + 1)) F-pastProjection (τ i) F

theorem cell_past (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (F : GaussianL2) (i : ℕ) :
    cell τ F i ∈ pastL2 (τ (i + 1)) :=
  (pastL2 (τ (i + 1))).sub_mem ((pastL2 (τ (i + 1))).starProjection_apply_mem F)
    (((pastL2 (τ i)).starProjection_apply_mem F).mono (naturalFiltration.mono (hτ (Nat.le_succ i))))

theorem cells_orthogonal (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F G : GaussianL2) (i j : ℕ) (hij : i < j) : inner ℝ (cell τ F i) (cell τ G j)=0 :=
  past_inner_difference (τ j) (τ (j+1)) (hτ (Nat.le_succ j)) _ G
    ((cell_past τ hτ F i).mono (naturalFiltration.mono (hτ (Nat.succ_le_of_lt hij))))

theorem cell_energy (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (F : GaussianL2) (i : ℕ) :
    ‖cell τ F i‖ ^ 2=‖pastProjection (τ (i + 1)) F‖ ^ 2-‖pastProjection (τ i) F‖ ^ 2 := by
  have ho := past_inner_difference (τ i) (τ (i + 1)) (hτ (Nat.le_succ i))
    (pastProjection (τ i) F) F ((pastL2 (τ i)).starProjection_apply_mem F)
  have he := norm_add_sq_real (pastProjection (τ i) F) (cell τ F i)
  have hs : pastProjection (τ i) F+cell τ F i=pastProjection (τ (i + 1)) F := by
    unfold cell
    abel
  rw [hs,show inner ℝ (pastProjection (τ i) F) (cell τ F i)=0 from ho] at he
  linarith

theorem cell_energy_sum (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (F : GaussianL2) (n : ℕ) :
    (∑ i ∈ Finset.range n, ‖cell τ F i‖ ^ 2)=
      ‖pastProjection (τ n) F‖ ^ 2-‖pastProjection (τ 0) F‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,cell_energy τ hτ F n]
    ring

theorem cell_energy_sum_le (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (F : GaussianL2) (n : ℕ) :
    (∑ i ∈ Finset.range n, ‖cell τ F i‖ ^ 2) ≤ ‖F‖ ^ 2 := by
  rw [cell_energy_sum τ hτ F n]
  have hb := (pastL2 (τ n)).norm_starProjection_apply_le F
  change ‖pastProjection (τ n) F‖ ≤ ‖F‖ at hb
  nlinarith [norm_nonneg (pastProjection (τ n) F),norm_nonneg F,sq_nonneg ‖pastProjection (τ 0) F‖]

/-- Mixed quadratic variation in the ACTUAL independent-source product L2. -/
def mixedRemainder (τ : ℕ → ℝ≥0) (F G : GaussianL2) (n : ℕ) : JointL2 :=
  ∑ i ∈ Finset.range n, ProductL2Curry.productTensor gaussianProduct gaussianProduct (cell τ F i) (cell τ G i)

theorem mixedRemainder_energy (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (F G : GaussianL2) (n : ℕ) :
    ‖mixedRemainder τ F G n‖ ^ 2=
      ∑ i ∈ Finset.range n, ‖cell τ F i‖ ^ 2*‖cell τ G i‖ ^ 2 := by
  induction n with
  | zero => simp [mixedRemainder]
  | succ n ih =>
    have ho : inner ℝ (mixedRemainder τ F G n)
        (ProductL2Curry.productTensor gaussianProduct gaussianProduct (cell τ F n) (cell τ G n))=0 := by
      rw [mixedRemainder,sum_inner]
      apply Finset.sum_eq_zero
      intro i hi
      rw [tensor_inner,cells_orthogonal τ hτ F F i n (Finset.mem_range.mp hi),zero_mul]
    have ht : ‖ProductL2Curry.productTensor gaussianProduct gaussianProduct
        (cell τ F n) (cell τ G n)‖ ^ 2=‖cell τ F n‖ ^ 2*‖cell τ G n‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq,tensor_inner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
    have hs : mixedRemainder τ F G (n + 1)=mixedRemainder τ F G n+
        ProductL2Curry.productTensor gaussianProduct gaussianProduct (cell τ F n) (cell τ G n) :=
      Finset.sum_range_succ _ _
    rw [hs,norm_add_sq_real,ho,ht,ih,Finset.sum_range_succ]
    ring

theorem mixedRemainder_bound (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (F G : GaussianL2)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hcell : ∀ i < n, ‖cell τ F i‖ ^ 2 ≤ ε) :
    ‖mixedRemainder τ F G n‖ ^ 2 ≤ ε*‖G‖ ^ 2 := by
  rw [mixedRemainder_energy τ hτ F G n]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ε*‖cell τ G i‖ ^ 2 := Finset.sum_le_sum
      (fun i hi => mul_le_mul_of_nonneg_right (hcell i (Finset.mem_range.mp hi)) (sq_nonneg _))
    _ = ε*(∑ i ∈ Finset.range n, ‖cell τ G i‖ ^ 2) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (cell_energy_sum_le τ hτ G n) hε

/-- Vanishing mixed quadratic variation for actual conditional martingales.
Only the first source needs the stated Brownian-generated continuity hypothesis. -/
theorem mixedRemainder_tendsto (T : ℝ≥0) (F G : GaussianL2) (hF : F ∈ brownianL2)
    (τ : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) (hτ : ∀ n, Monotone (τ n))
    (hb : ∀ n j, j ≤ N n → τ n j ≤ T) (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hstep : ∀ n i, i < N n → dist (τ n (i + 1)) (τ n i) ≤ mesh n) :
    Tendsto (fun n => mixedRemainder (τ n) F G (N n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(‖G‖+1)
  have hpos : 0 < ‖G‖+1 := by positivity
  have hη : 0 < η := div_pos hε hpos
  obtain ⟨δ,hδ,hu⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).uniformContinuousOn_of_continuous
      (past_time_continuous F hF).continuousOn) η hη
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn
  have hcell : ∀ i < N n, ‖cell (τ n) F i‖ ^ 2 ≤ η ^ 2 := by
    intro i hi
    have hc := hu (τ n (i + 1)) ⟨by positivity,hb n (i + 1) (Nat.succ_le_of_lt hi)⟩
      (τ n i) ⟨by positivity,hb n i hi.le⟩ ((hstep n i hi).trans_lt hn)
    have he : ‖cell (τ n) F i‖ < η := by simpa only [dist_eq_norm,cell] using hc
    nlinarith [norm_nonneg (cell (τ n) F i)]
  have he := mixedRemainder_bound (τ n) (hτ n) F G (N n) (η ^ 2) (sq_nonneg _) hcell
  have hnorm : ‖mixedRemainder (τ n) F G (N n)‖ ≤ η*‖G‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hη.le (norm_nonneg G))).mp
    simpa only [mul_pow] using he
  have hsmall : η*‖G‖ < ε := by
    change ε/(‖G‖+1)*‖G‖ < ε
    rw [div_mul_eq_mul_div,div_lt_iff₀ hpos]
    nlinarith
  simpa only [dist_zero_right] using hnorm.trans_lt hsmall

private theorem tensor_cell_identity (A B C D : GaussianL2) :
    ProductL2Curry.productTensor gaussianProduct gaussianProduct B D-
      ProductL2Curry.productTensor gaussianProduct gaussianProduct A C =
      ProductL2Curry.productTensor gaussianProduct gaussianProduct (B-A) C+
      ProductL2Curry.productTensor gaussianProduct gaussianProduct A (D-C)+
      ProductL2Curry.productTensor gaussianProduct gaussianProduct (B-A) (D-C) := by
  apply (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).injective
  simp only [map_sub,map_add]
  have ht (a b : GaussianL2) : ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
      (ProductL2Curry.productTensor gaussianProduct gaussianProduct a b)=
        BochnerClosedOperator.tensor gaussianProduct a b :=
    ProductL2Curry.curry_productTensor gaussianProduct gaussianProduct a b
  rw [ht,ht,ht,ht,ht]
  apply Lp.ext
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct B D,
    BochnerClosedOperator.tensor_coeFn gaussianProduct A C,
    BochnerClosedOperator.tensor_coeFn gaussianProduct (B-A) C,
    BochnerClosedOperator.tensor_coeFn gaussianProduct A (D-C),
    BochnerClosedOperator.tensor_coeFn gaussianProduct (B-A) (D-C),Lp.coeFn_sub B A,
    Lp.coeFn_sub (BochnerClosedOperator.tensor gaussianProduct B D)
      (BochnerClosedOperator.tensor gaussianProduct A C),
    Lp.coeFn_add (BochnerClosedOperator.tensor gaussianProduct (B-A) C)
      (BochnerClosedOperator.tensor gaussianProduct A (D-C)),
    Lp.coeFn_add (BochnerClosedOperator.tensor gaussianProduct (B-A) C+
      BochnerClosedOperator.tensor gaussianProduct A (D-C))
      (BochnerClosedOperator.tensor gaussianProduct (B-A) (D-C))]
    with w hbd hac hbc had hbad hba hsub hadd hbig
  simp only [Pi.sub_apply,Pi.add_apply] at hba hsub hadd hbig
  rw [hsub,hbig,hadd,hbd,hac,hbc,had,hbad,hba]
  simp only [sub_smul,smul_sub]
  abel

/-- Actual chronological conditional-martingale sums, in native product L2. -/
def chronologicalSum (τ : ℕ → ℝ≥0) (F G : GaussianL2) (n : ℕ) : JointL2 :=
  ∑ i ∈ Finset.range n,
    (ProductL2Curry.productTensor gaussianProduct gaussianProduct (cell τ F i) (pastProjection (τ i) G)+
      ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection (τ i) F) (cell τ G i))

theorem product_telescope (τ : ℕ → ℝ≥0) (F G : GaussianL2) (n : ℕ) :
    ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection (τ n) F) (pastProjection (τ n) G)-
      ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection (τ 0) F) (pastProjection (τ 0) G)=
      chronologicalSum τ F G n+mixedRemainder τ F G n := by
  induction n with
  | zero => simp [chronologicalSum,mixedRemainder]
  | succ n ih =>
    have hc : chronologicalSum τ F G (n + 1)=chronologicalSum τ F G n+
        (ProductL2Curry.productTensor gaussianProduct gaussianProduct (cell τ F n) (pastProjection (τ n) G)+
          ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection (τ n) F) (cell τ G n)) :=
      Finset.sum_range_succ _ _
    have hm : mixedRemainder τ F G (n + 1)=mixedRemainder τ F G n+
        ProductL2Curry.productTensor gaussianProduct gaussianProduct (cell τ F n) (cell τ G n) :=
      Finset.sum_range_succ _ _
    have he := tensor_cell_identity (pastProjection (τ n) F) (pastProjection (τ (n + 1)) F)
      (pastProjection (τ n) G) (pastProjection (τ (n + 1)) G)
    change ProductL2Curry.productTensor gaussianProduct gaussianProduct
      (pastProjection (τ (n + 1)) F) (pastProjection (τ (n + 1)) G)-
        ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection (τ n) F) (pastProjection (τ n) G)=
        ProductL2Curry.productTensor gaussianProduct gaussianProduct (cell τ F n) (pastProjection (τ n) G)+
        ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection (τ n) F) (cell τ G n)+
        ProductL2Curry.productTensor gaussianProduct gaussianProduct (cell τ F n) (cell τ G n) at he
    rw [hc,hm]
    calc
      _ = (ProductL2Curry.productTensor gaussianProduct gaussianProduct
          (pastProjection (τ (n + 1)) F) (pastProjection (τ (n + 1)) G)-
            ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection (τ n) F) (pastProjection (τ n) G))+
          (ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection (τ n) F) (pastProjection (τ n) G)-
            ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection (τ 0) F) (pastProjection (τ 0) G)) := by abel
      _ = _ := by rw [he,ih]; abel

/-- No fourth moments: all products are of independent L2 source factors. -/
theorem chronologicalSum_tendsto (T : ℝ≥0) (F G : GaussianL2) (hF : F ∈ brownianL2)
    (τ : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) (hτ : ∀ n, Monotone (τ n))
    (hb : ∀ n j, j ≤ N n → τ n j ≤ T) (h0 : ∀ n, τ n 0=0)
    (hT : ∀ n, τ n (N n)=T) (mesh : ℕ → ℝ) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hstep : ∀ n i, i < N n → dist (τ n (i + 1)) (τ n i) ≤ mesh n) :
    Tendsto (fun n => chronologicalSum (τ n) F G (N n)) atTop
      (𝓝 (ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection T F) (pastProjection T G)-
        ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection 0 F) (pastProjection 0 G))) := by
  have hr := mixedRemainder_tendsto T F G hF τ N hτ hb mesh hmesh hstep
  have he (n : ℕ) : chronologicalSum (τ n) F G (N n)=
      (ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection T F) (pastProjection T G)-
        ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection 0 F) (pastProjection 0 G))-
        mixedRemainder (τ n) F G (N n) := by
    have ht := product_telescope (τ n) F G (N n)
    rw [h0 n,hT n] at ht
    exact eq_sub_iff_add_eq.mpr ht.symm
  have hc := (tendsto_const_nhds (x :=
    ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection T F) (pastProjection T G)-
      ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection 0 F) (pastProjection 0 G))).sub hr
  simpa only [sub_zero,he] using hc

def uniformGrid (T : ℝ≥0) (n i : ℕ) : ℝ≥0 := (i : ℝ≥0)*(T/(n + 1 : ℝ≥0))

theorem uniformGrid_monotone (T : ℝ≥0) (n : ℕ) : Monotone (uniformGrid T n) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

theorem uniformGrid_zero (T : ℝ≥0) (n : ℕ) : uniformGrid T n 0=0 := by simp [uniformGrid]

theorem uniformGrid_end (T : ℝ≥0) (n : ℕ) : uniformGrid T n (n + 1)=T := by
  simp only [uniformGrid,Nat.cast_add,Nat.cast_one]
  rw [mul_comm,div_mul_cancel₀ _ (by positivity)]

theorem uniformGrid_distance (T : ℝ≥0) (n i : ℕ) :
    dist (uniformGrid T n (i + 1)) (uniformGrid T n i)=(T : ℝ)/(n + 1) := by
  change dist (uniformGrid T n (i + 1) : ℝ) (uniformGrid T n i : ℝ) = _
  rw [Real.dist_eq]
  simp only [uniformGrid,NNReal.coe_mul,NNReal.coe_div,NNReal.coe_natCast,
    NNReal.coe_add,NNReal.coe_one,Nat.cast_add,Nat.cast_one]
  have he : ((i : ℝ)+1)*((T : ℝ)/(n + 1))-i*((T : ℝ)/(n + 1))=(T : ℝ)/(n + 1) := by ring
  rw [he,abs_of_nonneg (by positivity)]

theorem uniform_mesh_tendsto (T : ℝ≥0) :
    Tendsto (fun n : ℕ => (T : ℝ)/(n + 1)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- Concrete uniform partitions discharge every mesh and horizon condition. -/
theorem mixedRemainder_uniform_tendsto (T : ℝ≥0) (F G : GaussianL2) (hF : F ∈ brownianL2) :
    Tendsto (fun n => mixedRemainder (uniformGrid T n) F G (n + 1)) atTop (𝓝 0) := by
  apply mixedRemainder_tendsto T F G hF (uniformGrid T) (fun n => n + 1)
    (uniformGrid_monotone T) (fun n j hj => ?_) (fun n => (T : ℝ)/(n + 1))
    (uniform_mesh_tendsto T) (fun n i hi => ?_)
  · exact (uniformGrid_monotone T n hj).trans (uniformGrid_end T n).le
  · exact (uniformGrid_distance T n i).le

theorem chronologicalSum_uniform_tendsto (T : ℝ≥0) (F G : GaussianL2) (hF : F ∈ brownianL2) :
    Tendsto (fun n => chronologicalSum (uniformGrid T n) F G (n + 1)) atTop
      (𝓝 (ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection T F) (pastProjection T G)-
        ProductL2Curry.productTensor gaussianProduct gaussianProduct (pastProjection 0 F) (pastProjection 0 G))) := by
  apply chronologicalSum_tendsto T F G hF (uniformGrid T) (fun n => n + 1)
    (uniformGrid_monotone T) (fun n j hj => ?_) (uniformGrid_zero T) (uniformGrid_end T)
    (fun n => (T : ℝ)/(n + 1)) (uniform_mesh_tendsto T) (fun n i hi => ?_)
  · exact (uniformGrid_monotone T n hj).trans (uniformGrid_end T n).le
  · exact (uniformGrid_distance T n i).le

theorem pastProjection_zero_mean (F : GaussianL2) (hF : F ∈ brownianL2) :
    pastProjection 0 F=(∫ w, F w ∂gaussianProduct) • gaussianOne :=
  tendsto_nhds_unique tendsto_const_nhds
    (GaussianSmallTimeCutoff.pastProjection_small_tendsto F hF (fun _ => 0) tendsto_const_nhds)

/-- Strong native L2 product reconstruction for ANY two independent past L2 observables.
No fourth moments or full Malliavin-domain assumptions occur. -/
theorem past_tensor_reconstruction (T : ℝ≥0) (F G : GaussianL2)
    (hF : F ∈ pastL2 T) (hG : G ∈ pastL2 T) :
    Tendsto (fun n => chronologicalSum (uniformGrid T n) F G (n + 1)) atTop
      (𝓝 (ProductL2Curry.productTensor gaussianProduct gaussianProduct F G-
        ProductL2Curry.productTensor gaussianProduct gaussianProduct
          ((∫ w, F w ∂gaussianProduct) • gaussianOne)
          ((∫ w, G w ∂gaussianProduct) • gaussianOne))) := by
  have hbF := past_mem_brownian T hF
  have hbG := past_mem_brownian T hG
  have he := chronologicalSum_uniform_tendsto T F G hbF
  have hfT : pastProjection T F=F := Submodule.starProjection_eq_self_iff.mpr hF
  have hgT : pastProjection T G=G := Submodule.starProjection_eq_self_iff.mpr hG
  rwa [hfT,hgT,pastProjection_zero_mean F hbF,pastProjection_zero_mean G hbG] at he

theorem pastProjection_mean (s : ℝ≥0) (F : GaussianL2) :
    (∫ w, pastProjection s F w ∂gaussianProduct)=(∫ w, F w ∂gaussianProduct) := by
  have hm (A : GaussianL2) : inner ℝ A gaussianOne=∫ w, A w ∂gaussianProduct :=
    (real_inner_comm A gaussianOne).symm.trans (gaussianOne_inner_eq_integral A)
  have he := (pastL2 s).inner_starProjection_left_eq_right F gaussianOne
  change inner ℝ (pastProjection s F) gaussianOne=inner ℝ F (pastProjection s gaussianOne) at he
  rwa [pastProjection_one,hm,hm] at he

/-- Native predictable mode of an actual conditional-martingale increment. -/
def incrementMode (T : ℝ≥0) (τ : ℕ → ℝ≥0) (F : GaussianL2) (i : ℕ) :
    Lp ℝ 2 (GaussianComplexHorizonIto.predictableMeasure T) :=
  GaussianComplexHorizonIto.trimEquiv T (GaussianFiniteHorizonAdjoint.finiteAdjoint T (cell τ F i))

theorem incrementMode_integral (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F : GaussianL2) (i : ℕ) (hT : τ (i + 1) ≤ T) :
    GaussianComplexHorizonIto.realIto T (incrementMode T τ F i)=cell τ F i := by
  have hp : cell τ F i ∈ pastL2 T :=
    (cell_past τ hτ F i).mono (naturalFiltration.mono hT)
  have hm : (∫ w, cell τ F i w ∂gaussianProduct)=0 := by
    rw [← gaussianOne_inner_eq_integral,cell,inner_sub_right,gaussianOne_inner_eq_integral,
      gaussianOne_inner_eq_integral,pastProjection_mean,pastProjection_mean,sub_self]
  rw [incrementMode,GaussianComplexHorizonIto.realIto_trim,
    GaussianFiniteHorizonAdjoint.finiteAdjoint_representation T _ hp,hm,zero_smul,sub_zero]

/-- Coefficients in the EXISTING full parameterized native domains.
Membership in the narrower common Input remains a density obligation. -/
def leftInput (T : ℝ≥0) (τ : ℕ → ℝ≥0) (F G : GaussianL2) (n : ℕ) :
    StochasticCauchyParameterizedObstruction.Domain T :=
  ∑ i ∈ Finset.range n, tensorInput T (incrementMode T τ F i) (pastProjection (τ i) G)

def rightInput (T : ℝ≥0) (τ : ℕ → ℝ≥0) (F G : GaussianL2) (n : ℕ) :
    StochasticCauchyParameterizedObstruction.Domain T :=
  ∑ i ∈ Finset.range n, tensorInput T (incrementMode T τ G i) (pastProjection (τ i) F)

/-- Agreement with actual two-source stochastic integrals, not just expectations. -/
theorem chronologicalSum_integrals (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (F G : GaussianL2) (n : ℕ) (hT : τ n ≤ T) :
    firstIntegral T (leftInput T τ F G n)+secondIntegral T (rightInput T τ F G n)=
      chronologicalSum τ F G n := by
  classical
  unfold leftInput rightInput chronologicalSum
  rw [map_sum,map_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have ht : τ (i + 1) ≤ T := (hτ (Nat.succ_le_of_lt (Finset.mem_range.mp hi))).trans hT
  rw [first_tensor,second_tensor,incrementMode_integral T τ hτ F i ht,
    incrementMode_integral T τ hτ G i ht]

/-- Stochastic reconstruction of every independent-source past L2 tensor.
This is output convergence, not common-domain coefficient convergence or full PRP. -/
theorem native_past_tensor_reconstruction (T : ℝ≥0) (F G : GaussianL2)
    (hF : F ∈ pastL2 T) (hG : G ∈ pastL2 T) :
    Tendsto (fun n => firstIntegral T (leftInput T (uniformGrid T n) F G (n + 1))+
      secondIntegral T (rightInput T (uniformGrid T n) F G (n + 1))) atTop
      (𝓝 (ProductL2Curry.productTensor gaussianProduct gaussianProduct F G-
        ProductL2Curry.productTensor gaussianProduct gaussianProduct
          ((∫ w, F w ∂gaussianProduct) • gaussianOne)
          ((∫ w, G w ∂gaussianProduct) • gaussianOne))) := by
  apply (past_tensor_reconstruction T F G hF hG).congr'
  exact Eventually.of_forall (fun n => (chronologicalSum_integrals T (uniformGrid T n)
    (uniformGrid_monotone T n) F G (n + 1) (uniformGrid_end T n).le).symm)

end OperatorDerivativeRewrite.Foundation.StochasticCauchyTensorReconstruction
