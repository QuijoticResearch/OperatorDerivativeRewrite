import Foundation.IBMTerminalBracketWeights

/-! Actual terminal-dependent uniform Riemann occupation sums. Finite cells
are identified with literal Lebesgue integrals before any limit is taken. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTerminalRiemannOccupation
open InfiniteGaussian GaussianBrownianQuadraticVariation IBMClockOverlapEnergy
open IBMConstructedSources IBMRandomTerminalBoundary

def step (φ : ℝ × ℝ → ℝ) (T : ℝ≥0) (N : ℕ) (z : ℝ × SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), (Ioc (uniformTime T N i.castSucc:ℝ) (uniformTime T N i.succ:ℝ)).indicator
    (fun _ => φ (clockPath z.2 (uniformTime T N i.castSucc),clockPath z.2 T)) z.1

private theorem step_on_cell (φ : ℝ × ℝ → ℝ) (T : ℝ≥0) (N : ℕ)
    (i : Fin (N+1)) (t : ℝ) (Y : SampleSpace)
    (ht : t ∈ Ioc (uniformTime T N i.castSucc:ℝ) (uniformTime T N i.succ:ℝ)) :
    step φ T N (t,Y) = φ (clockPath Y (uniformTime T N i.castSucc),clockPath Y T) := by
  rw [step,Finset.sum_eq_single i,indicator_of_mem ht]
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    rcases lt_or_gt_of_ne hji with h | h
    · have he : (uniformTime T N j.succ:ℝ) ≤ uniformTime T N i.castSucc :=
        uniformTime_monotone T N (Fin.succ_le_castSucc_iff.mpr h)
      linarith [ht.1,hj.2]
    · have he : (uniformTime T N i.succ:ℝ) ≤ uniformTime T N j.castSucc :=
        uniformTime_monotone T N (Fin.succ_le_castSucc_iff.mpr h)
      linarith [hj.1,ht.2]
  · simp

private theorem step_bound (φ : ℝ × ℝ → ℝ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (T : ℝ≥0) (N : ℕ) (t : ℝ) (Y : SampleSpace) (ht : t ∈ Ioc 0 (T:ℝ)) :
    ‖step φ T N (t,Y)‖ ≤ 1 := by
  obtain ⟨i,hi⟩ := GaussianQuadraticIto.uniformTime_covers T N t ht
  rw [step_on_cell φ T N i t Y hi]
  exact hb _

private theorem left_nodes_tendsto (T : ℝ≥0) (t : ℝ) (ht : t ∈ Ioc 0 (T:ℝ))
    (i : (N : ℕ) → Fin (N+1))
    (hi : ∀ N, t ∈ Ioc (uniformTime T N (i N).castSucc:ℝ) (uniformTime T N (i N).succ:ℝ)) :
    Tendsto (fun N => uniformTime T N (i N).castSucc) atTop (𝓝 t.toNNReal) := by
  have hb (N : ℕ) : ‖(uniformTime T N (i N).castSucc:ℝ)-t‖ ≤ (T:ℝ)/(N+1) := by
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (hi N).1.le)]
    have hs := uniformTime_step T N (i N)
    linarith [(hi N).2]
  have hr := tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun N => norm_nonneg _) hb
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)))
  have hn := continuous_real_toNNReal.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def,Real.toNNReal_coe] using hn

private theorem node_measurable (t : ℝ≥0) : Measurable (fun Y => clockPath Y t) :=
  (ContinuousMap.measurable_eval t).comp clockPath_measurable

theorem step_measurable (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (T : ℝ≥0) (N : ℕ) :
    Measurable (step φ T N) := by
  apply Finset.measurable_sum
  intro i hi
  have hm : Measurable (fun z : ℝ × SampleSpace => φ
      (clockPath z.2 (uniformTime T N i.castSucc),clockPath z.2 T)) :=
    hφ.comp (((node_measurable (uniformTime T N i.castSucc)).comp measurable_snd).prodMk
    ((node_measurable T).comp measurable_snd))
  exact Measurable.ite ((measurableSet_Ioc).preimage measurable_fst) hm measurable_const

def pathSum (φ : ℝ × ℝ → ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ((T:ℝ)/(N+1))*∑ i : Fin (N+1), φ (clockPath Y (uniformTime T N i.castSucc),clockPath Y T)

private theorem cell_subset (T : ℝ≥0) (N : ℕ) (i : Fin (N+1)) :
    Ioc (uniformTime T N i.castSucc:ℝ) (uniformTime T N i.succ:ℝ) ⊆ Ioc 0 (T:ℝ) := by
  intro t ht
  have he := uniformTime_monotone T N (Fin.le_last i.succ)
  rw [(uniformTime_endpoints T N).2] at he
  exact ⟨lt_of_le_of_lt (uniformTime T N i.castSucc).property ht.1,ht.2.trans he⟩

theorem step_integral (φ : ℝ × ℝ → ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    (∫ t, step φ T N (t,Y) ∂window T) = pathSum φ T N Y := by
  have hi (i : Fin (N+1)) : Integrable
      ((Ioc (uniformTime T N i.castSucc:ℝ) (uniformTime T N i.succ:ℝ)).indicator
        (fun _ : ℝ => φ (clockPath Y (uniformTime T N i.castSucc),clockPath Y T))) (window T) :=
    (integrable_const _).indicator measurableSet_Ioc
  unfold step
  rw [integral_finset_sum _ (fun i _ => hi i)]
  simp only [integral_indicator_const _ measurableSet_Ioc,smul_eq_mul]
  have hm (i : Fin (N+1)) : (window T).real
      (Ioc (uniformTime T N i.castSucc:ℝ) (uniformTime T N i.succ:ℝ)) = (T:ℝ)/(N+1) := by
    rw [Measure.real,window,Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr (cell_subset T N i),Real.volume_Ioc,uniformTime_step]
    exact ENNReal.toReal_ofReal (by positivity)
  simp only [hm]
  exact (Finset.mul_sum _ _ _).symm

theorem pathSum_bound (φ : ℝ × ℝ → ℝ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ‖pathSum φ T N Y‖ ≤ T := by
  rw [← step_integral]
  have h := norm_integral_le_of_norm_le_const (μ:=window (T:ℝ))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht; exact step_bound φ hb T N t Y ht)
  simpa [window,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal T.property] using h

def actualSum (φ : ℝ × ℝ → ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ((T:ℝ)/(N+1))*∑ i : Fin (N+1), φ (GaussianTimeProcess.process (uniformTime T N i.castSucc) Y,
    GaussianTimeProcess.process T Y)

theorem actualSum_eq_pathSum (φ : ℝ × ℝ → ℝ) (T : ℝ≥0) (N : ℕ) :
    actualSum φ T N =ᵐ[gaussianProduct] pathSum φ T N := by
  filter_upwards [ae_all_iff.mpr (fun i : Fin (N+1) => clockPath_coordinate_ae (uniformTime T N i.castSucc)),
    clockPath_coordinate_ae T] with Y hi hT
  unfold actualSum pathSum
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [hi i,hT]

theorem actualSum_measurable (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (T : ℝ≥0) (N : ℕ) :
    Measurable (actualSum φ T N) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun i _ => hφ.comp
    ((GaussianTimeProcess.process_stronglyMeasurable _).measurable.prodMk
      (GaussianTimeProcess.process_stronglyMeasurable _).measurable)

theorem actualSum_memLp (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (T : ℝ≥0) (N : ℕ) : MemLp (actualSum φ T N) 2 gaussianProduct := by
  apply MemLp.of_bound (actualSum_measurable φ hφ T N).aestronglyMeasurable T
  filter_upwards [actualSum_eq_pathSum φ T N] with Y hY
  rw [hY]
  exact pathSum_bound φ hb T N Y

def sumClass (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (T : ℝ≥0) (N : ℕ) : GaussianL2 := (actualSum_memLp φ hφ hb T N).toLp _

theorem sumClass_actual (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (T : ℝ≥0) (N : ℕ) : sumClass φ hφ hb T N =ᵐ[gaussianProduct] actualSum φ T N :=
  (actualSum_memLp φ hφ hb T N).coeFn_toLp

theorem outer_pathSum_tendsto_ae (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, Tendsto (fun N => pathSum (IBMTerminalBracketWeights.outerBand (δ N)) T N Y)
      atTop (𝓝 0) := by
  filter_upwards [distance_positive_ae T] with Y hY
  have ht : ∀ᵐ t ∂window T, Tendsto
      (fun N => step (IBMTerminalBracketWeights.outerBand (δ N)) T N (t,Y)) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hY,ae_restrict_mem measurableSet_Ioc] with t hd ht
    choose i hi using fun N => GaussianQuadraticIto.uniformTime_covers T N t ht
    have hn := (clockPath Y).continuous.continuousAt.tendsto.comp (left_nodes_tendsto T t ht i hi)
    have hc := ((continuous_abs.continuousAt.tendsto.comp hn).sub
      (tendsto_const_nhds (x:=abs (clockPath Y T)))).abs
    change Tendsto (fun N => abs (abs (clockPath Y (uniformTime T N (i N).castSucc))-
      abs (clockPath Y T))) atTop (𝓝 (distance T (t,Y))) at hc
    have h1 := (tendsto_order.1 hc).1 (distance T (t,Y)/2) (by linarith)
    have h2 := (tendsto_order.1 hδ).2 (distance T (t,Y)/2) (by linarith)
    apply (tendsto_const_nhds (x:=(0:ℝ))).congr'
    filter_upwards [h1,h2] with N h1 h2
    rw [step_on_cell _ T N (i N) t Y (hi N)]
    unfold IBMTerminalBracketWeights.outerBand
    rw [if_neg (by linarith)]
  have hi := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
    (fun N => ((step_measurable _ (IBMTerminalBracketWeights.outerBand_measurable (δ N)) T N).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (integrable_const (1:ℝ) : Integrable _ (window T))
    (fun N => by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
                 exact step_bound _ (IBMTerminalBracketWeights.outerBand_bound (δ N)) T N t Y ht) ht
  simpa only [Function.comp_def,id_eq,step_integral,integral_zero] using hi

theorem outer_actualSum_tendsto_ae (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, Tendsto
      (fun N => actualSum (IBMTerminalBracketWeights.outerBand (δ N)) T N Y) atTop (𝓝 0) := by
  filter_upwards [outer_pathSum_tendsto_ae δ hδ T,
    ae_all_iff.mpr (fun N => actualSum_eq_pathSum (IBMTerminalBracketWeights.outerBand (δ N)) T N)]
      with Y hY he
  exact hY.congr' (Eventually.of_forall fun N => (he N).symm)

theorem outer_sumClass_tendsto (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun N => sumClass (IBMTerminalBracketWeights.outerBand (δ N))
      (IBMTerminalBracketWeights.outerBand_measurable (δ N))
      (IBMTerminalBracketWeights.outerBand_bound (δ N)) T N) atTop (𝓝 (0:GaussianL2)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (Lp.const 2 gaussianProduct (T:ℝ))
  · intro N
    filter_upwards [sumClass_actual _ (IBMTerminalBracketWeights.outerBand_measurable (δ N))
        (IBMTerminalBracketWeights.outerBand_bound (δ N)) T N,
      actualSum_eq_pathSum (IBMTerminalBracketWeights.outerBand (δ N)) T N,
      Lp.coeFn_const 2 gaussianProduct (T:ℝ)] with Y h1 h2 hb
    rw [h1,h2,hb]
    change ‖pathSum _ T N Y‖ ≤ ‖(T:ℝ)‖
    exact (pathSum_bound _ (IBMTerminalBracketWeights.outerBand_bound (δ N)) T N Y).trans
      (Real.le_norm_self (T:ℝ))
  · filter_upwards [Lp.coeFn_zero ℝ 2 gaussianProduct] with Y hz
    rw [hz]
    simp only [Pi.zero_apply,norm_zero]
    exact norm_nonneg _
  · filter_upwards [outer_actualSum_tendsto_ae δ hδ T,
      ae_all_iff.mpr (fun N => sumClass_actual _ (IBMTerminalBracketWeights.outerBand_measurable (δ N))
        (IBMTerminalBracketWeights.outerBand_bound (δ N)) T N),Lp.coeFn_zero ℝ 2 gaussianProduct]
          with Y hY he hz
    rw [hz]
    exact hY.congr' (Eventually.of_forall fun N => (he N).symm)

theorem outer_mean_tendsto (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun N => ∫ Y, actualSum (IBMTerminalBracketWeights.outerBand (δ N)) T N Y
      ∂gaussianProduct) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun _ : SampleSpace => (T:ℝ))
    (fun N => (actualSum_measurable _ (IBMTerminalBracketWeights.outerBand_measurable (δ N)) T N).aestronglyMeasurable)
    (integrable_const (T:ℝ))
    (fun N => (actualSum_eq_pathSum (IBMTerminalBracketWeights.outerBand (δ N)) T N).mono
      (fun Y hY => by rw [hY]; exact pathSum_bound _ (IBMTerminalBracketWeights.outerBand_bound (δ N)) T N Y))
    (outer_actualSum_tendsto_ae δ hδ T)
  simpa only [integral_zero] using h

def originBand (δ : ℝ) (x : ℝ × ℝ) : ℝ := if abs x.1 ≤ δ then 1 else 0

theorem originBand_measurable (δ : ℝ) : Measurable (originBand δ) :=
  Measurable.ite (measurableSet_le (continuous_abs.measurable.comp measurable_fst)
    measurable_const) measurable_const measurable_const

theorem originBand_bound (δ : ℝ) (x : ℝ × ℝ) : ‖originBand δ x‖ ≤ 1 := by
  unfold originBand
  split_ifs <;> norm_num

theorem origin_pathSum_tendsto_ae (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, Tendsto (fun N => pathSum (originBand (δ N)) T N Y) atTop (𝓝 0) := by
  have hm : MeasurableSet {z : ℝ × SampleSpace | BrownianClockWeightedEnergy.sigma z ≠ 0} :=
    (measurableSet_eq_fun BrownianClockWeightedEnergy.sigma_measurable measurable_const).compl
  have hz := BrownianClockWeightedEnergy.sigma_nonzero T
  change ∀ᵐ z ∂PredictableRealL2.horizonMeasure T gaussianProduct,
    BrownianClockWeightedEnergy.sigma z ≠ 0 at hz
  rw [PredictableRealL2.horizonMeasure_eq_product] at hz
  have hy := (Measure.ae_ae_comm hm).mp ((Measure.ae_prod_iff_ae_ae hm).mp hz)
  filter_upwards [hy] with Y hY
  have ht : ∀ᵐ t ∂window T, Tendsto (fun N => step (originBand (δ N)) T N (t,Y)) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hY,ae_restrict_mem measurableSet_Ioc] with t hn ht
    change clockPath Y t.toNNReal ≠ 0 at hn
    have hp : 0 < abs (clockPath Y t.toNNReal) := abs_pos.mpr hn
    choose i hi using fun N => GaussianQuadraticIto.uniformTime_covers T N t ht
    have hc := (continuous_abs.continuousAt.tendsto.comp
      ((clockPath Y).continuous.continuousAt.tendsto.comp (left_nodes_tendsto T t ht i hi)))
    change Tendsto (fun N => abs (clockPath Y (uniformTime T N (i N).castSucc)))
      atTop (𝓝 (abs (clockPath Y t.toNNReal))) at hc
    have h1 := (tendsto_order.1 hc).1 (abs (clockPath Y t.toNNReal)/2) (by linarith)
    have h2 := (tendsto_order.1 hδ).2 (abs (clockPath Y t.toNNReal)/2) (by linarith)
    apply (tendsto_const_nhds (x:=(0:ℝ))).congr'
    filter_upwards [h1,h2] with N h1 h2
    rw [step_on_cell _ T N (i N) t Y (hi N)]
    unfold originBand
    rw [if_neg (by change ¬abs (clockPath Y (uniformTime T N (i N).castSucc)) ≤ δ N; linarith)]
  have hi := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
    (fun N => ((step_measurable _ (originBand_measurable (δ N)) T N).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (integrable_const (1:ℝ) : Integrable _ (window T))
    (fun N => by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
                 exact step_bound _ (originBand_bound (δ N)) T N t Y ht) ht
  simpa only [Function.comp_def,id_eq,step_integral,integral_zero] using hi

theorem origin_actualSum_tendsto_ae (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, Tendsto (fun N => actualSum (originBand (δ N)) T N Y) atTop (𝓝 0) := by
  filter_upwards [origin_pathSum_tendsto_ae δ hδ T,
    ae_all_iff.mpr (fun N => actualSum_eq_pathSum (originBand (δ N)) T N)] with Y hY he
  exact hY.congr' (Eventually.of_forall fun N => (he N).symm)

theorem origin_mean_tendsto (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun N => ∫ Y, actualSum (originBand (δ N)) T N Y ∂gaussianProduct) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun _ : SampleSpace => (T:ℝ))
    (fun N => (actualSum_measurable _ (originBand_measurable (δ N)) T N).aestronglyMeasurable)
    (integrable_const (T:ℝ))
    (fun N => (actualSum_eq_pathSum (originBand (δ N)) T N).mono
      (fun Y hY => by rw [hY]; exact pathSum_bound _ (originBand_bound (δ N)) T N Y))
    (origin_actualSum_tendsto_ae δ hδ T)
  simpa only [integral_zero] using h

def interiorValue (T : ℝ≥0) (z : ℝ × SampleSpace) : ℝ :=
  IBMTerminalBracketWeights.interior (clockPath z.2 z.1.toNNReal,clockPath z.2 T)

theorem interiorValue_measurable (T : ℝ≥0) : Measurable (interiorValue T) :=
  IBMTerminalBracketWeights.interior_measurable.comp
    (BrownianClockWeightedEnergy.sigma_measurable.prodMk ((node_measurable T).comp measurable_snd))

def interiorIntegral (T : ℝ≥0) (Y : SampleSpace) : ℝ := ∫ t, interiorValue T (t,Y) ∂window T

theorem interiorIntegral_measurable (T : ℝ≥0) : Measurable (interiorIntegral T) :=
  (interiorValue_measurable T).stronglyMeasurable.integral_prod_left'.measurable

theorem interiorIntegral_norm_bound (T : ℝ≥0) (Y : SampleSpace) : ‖interiorIntegral T Y‖ ≤ T := by
  have h := norm_integral_le_of_norm_le_const (μ:=window (T:ℝ))
    (ae_of_all _ fun t => IBMTerminalBracketWeights.interior_bound
      (clockPath Y t.toNNReal,clockPath Y T))
  simpa [interiorIntegral,interiorValue,window,Measure.real,Real.volume_Ioc,
    ENNReal.toReal_ofReal T.property] using h

theorem interiorIntegral_bounds (T : ℝ≥0) (Y : SampleSpace) :
    0 ≤ interiorIntegral T Y ∧ interiorIntegral T Y ≤ T := by
  have hn : 0 ≤ interiorIntegral T Y := by
    apply integral_nonneg
    intro t
    change 0 ≤ IBMTerminalBracketWeights.interior (clockPath Y t.toNNReal,clockPath Y T)
    unfold IBMTerminalBracketWeights.interior
    split_ifs <;> norm_num
  exact ⟨hn,(Real.le_norm_self _).trans (interiorIntegral_norm_bound T Y)⟩

theorem interior_memLp (T : ℝ≥0) : MemLp (interiorIntegral T) 2 gaussianProduct :=
  MemLp.of_bound (interiorIntegral_measurable T).aestronglyMeasurable T
    (ae_of_all _ fun Y => interiorIntegral_norm_bound T Y)

def interiorClass (T : ℝ≥0) : GaussianL2 := (interior_memLp T).toLp _

theorem interiorClass_actual (T : ℝ≥0) : interiorClass T =ᵐ[gaussianProduct] interiorIntegral T :=
  (interior_memLp T).coeFn_toLp

theorem interior_pathSum_tendsto_ae (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, Tendsto
      (fun N => pathSum IBMTerminalBracketWeights.interior T N Y) atTop (𝓝 (interiorIntegral T Y)) := by
  filter_upwards [distance_positive_ae T] with Y hY
  have ht : ∀ᵐ t ∂window T, Tendsto
      (fun N => step IBMTerminalBracketWeights.interior T N (t,Y)) atTop (𝓝 (interiorValue T (t,Y))) := by
    filter_upwards [hY,ae_restrict_mem measurableSet_Ioc] with t hd ht
    choose i hi using fun N => GaussianQuadraticIto.uniformTime_covers T N t ht
    have hc := continuous_abs.continuousAt.tendsto.comp
      ((clockPath Y).continuous.continuousAt.tendsto.comp (left_nodes_tendsto T t ht i hi))
    change Tendsto (fun N => abs (clockPath Y (uniformTime T N (i N).castSucc)))
      atTop (𝓝 (abs (clockPath Y t.toNNReal))) at hc
    by_cases hr : abs (clockPath Y t.toNNReal) < abs (clockPath Y T)
    · have he := (tendsto_order.1 hc).2 (abs (clockPath Y T)) hr
      rw [show interiorValue T (t,Y)=1 by simp [interiorValue,IBMTerminalBracketWeights.interior,hr]]
      apply (tendsto_const_nhds (x:=(1:ℝ))).congr'
      filter_upwards [he] with N hN
      rw [step_on_cell _ T N (i N) t Y (hi N)]
      simp only [IBMTerminalBracketWeights.interior,if_pos hN]
    · have hn : abs (clockPath Y t.toNNReal) ≠ abs (clockPath Y T) :=
        sub_ne_zero.mp (abs_pos.mp hd)
      have hl : abs (clockPath Y T) < abs (clockPath Y t.toNNReal) :=
        lt_of_le_of_ne (le_of_not_gt hr) hn.symm
      have he := (tendsto_order.1 hc).1 (abs (clockPath Y T)) hl
      rw [show interiorValue T (t,Y)=0 by simp [interiorValue,IBMTerminalBracketWeights.interior,hr]]
      apply (tendsto_const_nhds (x:=(0:ℝ))).congr'
      filter_upwards [he] with N hN
      rw [step_on_cell _ T N (i N) t Y (hi N)]
      simp only [IBMTerminalBracketWeights.interior,if_neg (not_lt_of_ge hN.le)]
  have hi := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
    (fun N => ((step_measurable _ IBMTerminalBracketWeights.interior_measurable T N).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (integrable_const (1:ℝ) : Integrable _ (window T))
    (fun N => by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
                 exact step_bound _ IBMTerminalBracketWeights.interior_bound T N t Y ht) ht
  simpa only [Function.comp_def,id_eq,step_integral,interiorIntegral] using hi

theorem interior_actualSum_tendsto_ae (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, Tendsto (fun N => actualSum IBMTerminalBracketWeights.interior T N Y)
      atTop (𝓝 (interiorIntegral T Y)) := by
  filter_upwards [interior_pathSum_tendsto_ae T,
    ae_all_iff.mpr (fun N => actualSum_eq_pathSum IBMTerminalBracketWeights.interior T N)] with Y hY he
  exact hY.congr' (Eventually.of_forall fun N => (he N).symm)

theorem interior_sumClass_tendsto (T : ℝ≥0) :
    Tendsto (sumClass IBMTerminalBracketWeights.interior IBMTerminalBracketWeights.interior_measurable
      IBMTerminalBracketWeights.interior_bound T) atTop (𝓝 (interiorClass T)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (Lp.const 2 gaussianProduct (T:ℝ))
  · intro N
    filter_upwards [sumClass_actual _ IBMTerminalBracketWeights.interior_measurable
        IBMTerminalBracketWeights.interior_bound T N,
      actualSum_eq_pathSum IBMTerminalBracketWeights.interior T N,Lp.coeFn_const 2 gaussianProduct (T:ℝ)]
        with Y h1 h2 hb
    rw [h1,h2,hb]
    change ‖pathSum _ T N Y‖ ≤ ‖(T:ℝ)‖
    exact (pathSum_bound _ IBMTerminalBracketWeights.interior_bound T N Y).trans (Real.le_norm_self (T:ℝ))
  · filter_upwards [interiorClass_actual T,Lp.coeFn_const 2 gaussianProduct (T:ℝ)] with Y hi hb
    rw [hi,hb]
    change ‖interiorIntegral T Y‖ ≤ ‖(T:ℝ)‖
    exact (interiorIntegral_norm_bound T Y).trans (Real.le_norm_self (T:ℝ))
  · filter_upwards [interior_actualSum_tendsto_ae T,interiorClass_actual T,
      ae_all_iff.mpr (fun N => sumClass_actual _ IBMTerminalBracketWeights.interior_measurable
        IBMTerminalBracketWeights.interior_bound T N)] with Y hY hg he
    rw [hg]
    exact hY.congr' (Eventually.of_forall fun N => (he N).symm)

theorem interior_mean_tendsto (T : ℝ≥0) :
    Tendsto (fun N => ∫ Y, actualSum IBMTerminalBracketWeights.interior T N Y ∂gaussianProduct)
      atTop (𝓝 (∫ Y, interiorIntegral T Y ∂gaussianProduct)) := by
  have h := tendsto_integral_of_dominated_convergence (fun _ : SampleSpace => (T:ℝ))
    (fun N => (actualSum_measurable _ IBMTerminalBracketWeights.interior_measurable T N).aestronglyMeasurable)
    (integrable_const (T:ℝ))
    (fun N => (actualSum_eq_pathSum IBMTerminalBracketWeights.interior T N).mono
      (fun Y hY => by rw [hY]; exact pathSum_bound _ IBMTerminalBracketWeights.interior_bound T N Y))
    (interior_actualSum_tendsto_ae T)
  exact h

end OperatorDerivativeRewrite.Foundation.IBMTerminalRiemannOccupation
