import Foundation.IBMTerminalRiemannOccupation

/-! Actual occupation samples on horizon H with a SEPARATE clock observation R.
Riemann limits use proved random-level noncollision, not an assumed path law. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMObservedClockOccupation
open InfiniteGaussian GaussianBrownianQuadraticVariation IBMClockOverlapEnergy
open IBMConstructedSources IBMRandomTerminalBoundary IBMTerminalBracketWeights
open IBMTerminalRiemannOccupation

private def sampledStep (φ : ℝ × ℝ → ℝ) (H R : ℝ≥0) (N : ℕ) (z : ℝ × SampleSpace) : ℝ :=
  step (fun x => φ (x.1,clockPath z.2 R)) H N z

def sampledPathSum (φ : ℝ × ℝ → ℝ) (H R : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  pathSum (fun x => φ (x.1,clockPath Y R)) H N Y

private theorem sampledStep_measurable (φ : ℝ × ℝ → ℝ) (hm : Measurable φ)
    (H R : ℝ≥0) (N : ℕ) : Measurable (sampledStep φ H R N) := by
  unfold sampledStep step
  apply Finset.measurable_sum
  intro i hi
  have hn (t : ℝ≥0) : Measurable (fun Y => clockPath Y t) :=
    (ContinuousMap.measurable_eval t).comp clockPath_measurable
  exact Measurable.ite ((measurableSet_Ioc).preimage measurable_fst)
    (hm.comp (((hn _).comp measurable_snd).prodMk ((hn R).comp measurable_snd))) measurable_const

theorem sampledPathSum_bound (φ : ℝ × ℝ → ℝ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (H R : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ‖sampledPathSum φ H R N Y‖ ≤ H :=
  pathSum_bound _ (fun x => hb _) H N Y

def sampledSum (φ : ℝ × ℝ → ℝ) (H R : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ((H:ℝ)/(N+1))*∑ i : Fin (N+1), φ
    (GaussianTimeProcess.process (uniformTime H N i.castSucc) Y,GaussianTimeProcess.process R Y)

theorem sampledSum_eq_pathSum (φ : ℝ × ℝ → ℝ) (H R : ℝ≥0) (N : ℕ) :
    sampledSum φ H R N =ᵐ[gaussianProduct] sampledPathSum φ H R N := by
  filter_upwards [ae_all_iff.mpr (fun i : Fin (N+1) => clockPath_coordinate_ae (uniformTime H N i.castSucc)),
    clockPath_coordinate_ae R] with Y hi hR
  unfold sampledSum sampledPathSum pathSum
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [hi i,hR]

theorem sampledSum_measurable (φ : ℝ × ℝ → ℝ) (hm : Measurable φ) (H R : ℝ≥0) (N : ℕ) :
    Measurable (sampledSum φ H R N) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun i _ => hm.comp
    ((GaussianTimeProcess.process_stronglyMeasurable _).measurable.prodMk
      (GaussianTimeProcess.process_stronglyMeasurable R).measurable)

theorem sampledSum_memLp (φ : ℝ × ℝ → ℝ) (hm : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (H R : ℝ≥0) (N : ℕ) : MemLp (sampledSum φ H R N) 2 gaussianProduct := by
  apply MemLp.of_bound (sampledSum_measurable φ hm H R N).aestronglyMeasurable H
  filter_upwards [sampledSum_eq_pathSum φ H R N] with Y hY
  rw [hY]
  exact sampledPathSum_bound φ hb H R N Y

def sampledClass (φ : ℝ × ℝ → ℝ) (hm : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (H R : ℝ≥0) (N : ℕ) : GaussianL2 := (sampledSum_memLp φ hm hb H R N).toLp _

theorem sampledClass_actual (φ : ℝ × ℝ → ℝ) (hm : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (H R : ℝ≥0) (N : ℕ) : sampledClass φ hm hb H R N =ᵐ[gaussianProduct] sampledSum φ H R N :=
  (sampledSum_memLp φ hm hb H R N).coeFn_toLp

theorem distance_positive_on_window (H R : ℝ≥0) (hHR : H ≤ R) :
    ∀ᵐ Y ∂gaussianProduct, ∀ᵐ t ∂window H, 0 < distance R (t,Y) := by
  have hw : window H ≤ window R := Measure.restrict_mono_set volume
    (Ioc_subset_Ioc le_rfl (show (H:ℝ) ≤ R from hHR))
  exact (distance_positive_ae R).mono fun Y hY => hY.filter_mono (ae_mono hw)

theorem outer_sampledPathSum_tendsto_ae (H R : ℝ≥0) (hHR : H ≤ R)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ᵐ Y ∂gaussianProduct, Tendsto (fun N => sampledPathSum (outerBand (δ N)) H R N Y) atTop (𝓝 0) := by
  filter_upwards [distance_positive_on_window H R hHR] with Y hY
  have ht : ∀ᵐ t ∂window H, Tendsto (fun N => sampledStep (outerBand (δ N)) H R N (t,Y))
      atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hY,ae_restrict_mem measurableSet_Ioc] with t hd ht
    choose i hi using fun N => GaussianQuadraticIto.uniformTime_covers H N t ht
    have hc := ((continuous_abs.continuousAt.tendsto.comp
      ((clockPath Y).continuous.continuousAt.tendsto.comp (uniform_left_nodes_tendsto H t ht i hi))).sub
        (tendsto_const_nhds (x:=abs (clockPath Y R)))).abs
    change Tendsto (fun N => abs (abs (clockPath Y (uniformTime H N (i N).castSucc))-
      abs (clockPath Y R))) atTop (𝓝 (distance R (t,Y))) at hc
    have h1 := (tendsto_order.1 hc).1 (distance R (t,Y)/2) (by linarith)
    have h2 := (tendsto_order.1 hδ).2 (distance R (t,Y)/2) (by linarith)
    apply (tendsto_const_nhds (x:=(0:ℝ))).congr'
    filter_upwards [h1,h2] with N h1 h2
    rw [sampledStep,step_value_on_cell _ H N (i N) t Y (hi N)]
    unfold outerBand
    rw [if_neg (by change ¬abs (abs (clockPath Y (uniformTime H N (i N).castSucc))-
      abs (clockPath Y R)) ≤ δ N; linarith)]
  have hi := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
    (fun N => ((sampledStep_measurable _ (outerBand_measurable (δ N)) H R N).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (integrable_const (1:ℝ) : Integrable _ (window H))
    (fun N => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      change ‖step (fun x => outerBand (δ N) (x.1,clockPath Y R)) H N (t,Y)‖ ≤ 1
      exact step_norm_on_window _ (fun x => outerBand_bound (δ N) (x.1,clockPath Y R)) H N t Y ht) ht
  simpa only [Function.comp_def,id_eq,sampledStep,step_integral,integral_zero,sampledPathSum] using hi

private theorem class_tendsto_of_path (φ : ℕ → ℝ × ℝ → ℝ) (hm : ∀ N, Measurable (φ N))
    (hb : ∀ N x, ‖φ N x‖ ≤ 1) (H R : ℝ≥0) (f : SampleSpace → ℝ) (g : GaussianL2)
    (hg : g =ᵐ[gaussianProduct] f) (hf : ∀ Y, ‖f Y‖ ≤ H)
    (hpath : ∀ᵐ Y ∂gaussianProduct, Tendsto (fun N => sampledPathSum (φ N) H R N Y) atTop (𝓝 (f Y))) :
    Tendsto (fun N => sampledClass (φ N) (hm N) (hb N) H R N) atTop (𝓝 g) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (Lp.const 2 gaussianProduct (H:ℝ))
  · intro N
    filter_upwards [sampledClass_actual _ (hm N) (hb N) H R N,
      sampledSum_eq_pathSum (φ N) H R N,Lp.coeFn_const 2 gaussianProduct (H:ℝ)] with Y hc hs hH
    rw [hc,hs,hH]
    exact (sampledPathSum_bound _ (hb N) H R N Y).trans (Real.le_norm_self (H:ℝ))
  · filter_upwards [hg,Lp.coeFn_const 2 gaussianProduct (H:ℝ)] with Y hY hH
    rw [hY,hH]
    exact (hf Y).trans (Real.le_norm_self (H:ℝ))
  · filter_upwards [hpath,hg,
      ae_all_iff.mpr (fun N => sampledClass_actual _ (hm N) (hb N) H R N),
      ae_all_iff.mpr (fun N => sampledSum_eq_pathSum (φ N) H R N)] with Y hY hg hc hs
    rw [hg]
    exact hY.congr' (Eventually.of_forall fun N => ((hc N).trans (hs N)).symm)

theorem outer_sampledClass_tendsto (H R : ℝ≥0) (hHR : H ≤ R)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N => sampledClass (outerBand (δ N)) (outerBand_measurable (δ N))
      (outerBand_bound (δ N)) H R N) atTop (𝓝 (0:GaussianL2)) :=
  class_tendsto_of_path _ (fun N => outerBand_measurable (δ N))
    (fun N => outerBand_bound (δ N)) H R (fun _ => 0) 0 (Lp.coeFn_zero ℝ 2 gaussianProduct)
    (fun Y => by simp only [norm_zero]; exact H.property) (outer_sampledPathSum_tendsto_ae H R hHR δ hδ)

def occupationValue (R : ℝ≥0) (z : ℝ × SampleSpace) : ℝ :=
  IBMTerminalBracketWeights.interior (clockPath z.2 z.1.toNNReal,clockPath z.2 R)

def occupation (H R : ℝ≥0) (Y : SampleSpace) : ℝ := ∫ t, occupationValue R (t,Y) ∂window H

theorem occupation_measurable (H R : ℝ≥0) : Measurable (occupation H R) :=
  (interiorValue_measurable R).stronglyMeasurable.integral_prod_left'.measurable

theorem occupation_norm_bound (H R : ℝ≥0) (Y : SampleSpace) : ‖occupation H R Y‖ ≤ H := by
  have h := norm_integral_le_of_norm_le_const (μ:=window (H:ℝ))
    (ae_of_all _ fun t => interior_bound (clockPath Y t.toNNReal,clockPath Y R))
  simpa [occupation,occupationValue,window,Measure.real,Real.volume_Ioc,
    ENNReal.toReal_ofReal H.property] using h

theorem occupation_memLp (H R : ℝ≥0) : MemLp (occupation H R) 2 gaussianProduct :=
  MemLp.of_bound (occupation_measurable H R).aestronglyMeasurable H
    (ae_of_all _ fun Y => occupation_norm_bound H R Y)

def occupationL2 (H R : ℝ≥0) : GaussianL2 := (occupation_memLp H R).toLp _

theorem occupationL2_actual (H R : ℝ≥0) : occupationL2 H R =ᵐ[gaussianProduct] occupation H R :=
  (occupation_memLp H R).coeFn_toLp

theorem interior_sampledPathSum_tendsto_ae (H R : ℝ≥0) (hHR : H ≤ R) :
    ∀ᵐ Y ∂gaussianProduct, Tendsto
      (fun N => sampledPathSum IBMTerminalBracketWeights.interior H R N Y) atTop (𝓝 (occupation H R Y)) := by
  filter_upwards [distance_positive_on_window H R hHR] with Y hY
  have ht : ∀ᵐ t ∂window H, Tendsto
      (fun N => sampledStep IBMTerminalBracketWeights.interior H R N (t,Y))
      atTop (𝓝 (occupationValue R (t,Y))) := by
    filter_upwards [hY,ae_restrict_mem measurableSet_Ioc] with t hd ht
    choose i hi using fun N => GaussianQuadraticIto.uniformTime_covers H N t ht
    have hc := continuous_abs.continuousAt.tendsto.comp
      ((clockPath Y).continuous.continuousAt.tendsto.comp (uniform_left_nodes_tendsto H t ht i hi))
    change Tendsto (fun N => abs (clockPath Y (uniformTime H N (i N).castSucc)))
      atTop (𝓝 (abs (clockPath Y t.toNNReal))) at hc
    by_cases hr : abs (clockPath Y t.toNNReal) < abs (clockPath Y R)
    · have he := (tendsto_order.1 hc).2 (abs (clockPath Y R)) hr
      rw [show occupationValue R (t,Y)=1 by simp [occupationValue,IBMTerminalBracketWeights.interior,hr]]
      apply (tendsto_const_nhds (x:=(1:ℝ))).congr'
      filter_upwards [he] with N hN
      rw [sampledStep,step_value_on_cell _ H N (i N) t Y (hi N)]
      simp only [IBMTerminalBracketWeights.interior,if_pos hN]
    · have hn : abs (clockPath Y t.toNNReal) ≠ abs (clockPath Y R) := sub_ne_zero.mp (abs_pos.mp hd)
      have hl : abs (clockPath Y R) < abs (clockPath Y t.toNNReal) := lt_of_le_of_ne (le_of_not_gt hr) hn.symm
      have he := (tendsto_order.1 hc).1 (abs (clockPath Y R)) hl
      rw [show occupationValue R (t,Y)=0 by simp [occupationValue,IBMTerminalBracketWeights.interior,hr]]
      apply (tendsto_const_nhds (x:=(0:ℝ))).congr'
      filter_upwards [he] with N hN
      rw [sampledStep,step_value_on_cell _ H N (i N) t Y (hi N)]
      simp only [IBMTerminalBracketWeights.interior,if_neg (not_lt_of_ge hN.le)]
  have hi := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
    (fun N => ((sampledStep_measurable _ interior_measurable H R N).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (integrable_const (1:ℝ) : Integrable _ (window H))
    (fun N => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      change ‖step (fun x => IBMTerminalBracketWeights.interior (x.1,clockPath Y R)) H N (t,Y)‖ ≤ 1
      exact step_norm_on_window _ (fun x => interior_bound (x.1,clockPath Y R)) H N t Y ht) ht
  simpa only [Function.comp_def,id_eq,sampledStep,step_integral,occupation,occupationValue,
    sampledPathSum] using hi

theorem interior_sampledClass_tendsto (H R : ℝ≥0) (hHR : H ≤ R) :
    Tendsto (sampledClass IBMTerminalBracketWeights.interior interior_measurable interior_bound H R)
      atTop (𝓝 (occupationL2 H R)) :=
  class_tendsto_of_path (fun _ => IBMTerminalBracketWeights.interior) (fun _ => interior_measurable)
    (fun _ => interior_bound) H R _ _ (occupationL2_actual H R) (occupation_norm_bound H R)
    (interior_sampledPathSum_tendsto_ae H R hHR)

end OperatorDerivativeRewrite.Foundation.IBMObservedClockOccupation
