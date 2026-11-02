import Foundation.StochasticCauchyAnalyticMartingale
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyOccupationEnergy
open InfiniteGaussian StochasticCauchyPhysicalInput StochasticCauchyComplexChannels
open StochasticCauchyExponentialInput StochasticCauchyExitClock StochasticCauchyBrownianRealization
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct
private abbrev ρ (T : ℝ≥0) := (timeMeasure T).prod gaussianProduct

/-- Actual nonnegative time/source occupation density with TRUE survival mask. -/
def density (g : ℂ → ℂ) (R : ℝ) (q : ℝ × Sample) : ℝ :=
  {q : ℝ × Sample | (q.1.toNNReal:WithTop ℝ≥0)≤exitTime R q.2}.indicator
    (fun q => ‖g (value q.1.toNNReal q.2)‖^2) q

/-- Actual source-dependent clock, integrated over the specified finite horizon. -/
def clock (g : ℂ → ℂ) (R : ℝ) (T : ℝ≥0) (w : Sample) : ℝ :=
  ∫ r,density g R (r,w) ∂timeLaw T

theorem density_measurable (g : ℂ → ℂ) (hg : Continuous g) (R : ℝ) : Measurable (density g R) := by
  have ht0 : Measurable (fun q : ℝ × Sample => q.1.toNNReal) := continuous_real_toNNReal.measurable.comp measurable_fst
  have ht : Measurable (fun q : ℝ × Sample => ENNReal.ofReal q.1) := measurable_fst.ennreal_ofReal
  have hτ : Measurable (fun q : ℝ × Sample => StochasticCauchyExitOccupation.exitDuration R q.2) :=
    (exitTime_stopping R).measurable'.comp measurable_snd
  have hv : Measurable (fun q : ℝ × Sample => value q.1.toNNReal q.2) := measurable_uncurry_of_continuous_of_measurable
    (fun w => (StochasticCauchyBrownianRealization.value_continuous w).comp continuous_real_toNNReal)
    (fun r : ℝ => StochasticCauchyBrownianRealization.value_measurable r.toNNReal)
  have hb : Measurable (fun q : ℝ × Sample => ‖g (value q.1.toNNReal q.2)‖^2) := (hg.measurable.comp hv).norm.pow_const 2
  change Measurable ({q : ℝ × Sample | ENNReal.ofReal q.1≤StochasticCauchyExitOccupation.exitDuration R q.2}.indicator
    (fun q => ‖g (value q.1.toNNReal q.2)‖^2))
  exact hb.indicator (measurableSet_le ht hτ)

/-- Physical field identification gives a GENUINE source-clock energy identity.
Joint integrability is established BEFORE either application of Fubini. -/
theorem input_energy_of_physical (T : ℝ≥0) (u : ComplexInput T) (g : ℂ → ℂ) (hg : Continuous g)
    (R : ℝ) (hp : ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,
      (fieldEmbedding T (realInput T u) ((r,w.1),w.2):ℂ)+
        Complex.I*(fieldEmbedding T (imagInput T u) ((r,w.1),w.2):ℂ)=
      {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
        (fun w => g (value r.toNNReal w)) w) :
    Integrable (density g R) ((timeLaw T).prod μ) ∧ Integrable (clock g R T) μ ∧
      ‖u‖^2=∫ w,clock g R T w ∂μ := by
  let F : Lp ℂ 2 (ρ T) := ComplexL2Isometry.combine (ρ T)
    (fieldEmbedding T (realInput T u)) (fieldEmbedding T (imagInput T u))
  let a : ℝ × Sample → (ℝ × SampleSpace) × SampleSpace := fun q => ((q.1,q.2.1),q.2.2)
  have hm : MeasurePreserving a ((timeLaw T).prod μ) (ρ T) := by
    rw [ρ,timeMeasure,PredictableRealL2.horizonMeasure_eq_product]
    exact (measurePreserving_prodAssoc (timeLaw T) gaussianProduct gaussianProduct).symm
  have hi : Integrable (fun q => ‖F (a q)‖^2) ((timeLaw T).prod μ) :=
    hm.integrable_comp_of_integrable (Lp.memLp F).norm.integrable_sq
  have hr := ae_ae_of_ae_prod (hm.quasiMeasurePreserving.ae (ComplexL2Isometry.combine_ae (ρ T)
    (fieldEmbedding T (realInput T u)) (fieldEmbedding T (imagInput T u))))
  let B : ℝ × Sample → ℝ := hi.aestronglyMeasurable.mk (fun q => ‖F (a q)‖^2)
  have hB : StronglyMeasurable B := hi.aestronglyMeasurable.stronglyMeasurable_mk
  have hBF : (fun q => ‖F (a q)‖^2) =ᵐ[(timeLaw T).prod μ] B := hi.aestronglyMeasurable.ae_eq_mk
  have hBr := ae_ae_of_ae_prod hBF
  have heB : B =ᵐ[(timeLaw T).prod μ] density g R := by
    apply (ae_prod_iff_ae_ae (measurableSet_eq_fun hB.measurable (density_measurable g hg R))).mpr
    filter_upwards [hr,hp,hBr] with r hr hp hbr
    filter_upwards [hr,hp,hbr] with w hr hp hbr
    change B (r,w)=density g R (r,w)
    rw [← hbr,hr,hp]
    by_cases hw : (r.toNNReal:WithTop ℝ≥0)≤exitTime R w <;>
      simp only [density,Set.indicator,Set.mem_ofPred_eq,hw,ite_true,ite_false,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
  have he : (fun q => ‖F (a q)‖^2) =ᵐ[(timeLaw T).prod μ] density g R := hBF.trans heB
  have hd : Integrable (density g R) ((timeLaw T).prod μ) := hi.congr he
  refine ⟨hd,hd.integral_prod_right,?_⟩
  calc
    ‖u‖^2 = ‖F‖^2 := by
      dsimp only [F]
      rw [ComplexL2Isometry.combine_norm_sq,(fieldEmbedding T).norm_map,(fieldEmbedding T).norm_map,input_norm_sq]
    _ = ∫ q,‖F q‖^2 ∂ρ T := BochnerL2Dominated.norm_sq_integral F
    _ = ∫ q,‖F (a q)‖^2 ∂(timeLaw T).prod μ :=
      (hm.integral_comp (MeasurableEquiv.prodAssoc : ((ℝ × SampleSpace) × SampleSpace) ≃ᵐ ℝ × (SampleSpace × SampleSpace)).symm.measurableEmbedding _).symm
    _ = ∫ q,density g R q ∂(timeLaw T).prod μ := integral_congr_ae he
    _ = ∫ r,∫ w,density g R (r,w) ∂μ ∂timeLaw T := integral_prod _ hd
    _ = ∫ w,clock g R T w ∂μ := integral_integral_swap hd
private theorem surviving_disk (R : ℝ) (hR : 0≤R) (r : ℝ≥0) (w : Sample)
    (hw : value 0 w=0) (hs : (r:WithTop ℝ≥0)≤exitTime R w) : ‖value r w‖≤R := by
  have hc : clippedClock r (exitTime R) w=r := by
    apply WithTop.coe_injective
    rw [clippedClock_coe,min_eq_right hs]
  have hb := exit_stopped_bound R r w (by rw [hw,norm_zero];exact hR)
  rwa [hc] at hb

private theorem density_local_eq (g h : ℂ → ℂ) (R : ℝ) (hR : 0≤R)
    (he : ∀ z,‖z‖≤R → g z=h z) (r : ℝ) (w : Sample) (hw : value 0 w=0) :
    density g R (r,w)=density h R (r,w) := by
  by_cases hs : (r.toNNReal:WithTop ℝ≥0)≤exitTime R w
  · simp only [density,Set.indicator,Set.mem_ofPred_eq,hs,ite_true]
    rw [he _ (surviving_disk R hR r.toNNReal w hw hs)]
  · simp only [density,Set.indicator,Set.mem_ofPred_eq,hs,ite_false]

/-- Actual local holomorphic occupation clock and its GENUINE joint/source
integrability, using the SAME verified native input. No global f measurability. -/
theorem analytic_input_energy (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) (T : ℝ≥0) :
    Integrable (density (deriv f) R) ((timeLaw T).prod μ) ∧
      Integrable (clock (deriv f) R T) μ ∧
      ‖StochasticCauchyAnalyticDisk.nativeInput f R S hRS hf T‖^2=∫ w,clock (deriv f) R T w ∂μ := by
  obtain ⟨g,hg⟩ := StochasticCauchyAnalyticMartingale.continuous_extension (deriv f) R S hRS (hf.deriv Metric.isOpen_ball)
  let u := StochasticCauchyAnalyticDisk.nativeInput f R S hRS hf T
  have hp := (Classical.choose_spec (StochasticCauchyAnalyticDisk.analytic_ito f R S hRS hf T)).2.1
  change ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,
    (fieldEmbedding T (realInput T u) ((r,w.1),w.2):ℂ)+
      Complex.I*(fieldEmbedding T (imagInput T u) ((r,w.1),w.2):ℂ)=
    {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
      (fun w => deriv f (value r.toNNReal w)) w at hp
  have hpg : ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,
      (fieldEmbedding T (realInput T u) ((r,w.1),w.2):ℂ)+
        Complex.I*(fieldEmbedding T (imagInput T u) ((r,w.1),w.2):ℂ)=
      {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
        (fun w => g (value r.toNNReal w)) w := by
    filter_upwards [hp] with r hr
    filter_upwards [hr,value_zero_ae] with w hh hz
    rw [hh]
    by_cases hs : (r.toNNReal:WithTop ℝ≥0)≤exitTime R w
    · simp only [Set.indicator,Set.mem_ofPred_eq,hs,ite_true]
      exact (hg _ (surviving_disk R R.coe_nonneg r.toNNReal w hz hs)).symm
    · simp only [Set.indicator,Set.mem_ofPred_eq,hs,ite_false]
  obtain ⟨hd,hc,he⟩ := input_energy_of_physical T u g g.continuous R hpg
  have hz : ∀ᵐ q ∂(timeLaw T).prod μ,value 0 q.2=0 :=
    (Measure.quasiMeasurePreserving_snd (μ := timeLaw T) (ν := μ)).ae value_zero_ae
  have hD : density g R =ᵐ[(timeLaw T).prod μ] density (deriv f) R :=
    hz.mono fun q hq => density_local_eq g (deriv f) R R.coe_nonneg hg q.1 q.2 hq
  have hclock : clock g R T =ᵐ[μ] clock (deriv f) R T := by
    filter_upwards [value_zero_ae] with w hw
    change (∫ r,density g R (r,w) ∂timeLaw T)=∫ r,density (deriv f) R (r,w) ∂timeLaw T
    exact integral_congr_ae (Eventually.of_forall fun r => density_local_eq g (deriv f) R R.coe_nonneg hg r w hw)
  have hdf := hd.congr hD
  exact ⟨hdf,hdf.integral_prod_right,he.trans (integral_congr_ae hclock)⟩

theorem density_nonneg (g : ℂ → ℂ) (R : ℝ) (q : ℝ × Sample) : 0≤density g R q := by
  by_cases h : (q.1.toNNReal:WithTop ℝ≥0)≤exitTime R q.2
  · simp only [density,Set.indicator,Set.mem_ofPred_eq,h,ite_true]
    exact sq_nonneg _
  · simp only [density,Set.indicator,Set.mem_ofPred_eq,h,ite_false]
    exact le_refl 0

theorem clock_nonneg (g : ℂ → ℂ) (R : ℝ) (T : ℝ≥0) (w : Sample) : 0≤clock g R T w :=
  integral_nonneg (fun r => density_nonneg g R (r,w))

/-- Actual centered terminal energy equals TWICE the expectation of the actual
stopped physical clock. The factor2 is for Z=B1+iB2, not normalized Z/sqrt2. -/
theorem analytic_variance_energy (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) (T : ℝ≥0) :
    (∫ w,‖f (value (clippedClock T (exitTime R) w) w)-f 0‖^2 ∂μ)=
      2*(∫ w,clock (deriv f) R T w ∂μ) := by
  let u := StochasticCauchyAnalyticDisk.nativeInput f R S hRS hf T
  let α : ℂ := ((Real.sqrt 2:ℝ):ℂ)
  have hα : ‖α‖^2=2 := by
    dsimp only [α]
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  calc
    _ = ‖channel T false (α • u)‖^2 := by
      rw [BochnerL2Dominated.norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [StochasticCauchyAnalyticDisk.nativeInput_actual f R S hRS hf T] with w hw
      rw [hw]
    _ = 2*‖u‖^2 := by rw [(channel T false).norm_map,norm_smul,mul_pow,hα]
    _ = _ := by rw [(analytic_input_energy f R S hRS hf T).2.2]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyOccupationEnergy
