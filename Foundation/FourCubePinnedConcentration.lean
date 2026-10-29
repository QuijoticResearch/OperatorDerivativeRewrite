import Foundation.FourCubePinnedCoercivity

/-! Actual normalized Gibbs concentration on the full pinned cell at identity boundary. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubePinnedConcentration
open QuaternionSU2Representation OneSidedBlockIncidence OneSidedBlockRank
open OneSidedCapComplex FourCubeHaarParity FourCubeHaarChannels FourCubeIntegratedCubic
open FourCubePinnedHaar FourCubePinnedCoercivity
open OneSidedPinnedInterior (pole Free)
attribute [local irreducible] edges upperFaces

private theorem halfTrace_continuous : Continuous halfTrace := by
  have he : halfTrace=fun A : SU2 => ((A : SU2TraceHessianModel.M2) 0 0).re/2+
      ((A : SU2TraceHessianModel.M2) 1 1).re/2 := by
    funext A
    simp [halfTrace,SU2TraceHessianModel.traceReal,Matrix.trace_fin_two,add_div]
  rw [he]
  have hc (i j : Fin 2) : Continuous (fun A : SU2 => (A : SU2TraceHessianModel.M2) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact ((Complex.continuous_re.comp (hc 0 0)).div_const 2).add
    ((Complex.continuous_re.comp (hc 1 1)).div_const 2)

private theorem fill_continuous (e : Interior) :
    Continuous (fun y : PinnedState => fillPole 1 y e) := by
  by_cases h : e=pole
  · simpa only [fillPole,dif_pos h] using (continuous_const : Continuous (fun _ : PinnedState => (1 : SU2)))
  · simpa only [fillPole,dif_neg h] using (continuous_apply (⟨e,h⟩ : Free))

private theorem core_continuous (e : EdgeData) :
    Continuous (fun y : PinnedState => coreField (fillPole 1 y) e) := by
  by_cases h : e∈edges
  · simpa only [coreField,dif_pos h] using fill_continuous (⟨e,h⟩ : Interior)
  · simpa only [coreField,dif_neg h] using (continuous_const : Continuous (fun _ : PinnedState => (1 : SU2)))

private theorem face_continuous (p : FaceData) :
    Continuous (fun y : PinnedState => faceWord (fillPole 1 y) p) :=
  (((core_continuous (p.1,p.2.1)).mul (core_continuous (shifted p.1 p.2.1,p.2.2))).mul
    (core_continuous (shifted p.1 p.2.2,p.2.1)).inv).mul (core_continuous (p.1,p.2.2)).inv

theorem pinnedAction_continuous : Continuous pinnedAction := by
  have hd : Continuous defect := continuous_const.sub halfTrace_continuous
  have hi : Continuous (fun y : PinnedState => internalAction (fillPole 1 y)) := by
    change Continuous (fun y => ∑ p∈innerFaces,defect (faceWord (fillPole 1 y) p))
    exact continuous_finset_sum _ (fun p _ => hd.comp (face_continuous p))
  have hr : Continuous (fun y : PinnedState => ribbonEnergy (fillPole 1 y)) :=
    continuous_finset_sum _ (fun p _ => hd.comp (fill_continuous (ribbonInterior p)))
  have he : pinnedAction=(fun y : PinnedState =>
      internalAction (fillPole 1 y)+ribbonEnergy (fillPole 1 y)) :=
    funext (fun y => vacuum_decomposition (fillPole 1 y))
  rw [he]
  exact hi.add hr

def energySource (y : PinnedState) : ℝ := -pinnedAction y/144

theorem energySource_measurable : Measurable energySource := pinnedAction_measurable.neg.div_const _

theorem energySource_bound (y : PinnedState) : |energySource y| ≤ 1 := by
  have hb := (FourCubeHaarParity.fullAction_bounds (fill (fun _ => 1) (fillPole 1 y))).2
  change pinnedAction y ≤ 144 at hb
  rw [abs_le]
  constructor <;> unfold energySource <;> linarith [pinnedAction_nonneg y]

def normalizer (β : ℝ) : ℝ := pinnedPartition β (fun _ => 1)
def gibbs (β : ℝ) : Measure PinnedState :=
  BoundedExponentialTiltResponse.tiltedMeasure pinnedHaar energySource (144*β)

instance gibbs_probability (β : ℝ) : IsProbabilityMeasure (gibbs β) :=
  BoundedExponentialTiltResponse.tiltedMeasure_probability pinnedHaar energySource
    energySource_measurable energySource_bound (144*β)

theorem normalizer_positive (β : ℝ) : 0<normalizer β := pinnedPartition_positive β _

theorem normalizer_integral (β : ℝ) :
    normalizer β=∫ y,Real.exp (-β*pinnedAction y) ∂pinnedHaar := rfl

theorem tilted_partition_eq (β : ℝ) :
    BoundedExponentialTiltResponse.partition pinnedHaar energySource (144*β)=normalizer β := by
  rw [normalizer_integral]
  unfold BoundedExponentialTiltResponse.partition BoundedExponentialTiltResponse.weighted
  simp only [one_mul]
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  unfold energySource
  ring

theorem gibbs_integral (β : ℝ) (f : PinnedState → ℝ) :
    (∫ y,f y ∂gibbs β)=(∫ y,f y*Real.exp (-β*pinnedAction y) ∂pinnedHaar)/normalizer β := by
  unfold gibbs
  rw [BoundedExponentialTiltResponse.tilted_integral pinnedHaar energySource f
    energySource_measurable energySource_bound (144*β)]
  rw [BoundedExponentialTiltResponse.expectation,tilted_partition_eq]
  unfold BoundedExponentialTiltResponse.weighted
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  congr 1
  unfold energySource
  ring

def lowEnergy (δ : ℝ) : Set PinnedState := {y | pinnedAction y<δ}
def lowMass (δ : ℝ) : ℝ := pinnedHaar.real (lowEnergy δ)

theorem lowEnergy_open (δ : ℝ) : IsOpen (lowEnergy δ) :=
  isOpen_lt pinnedAction_continuous continuous_const

theorem lowMass_positive (δ : ℝ) (hδ : 0<δ) : 0<lowMass δ := by
  letI : Measure.IsOpenPosMeasure pinnedHaar := by unfold pinnedHaar; infer_instance
  have hm : (1 : PinnedState)∈lowEnergy δ := by
    change pinnedAction 1<δ
    rw [(pinnedAction_zero_iff 1).mpr rfl]
    exact hδ
  have hp := IsOpen.measure_pos pinnedHaar (lowEnergy_open δ) ⟨1,hm⟩
  exact ENNReal.toReal_pos hp.ne' (measure_lt_top _ _).ne

theorem normalizer_lower (δ β : ℝ) (hβ : 0 ≤ β) :
    lowMass δ*Real.exp (-β*δ) ≤ normalizer β := by
  have hs := (lowEnergy_open δ).measurableSet
  have hi := FourCubePinnedCoercivity.boltzmann_integrable β
  have hc : Integrable (fun _ : PinnedState => Real.exp (-β*δ)) pinnedHaar := integrable_const _
  have hl : (∫ y in lowEnergy δ,Real.exp (-β*δ) ∂pinnedHaar) ≤
      ∫ y in lowEnergy δ,Real.exp (-β*pinnedAction y) ∂pinnedHaar := by
    apply setIntegral_mono_on hc.integrableOn hi.integrableOn hs
    intro y hy
    apply Real.exp_le_exp.mpr
    change pinnedAction y<δ at hy
    nlinarith
  have ht := setIntegral_le_integral (s := lowEnergy δ) hi
    (Filter.Eventually.of_forall (fun y => (Real.exp_pos (-β*pinnedAction y)).le))
  rw [normalizer_integral]
  have hl' : lowMass δ*Real.exp (-β*δ) ≤
      ∫ y in lowEnergy δ,Real.exp (-β*pinnedAction y) ∂pinnedHaar := by
    simpa [setIntegral_const,lowMass,smul_eq_mul] using hl
  exact hl'.trans ht


def coordinateTail (e : Free) (ε : ℝ) : Set PinnedState := {y | ε ≤ defect (y e)}

theorem coordinateTail_measurable (e : Free) (ε : ℝ) : MeasurableSet (coordinateTail e ε) :=
  tail_event_measurable e ε

theorem gibbs_coordinate_tail_mass (β : ℝ) (e : Free) (ε : ℝ) :
    (gibbs β).real (coordinateTail e ε)=
      (∫ y in coordinateTail e ε,Real.exp (-β*pinnedAction y) ∂pinnedHaar)/normalizer β := by
  let f : PinnedState → ℝ := (coordinateTail e ε).indicator (fun _ => 1)
  have hh := gibbs_integral β f
  have hl : (∫ y,f y ∂gibbs β)=(gibbs β).real (coordinateTail e ε) :=
    integral_indicator_one (coordinateTail_measurable e ε)
  have hr : (∫ y,f y*Real.exp (-β*pinnedAction y) ∂pinnedHaar)=
      ∫ y in coordinateTail e ε,Real.exp (-β*pinnedAction y) ∂pinnedHaar := by
    have he : (fun y => f y*Real.exp (-β*pinnedAction y))=
        (coordinateTail e ε).indicator (fun y => Real.exp (-β*pinnedAction y)) := by
      funext y
      by_cases h : y∈coordinateTail e ε <;> simp [f,h]
    rw [he,integral_indicator (coordinateTail_measurable e ε)]
  rw [hl,hr] at hh
  exact hh

theorem gibbs_coordinate_tail_bound (β ε : ℝ) (hβ : 0 ≤ β) (hε : 0<ε) (e : Free) :
    (gibbs β).real (coordinateTail e ε) ≤ Real.exp (-β*(ε/6))/lowMass (ε/6) := by
  have hc := lowMass_positive (ε/6) (by linarith)
  have hz := normalizer_positive β
  have hd := normalizer_lower (ε/6) β hβ
  have hn := boltzmann_tail_bound β ε hβ e
  rw [gibbs_coordinate_tail_mass]
  apply (div_le_div_iff₀ hz hc).mpr
  calc
    _ ≤ Real.exp (-β*(ε/3))*lowMass (ε/6) := mul_le_mul_of_nonneg_right hn hc.le
    _ = Real.exp (-β*(ε/6))*(lowMass (ε/6)*Real.exp (-β*(ε/6))) := by
      have he : Real.exp (-β*(ε/3))=
          Real.exp (-β*(ε/6))*Real.exp (-β*(ε/6)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le

private theorem exponential_bound_tendsto_zero (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun β : ℝ => Real.exp (-β*(ε/6))/lowMass (ε/6)) atTop (𝓝 0) := by
  have ht : Tendsto (fun β : ℝ => Real.exp ((-(ε/6))*β)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  convert ht.div_const (lowMass (ε/6)) using 1 <;> simp
  funext β
  congr 1
  ring

theorem gibbs_coordinate_tail_tendsto_zero (ε : ℝ) (hε : 0<ε) (e : Free) :
    Tendsto (fun β : ℝ => (gibbs β).real (coordinateTail e ε)) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun β => measureReal_nonneg)) ?_
    (exponential_bound_tendsto_zero ε hε)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
  exact gibbs_coordinate_tail_bound β ε hβ hε e

def configurationTail (ε : ℝ) : Set PinnedState := ⋃ e : Free,coordinateTail e ε

theorem configurationTail_measurable (ε : ℝ) : MeasurableSet (configurationTail ε) :=
  MeasurableSet.iUnion (fun e => coordinateTail_measurable e ε)

theorem gibbs_configuration_tail_bound (β ε : ℝ) (hβ : 0 ≤ β) (hε : 0<ε) :
    (gibbs β).real (configurationTail ε) ≤
      31*(Real.exp (-β*(ε/6))/lowMass (ε/6)) := by
  have hu := measureReal_iUnion_fintype_le (μ := gibbs β) (fun e : Free => coordinateTail e ε)
  have hs := Finset.sum_le_sum (fun (e : Free) (_ : e∈Finset.univ) =>
    gibbs_coordinate_tail_bound β ε hβ hε e)
  have he : (∑ _e : Free,Real.exp (-β*(ε/6))/lowMass (ε/6))=
      31*(Real.exp (-β*(ε/6))/lowMass (ε/6)) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [OneSidedPinnedInterior.free_card]
    norm_num
  exact hu.trans (hs.trans_eq he)

theorem gibbs_configuration_tail_tendsto_zero (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun β : ℝ => (gibbs β).real (configurationTail ε)) atTop (𝓝 0) := by
  have hu := (exponential_bound_tendsto_zero ε hε).const_mul (31 : ℝ)
  simp only [mul_zero] at hu
  apply squeeze_zero' (Filter.Eventually.of_forall (fun β => measureReal_nonneg)) ?_ hu
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
  exact gibbs_configuration_tail_bound β ε hβ hε

/-- Simultaneously, every one of the31 pinned links has defect below epsilon with probability
approaching1 under the ACTUAL normalized full-cell Gibbs law. -/
theorem gibbs_configuration_good_tendsto_one (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun β : ℝ => (gibbs β).real (configurationTail ε)ᶜ) atTop (𝓝 1) := by
  have he (β : ℝ) : (gibbs β).real (configurationTail ε)ᶜ=
      1-(gibbs β).real (configurationTail ε) := by
    rw [measureReal_compl (configurationTail_measurable ε)]
    simp
  simp_rw [he]
  simpa using tendsto_const_nhds.sub (gibbs_configuration_tail_tendsto_zero ε hε)

end OperatorDerivativeRewrite.Foundation.FourCubePinnedConcentration
