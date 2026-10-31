import Foundation.PeriodicGaussianTransferGram
import Foundation.PeriodicHighMassAnchor
/-! Actual physical-event persistence and half stationary mass at the logarithmic
Wilson high-resolvent cutoff. Gaussian native positivity supplies the premise
missing from the generic reversible argument. Arbitrary-cutoff exponential tails follow from the same mechanism. No mixing or gap is inferred. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicPositiveMassAnchor
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicHighExcursion PeriodicHighActionL2
attribute [local irreducible] spatialAction temporalAction operator represented completed compression
private instance prob {β : ℝ} (g : GroundData β) : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance markov {β : ℝ} (g : GroundData β) : IsMarkovKernel g.transition := g.transition_markov
private instance edge_prob {β : ℝ} (g : GroundData β) : IsProbabilityMeasure (edgeLaw g) := by unfold edgeLaw; infer_instance

theorem physical_event_lower {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (A : Set State)
    (hA : MeasurableSet A)
    (hInv : ∀ a U, PeriodicSlabGauge.gaugeAction a U ∈ A ↔ U ∈ A) :
    g.stationary.real A ^ 2 ≤ (edgeLaw g).real (A.prod A) := by
  let I : State → ℝ := A.indicator (fun _ => 1)
  let a : ℝ := g.stationary.real A
  let f : State → ℝ := fun U => I U-a
  have hI : Measurable I := measurable_const.indicator hA
  have hIb (U : State) : |I U| ≤ 1 := by
    by_cases hU : U ∈ A <;> simp [I,hU]
  have hf : Measurable f := hI.sub measurable_const
  have hfb (U : State) : |f U| ≤ 1+|a| := by
    dsimp only [f]
    have h := abs_sub (I U) a
    linarith [hIb U]
  have hm : MemLp f 2 g.stationary :=
    MemLp.of_bound hf.aestronglyMeasurable (1+|a|) (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using hfb U))
  have hfi : ∀ b U, f (PeriodicSlabGauge.gaugeAction b U)=f U := by
    intro b U
    by_cases hU : U ∈ A
    · have hG := (hInv b U).mpr hU
      simp only [f,I,Set.indicator_of_mem hU,Set.indicator_of_mem hG]
    · have hG : PeriodicSlabGauge.gaugeAction b U ∉ A := fun h => hU ((hInv b U).mp h)
      simp only [f,I,Set.indicator_of_notMem hU,Set.indicator_of_notMem hG]
  have hp := PeriodicGaussianTransferGram.native_nonnegative hb g f hf hm (1+|a|) hfb hfi
  rw [operator_pairing] at hp
  have hL := (left_preserving g).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hm)
  have hR := (right_preserving g).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hm)
  have he : (∫ p, (hm.toLp f) p.1*(hm.toLp f) p.2 ∂edgeLaw g)=
      ∫ p, (I p.1-a)*(I p.2-a) ∂edgeLaw g := by
    apply integral_congr_ae
    filter_upwards [hL,hR] with p h1 h2
    change (hm.toLp f) p.1=f p.1 at h1
    change (hm.toLp f) p.2=f p.2 at h2
    rw [h1,h2]
  rw [he] at hp
  have hi : Integrable I g.stationary := Integrable.of_bound hI.aestronglyMeasurable 1
    (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using hIb U))
  have hl : Integrable (fun p : State × State => I p.1) (edgeLaw g) :=
    (left_preserving g).integrable_comp_of_integrable hi
  have hr : Integrable (fun p : State × State => I p.2) (edgeLaw g) :=
    (right_preserving g).integrable_comp_of_integrable hi
  have hleft : (∫ p, I p.1 ∂edgeLaw g)=a := by
    rw [← integral_map measurable_fst.aemeasurable hI.aestronglyMeasurable,(left_preserving g).map_eq]
    exact integral_indicator_one hA
  have hright : (∫ p, I p.2 ∂edgeLaw g)=a := by
    rw [← integral_map measurable_snd.aemeasurable hI.aestronglyMeasurable,(right_preserving g).map_eq]
    exact integral_indicator_one hA
  have hprod : (fun p : State × State => I p.1*I p.2)=
      (A.prod A).indicator (fun _ => (1:ℝ)) := by
    funext p
    by_cases h1 : p.1 ∈ A
    · by_cases h2 : p.2 ∈ A
      · have hp : p ∈ A.prod A := ⟨h1,h2⟩
        rw [Set.indicator_of_mem hp]
        simp only [I,Set.indicator_of_mem h1,Set.indicator_of_mem h2,mul_one]
      · have hp : p ∉ A.prod A := fun h => h2 h.2
        rw [Set.indicator_of_notMem hp]
        simp only [I,Set.indicator_of_mem h1,Set.indicator_of_notMem h2,mul_zero]
    · have hp : p ∉ A.prod A := fun h => h1 h.1
      rw [Set.indicator_of_notMem hp]
      simp only [I,Set.indicator_of_notMem h1,zero_mul]
  have hiProd : Integrable (fun p : State × State => I p.1*I p.2) (edgeLaw g) := by
    rw [hprod]
    exact (integrable_const (1:ℝ)).indicator (hA.prod hA)
  have hprodInt : (∫ p : State × State,I p.1*I p.2 ∂edgeLaw g)=(edgeLaw g).real (A.prod A) := by
    rw [hprod]
    exact integral_indicator_one (hA.prod hA)
  have hexpand : (fun p : State × State => (I p.1-a)*(I p.2-a))=
      ((fun p => I p.1*I p.2)-(fun p => a*I p.1)-(fun p => a*I p.2))+(fun _ => a^2) := by
    funext p
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  rw [hexpand] at hp
  change 0 ≤ ∫ p : State × State, ((I p.1*I p.2-a*I p.1)-a*I p.2)+a^2 ∂edgeLaw g at hp
  have hs1 : Integrable (fun p : State × State => I p.1*I p.2-a*I p.1) (edgeLaw g) :=
    hiProd.sub (hl.const_mul a)
  have hs2 : Integrable (fun p : State × State => I p.1*I p.2-a*I p.1-a*I p.2) (edgeLaw g) :=
    hs1.sub (hr.const_mul a)
  rw [integral_add hs2 (integrable_const _),
    integral_sub hs1 (hr.const_mul a),
    integral_sub hiProd (hl.const_mul a),integral_const_mul,integral_const_mul,hleft,hright,hprodInt] at hp
  simp only [integral_const,probReal_univ,one_smul] at hp
  change a^2 ≤ _
  nlinarith only [hp]

theorem high_mass {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    g.stationary.real (region β PeriodicHighActionSchur.threshold) ≤ (1/2 : ℝ) := by
  let K := PeriodicHighActionSchur.threshold
  have hA : MeasurableSet (region β K) :=
    measurableSet_lt measurable_const (spatial_action_measurable.const_mul β)
  have hi : ∀ a U, PeriodicSlabGauge.gaugeAction a U ∈ region β K ↔ U ∈ region β K := by
    intro a U
    simp only [region,Set.mem_ofPred_eq,PeriodicSlabGauge.spatial_action_invariant]
  have hl := physical_event_lower (by linarith : 0 ≤ β) g (region β K) hA hi
  rw [← PeriodicHighMassAnchor.one_step_event] at hl
  have hu := geometric_mass g hb 1
  simp only [pow_one] at hu
  change g.stationary.real (region β K) ≤ _
  nlinarith [measureReal_nonneg (μ := g.stationary) (s := region β K)]

theorem low_mass {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    (1/2 : ℝ) ≤ g.stationary.real {U | β*spatialAction U ≤ PeriodicHighActionSchur.threshold} := by
  let A := region β PeriodicHighActionSchur.threshold
  have hA : MeasurableSet A := measurableSet_lt measurable_const (spatial_action_measurable.const_mul β)
  have hc : Aᶜ={U | β*spatialAction U ≤ PeriodicHighActionSchur.threshold} := by
    ext U
    simp only [A,region,Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt]
  have h := measureReal_add_measureReal_compl (μ := g.stationary) hA
  rw [hc,probReal_univ] at h
  have hu := high_mass hb g
  linarith
theorem exponential_tail {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) (K : ℝ) :
    g.stationary.real (region β K) ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-K) := by
  have hA : MeasurableSet (region β K) := measurableSet_lt measurable_const (spatial_action_measurable.const_mul β)
  have hi : ∀ b U, PeriodicSlabGauge.gaugeAction b U ∈ region β K ↔ U ∈ region β K := by
    intro b U
    simp only [region,Set.mem_ofPred_eq,PeriodicSlabGauge.spatial_action_invariant]
  have hl := physical_event_lower (by linarith : 0 ≤ β) g (region β K) hA hi
  rw [← PeriodicHighMassAnchor.one_step_event] at hl
  let F : completed g K := highVector g K 0
  have hq : (survivingLaw g K 1).real Set.univ=inner ℝ (operator g (F : StateL2 g)) (F : StateL2 g) := by
    calc
      _ = inner ℝ (highVector g K 1) (highVector g K 0) := mass_pairing g K 1
      _ = inner ℝ (compression g K F) F := by rw [compression_step g K 0]
      _ = _ := compression_pairing g K F F
  have hu := completed_bound hb g K (F : StateL2 g) F.property
  have hn : ‖(F : StateL2 g)‖^2=g.stationary.real (region β K) := initial_norm g K
  rw [← hq,hn] at hu
  have hh := hl.trans ((le_abs_self _).trans hu)
  by_cases hz : g.stationary.real (region β K)=0
  · rw [hz]
    exact mul_nonneg
      (div_pos PeriodicGroundHaarScale.upperConstant_pos PeriodicGaugeSaturatedGround.eigenLowerConstant_pos).le
      (Real.exp_pos _).le
  · have hp : 0 < g.stationary.real (region β K) := lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ hp).mp
    simpa only [pow_two] using hh
end OperatorDerivativeRewrite.Foundation.PeriodicPositiveMassAnchor
