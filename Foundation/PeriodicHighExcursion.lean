import Foundation.PeriodicHighActionKernel
import Foundation.PeriodicHighActionSchur
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
/-! Genuine finite killed Wilson laws and quantitative high-excursion control.
Every intermediate transition is restricted. No unrestricted P-power or
continuum physical-time identification is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicHighExcursion
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicHighActionL2 PeriodicHighActionKernel
attribute [local irreducible] spatialAction temporalAction boundaryHaar kernel
def region (β K : ℝ) : Set State := {U | K<β*spatialAction U}
private theorem region_measurable (β K : ℝ) : MeasurableSet (region β K) :=
  measurableSet_lt measurable_const (spatial_action_measurable.const_mul β)
variable {β : ℝ} (g : GroundData β) (K : ℝ)
private instance stationary_prob : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance transition_markov : IsMarkovKernel g.transition := g.transition_markov

def killed : Kernel State State := g.transition.restrict (region_measurable β K)
private instance killed_finite : IsFiniteKernel (killed g K) := by
  unfold killed
  infer_instance

private theorem killed_mass_le (U : State) : killed g K U Set.univ ≤ 1 := by
  rw [killed,Kernel.restrict_apply' _ _ _ MeasurableSet.univ,Set.univ_inter]
  exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)

theorem power_mass_le (n : ℕ) (U : State) : ((killed g K)^n) U Set.univ ≤ 1 := by
  induction n generalizing U with
  | zero => simp only [pow_zero]; change Measure.dirac U Set.univ ≤ 1; simp
  | succ n ih =>
    rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ MeasurableSet.univ]
    calc
      _ ≤ ∫⁻ _V, (1:ℝ≥0∞) ∂((killed g K)^n) U := lintegral_mono (fun V => killed_mass_le g K V)
      _ = ((killed g K)^n) U Set.univ := by simp
      _ ≤ 1 := ih U

private instance power_finite (n : ℕ) : IsFiniteKernel ((killed g K)^n) :=
  ⟨⟨1,by simp,power_mass_le g K n⟩⟩

/-- Actual finite surviving measure: start in the high region, kill at every
subsequent transition, and retain the endpoint after n steps. -/
def survivingLaw (n : ℕ) : Measure State :=
  (((killed g K)^n) : Kernel State State) ∘ₘ (g.stationary.restrict (region β K))
private instance surviving_finite (n : ℕ) : IsFiniteMeasure (survivingLaw g K n) := by
  unfold survivingLaw
  infer_instance

def survival (n : ℕ) : State → ℝ :=
  cut β K (fun U => (((killed g K)^n) U Set.univ).toReal)

theorem survival_zero : survival g K 0=cut β K (fun _ => (1:ℝ)) := by
  unfold survival
  congr 1
  funext U
  change (Measure.dirac U Set.univ).toReal=1
  simp

theorem survival_succ (n : ℕ) : survival g K (n+1)=cut β K (transfer g (survival g K n)) := by
  unfold survival
  apply congrArg (cut β K)
  funext U
  have h : (∫ _V : State,(1:ℝ) ∂((killed g K)^(n+1)) U)=
      ∫ V,∫ _W : State,(1:ℝ) ∂((killed g K)^n) V ∂killed g K U := by
    rw [pow_succ]
    exact Kernel.integral_comp (integrable_const (1:ℝ))
  simp only [integral_const,smul_eq_mul,mul_one,measureReal_def] at h
  rw [h]
  change (∫ V,(((killed g K)^n) V Set.univ).toReal ∂(g.transition U).restrict (region β K))=_
  rw [← integral_indicator (region_measurable β K)]
  rfl

private theorem survival_measurable (n : ℕ) : Measurable (survival g K n) :=
  cut_measurable β K _ ((Kernel.measurable_coe _ MeasurableSet.univ).ennreal_toReal)

theorem survival_bounds (n : ℕ) (U : State) : 0 ≤ survival g K n U ∧ survival g K n U ≤ 1 := by
  by_cases h : K<β*spatialAction U
  · have hh : U∈{V : State | K<β*spatialAction V} := h
    simp only [survival,cut,Set.indicator_of_mem hh]
    exact ⟨ENNReal.toReal_nonneg,by simpa using ENNReal.toReal_mono (by simp) (power_mass_le g K n U)⟩
  · simp [survival,cut,h]

private theorem survival_bound (n : ℕ) (U : State) : |survival g K n U| ≤ 1 := by
  rw [abs_of_nonneg (survival_bounds g K n U).1]
  exact (survival_bounds g K n U).2

private theorem survival_memLp (n : ℕ) : MemLp (survival g K n) 2 g.stationary :=
  MemLp.of_bound (survival_measurable g K n).aestronglyMeasurable 1
    (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using survival_bound g K n U))

private theorem survival_physical (n : ℕ) :
    ∀ a U,survival g K n (PeriodicSlabGauge.gaugeAction a U)=survival g K n U := by
  cases n with
  | zero =>
    rw [survival_zero]
    intro a U
    simp only [cut,Set.indicator_apply,Set.mem_ofPred_eq,PeriodicSlabGauge.spatial_action_invariant]
  | succ n =>
    rw [survival_succ]
    intro a U
    simp only [cut,Set.indicator_apply,Set.mem_ofPred_eq,PeriodicSlabGauge.spatial_action_invariant,transfer_physical]

private theorem survival_support (n : ℕ) : ∀ U,β*spatialAction U ≤ K → survival g K n U=0 := by
  intro U hU
  have hh : ¬K<β*spatialAction U := not_lt.mpr hU
  simp [survival,cut,hh]

def highVector (n : ℕ) : completed g K :=
  ⟨(survival_memLp g K n).toLp (survival g K n),
    mem_completed g _ (survival_measurable g K n) (survival_memLp g K n)
      (survival_physical g K n) K (ae_of_all _ (survival_support g K n))⟩

attribute [local irreducible] represented completed operator compression

theorem compression_step (n : ℕ) : highVector g K (n+1)=compression g K (highVector g K n) := by
  have he : ((compression g K (highVector g K n) : completed g K) : StateL2 g)=
      (cut_memLp g K (transfer g (survival g K n))
        (transfer_memLp g _ (survival_measurable g K n) 1 (survival_bound g K n))).toLp
          (cut β K (transfer g (survival g K n))) :=
    compression_toLp g K (survival g K n) (survival_measurable g K n)
      (survival_memLp g K n) 1 (survival_bound g K n) (survival_physical g K n)
        (ae_of_all _ (survival_support g K n))
  apply Subtype.ext
  rw [he]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (survival_memLp g K (n+1)),
    MemLp.coeFn_toLp (cut_memLp g K (transfer g (survival g K n))
      (transfer_memLp g _ (survival_measurable g K n) 1 (survival_bound g K n)))] with U hU hV
  change ((survival_memLp g K (n+1)).toLp (survival g K (n+1))) U=_
  rw [hU,hV,survival_succ]

theorem native_powers (n : ℕ) : highVector g K n=((compression g K)^n) (highVector g K 0) := by
  induction n with
  | zero => simp
  | succ n ih => rw [compression_step,ih,pow_succ']; rfl

theorem mass_identity (n : ℕ) : (survivingLaw g K n).real Set.univ=
    ∫ U,survival g K n U ∂g.stationary := by
  have h : (∫ _V : State,(1:ℝ) ∂survivingLaw g K n)=
      ∫ U,∫ _V : State,(1:ℝ) ∂((killed g K)^n) U ∂g.stationary.restrict (region β K) := by
    unfold survivingLaw
    rw [Measure.comp_eq_comp_const_apply]
    exact Kernel.integral_comp (integrable_const (1:ℝ))
  simp only [integral_const,smul_eq_mul,mul_one] at h
  rw [h]
  exact (integral_indicator (region_measurable β K)).symm

/-- The finite surviving mass is the actual compressed-operator pairing. -/
theorem mass_pairing (n : ℕ) : (survivingLaw g K n).real Set.univ=
    inner ℝ (highVector g K n) (highVector g K 0) := by
  rw [mass_identity]
  symm
  change inner ℝ ((highVector g K n : completed g K) : StateL2 g)
    ((highVector g K 0 : completed g K) : StateL2 g)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (survival_memLp g K n),
    MemLp.coeFn_toLp (survival_memLp g K 0)] with U hN h0
  change inner ℝ (((survival_memLp g K n).toLp (survival g K n)) U)
    (((survival_memLp g K 0).toLp (survival g K 0)) U)=_
  rw [hN,h0,survival_zero]
  by_cases h : K<β*spatialAction U <;> simp [survival,cut,h]

theorem initial_norm : ‖highVector g K 0‖^2=g.stationary.real (region β K) := by
  rw [← real_inner_self_eq_norm_sq,← mass_pairing,mass_identity,survival_zero]
  change (∫ U,(region β K).indicator (fun _ => (1:ℝ)) U ∂g.stationary)=_
  rw [integral_indicator (region_measurable β K),setIntegral_const]
  simp

theorem mass_le_initial (n : ℕ) : (survivingLaw g K n).real Set.univ ≤
    g.stationary.real (region β K) := by
  have hp : ∀ U,survival g K n U ≤ survival g K 0 U := by
    intro U
    rw [survival_zero]
    by_cases h : K<β*spatialAction U
    · have hh : U∈{V : State | K<β*spatialAction V} := h
      simpa only [cut,Set.indicator_of_mem hh] using (survival_bounds g K n U).2
    · rw [survival_support g K n U (le_of_not_gt h)]
      simp [cut,h]
  calc
    _ = ∫ U,survival g K n U ∂g.stationary := mass_identity g K n
    _ ≤ ∫ U,survival g K 0 U ∂g.stationary :=
      integral_mono ((survival_memLp g K n).integrable (by norm_num))
        ((survival_memLp g K 0).integrable (by norm_num)) hp
    _ = inner ℝ (highVector g K 0) (highVector g K 0) :=
      (mass_identity g K 0).symm.trans (mass_pairing g K 0)
    _ = ‖highVector g K 0‖^2 := real_inner_self_eq_norm_sq _
    _ = _ := initial_norm g K

/-- Geometric decay of genuine surviving measures in the original lattice-step
count. Indicators are inserted at EVERY intermediate transition. -/
theorem geometric_mass (hb : 16777216 ≤ β) (n : ℕ) :
    (survivingLaw g PeriodicHighActionSchur.threshold n).real Set.univ ≤
      (1/2 : ℝ)^n*g.stationary.real (region β PeriodicHighActionSchur.threshold) := by
  let K := PeriodicHighActionSchur.threshold
  let C : completed g K →L[ℝ] completed g K := compression g K
  let F : completed g K := highVector g K 0
  have hC : ‖C‖ ≤ (1/2 : ℝ) := compression_half hb g
  have hp : ∀ j : ℕ,‖(C^j : completed g K →L[ℝ] completed g K)‖ ≤ (1/2 : ℝ)^j := by
    intro j
    induction j with
    | zero =>
      change ‖(1 : completed g K →L[ℝ] completed g K)‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    | succ j ih =>
      calc
        ‖(C^(j+1) : completed g K →L[ℝ] completed g K)‖ ≤ ‖C^j‖*‖C‖ := by
          rw [pow_succ]
          exact norm_mul_le (C^j : completed g K →L[ℝ] completed g K) C
        _ ≤ (1/2 : ℝ)^j*(1/2) := mul_le_mul ih hC (norm_nonneg C) (by positivity)
        _ = (1/2 : ℝ)^(j+1) := (pow_succ _ _).symm
  have hn : ‖(C^n) F‖ ≤ (1/2 : ℝ)^n*‖F‖ :=
    ((C^n).le_opNorm F).trans (mul_le_mul_of_nonneg_right (hp n) (norm_nonneg F))
  change (survivingLaw g K n).real Set.univ ≤ _
  calc
    _ = inner ℝ ((C^n) F) F := by rw [mass_pairing,native_powers]
    _ ≤ ‖(C^n) F‖*‖F‖ := real_inner_le_norm _ _
    _ ≤ ((1/2 : ℝ)^n*‖F‖)*‖F‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg F)
    _ = (1/2 : ℝ)^n*‖F‖^2 := by ring
    _ = _ := by rw [initial_norm]

/-- Summability of actual finite surviving masses, with a coupling-uniform
bound relative to the actual stationary high mass. No exit time is postulated. -/
theorem total_surviving_mass (hb : 16777216 ≤ β) :
    Summable (fun n : ℕ => (survivingLaw g PeriodicHighActionSchur.threshold n).real Set.univ) ∧
      (∑' n : ℕ,(survivingLaw g PeriodicHighActionSchur.threshold n).real Set.univ) ≤
        2*g.stationary.real (region β PeriodicHighActionSchur.threshold) := by
  let M := g.stationary.real (region β PeriodicHighActionSchur.threshold)
  have hr : ‖(1/2 : ℝ)‖ < 1 := by norm_num
  have hbs : Summable (fun n : ℕ => (1/2 : ℝ)^n*M) :=
    (summable_geometric_of_norm_lt_one hr).mul_right M
  have has : Summable (fun n : ℕ => (survivingLaw g PeriodicHighActionSchur.threshold n).real Set.univ) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) (geometric_mass g hb) hbs
  refine ⟨has,?_⟩
  calc
    _ ≤ ∑' n : ℕ,(1/2 : ℝ)^n*M := has.tsum_le_tsum (geometric_mass g hb) hbs
    _ = 2*M := by rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hr]; norm_num

end OperatorDerivativeRewrite.Foundation.PeriodicHighExcursion
