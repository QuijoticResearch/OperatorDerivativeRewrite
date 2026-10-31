import Foundation.PeriodicHighActionL2
import Foundation.PeriodicPlaquetteSeamSelection
/-! Exact hard-action projection on the represented physical native L2 domain,
and agreement of the actual high compression with the killed transfer kernel.
No hard-indicator claim is made for arbitrary ambient nonphysical classes. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicHighActionKernel
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicHighActionL2
attribute [local irreducible] spatialAction temporalAction boundaryHaar kernel

def cut (β K : ℝ) (f : State → ℝ) : State → ℝ := {U | K<β*spatialAction U}.indicator f

private theorem region_measurable (β K : ℝ) : MeasurableSet {U : State | K<β*spatialAction U} :=
  measurableSet_lt measurable_const (spatial_action_measurable.const_mul β)

theorem cut_measurable (β K : ℝ) (f : State → ℝ) (hf : Measurable f) :
    Measurable (cut β K f) := hf.indicator (region_measurable β K)

theorem cut_memLp {β : ℝ} (g : GroundData β) (K : ℝ) (f : State → ℝ)
    (hm : MemLp f 2 g.stationary) : MemLp (cut β K f) 2 g.stationary :=
  hm.indicator (region_measurable β K)

private theorem cut_physical (β K : ℝ) (f : State → ℝ)
    (hi : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    ∀ a U,cut β K f (PeriodicSlabGauge.gaugeAction a U)=cut β K f U := by
  intro a U
  simp only [cut,Set.indicator_apply,Set.mem_ofPred_eq,PeriodicSlabGauge.spatial_action_invariant,hi]

private theorem cut_support (β K : ℝ) (f : State → ℝ) :
    ∀ U,β*spatialAction U ≤ K → cut β K f U=0 := by
  intro U hU
  have hh : U∉{V : State | K<β*spatialAction V} := not_lt.mpr hU
  exact Set.indicator_of_notMem hh f

attribute [local irreducible] represented completed operator

/-- Every native class vanishing AE on the high region is orthogonal to the
defined physical high completion; no physicality of this LOW class is required. -/
theorem low_support_orthogonal {β : ℝ} (g : GroundData β) (K : ℝ) (G : StateL2 g)
    (hG : ∀ᵐ U ∂g.stationary,K<β*spatialAction U → G U=0) :
    G∈(completed g K).toSubmoduleᗮ := by
  apply ((completed g K).toSubmodule.mem_orthogonal G).mpr
  intro F hF
  have hc : IsClosed {F : StateL2 g | inner ℝ F G=0} :=
    isClosed_eq (continuous_id.inner (𝕜 := ℝ) continuous_const) continuous_const
  have hrepr : (represented g K : Set (StateL2 g)) ⊆ {F | inner ℝ F G=0} := by
    intro F hF
    unfold represented at hF
    rcases hF with ⟨f,hf,hm,_,hs,he⟩
    change inner ℝ F G=0
    rw [← he,L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [MemLp.coeFn_toLp hm,hs,hG] with U hU hS hT
    rw [hU]
    by_cases h : K<β*spatialAction U
    · simp only [hT h,inner_zero_right,Pi.zero_apply]
    · simp only [hS (le_of_not_gt h),inner_zero_left,Pi.zero_apply]
  have hh := closure_minimal hrepr hc
  unfold completed at hF
  exact hh hF

/-- The actual orthogonal projection is exactly the high indicator on every
measurable pointwise-physical native L2 representative, including unbounded ones. -/
theorem projection_toLp {β : ℝ} (g : GroundData β) (K : ℝ) (f : State → ℝ)
    (hf : Measurable f) (hm : MemLp f 2 g.stationary)
    (hi : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    (completed g K).toSubmodule.starProjection (hm.toLp f)=
      (cut_memLp g K f hm).toLp (cut β K f) := by
  let F := hm.toLp f
  let H := (cut_memLp g K f hm).toLp (cut β K f)
  have hH : H∈completed g K := mem_completed g (cut β K f) (cut_measurable β K f hf)
    (cut_memLp g K f hm) (cut_physical β K f hi) K
      (ae_of_all _ (cut_support β K f))
  have hL : F-H∈(completed g K).toSubmoduleᗮ := by
    apply low_support_orthogonal
    filter_upwards [Lp.coeFn_sub F H,MemLp.coeFn_toLp hm,MemLp.coeFn_toLp (cut_memLp g K f hm)] with U hSub hF hHigh
    intro hU
    rw [hSub]
    change F U-H U=0
    rw [hF,hHigh]
    have hh : U∈{U : State | K<β*spatialAction U} := hU
    simp only [cut,Set.indicator_of_mem hh,sub_self]
  exact (completed g K).toSubmodule.eq_starProjection_of_mem_orthogonal hH hL

/-- Gauge invariance is an actual smoothing property of the constructed transfer,
not an extra physicality assumption on the incoming observable. -/
theorem transfer_physical {β : ℝ} (g : GroundData β) (f : State → ℝ) :
    ∀ a U,transfer g f (PeriodicSlabGauge.gaugeAction a U)=transfer g f U := by
  intro a U
  simp only [transfer,g.transition_integral,PeriodicSlabGauge.kernel_left_invariant,g.invariant]

/-- Exact native projection of the actual Markov transfer on bounded measurable
inputs. This is a killed-kernel identity, not an identification of P^n and C^n. -/
theorem projected_transfer_toLp {β : ℝ} (g : GroundData β) (K : ℝ) (f : State → ℝ)
    (hf : Measurable f) (hm : MemLp f 2 g.stationary) (B : ℝ) (hB : ∀ U,|f U| ≤ B) :
    (completed g K).toSubmodule.starProjection (operator g (hm.toLp f))=
      (cut_memLp g K (transfer g f) (transfer_memLp g f hf B hB)).toLp
        (cut β K (transfer g f)) := by
  rw [operator_toLp g f hm hf B hB]
  exact projection_toLp g K (transfer g f) (transfer_measurable g f hf)
    (transfer_memLp g f hf B hB) (transfer_physical g f)

/-- On an actual physical high-supported core vector, the original compression
is exactly high-cutoff times the genuine transition integral. -/
theorem compression_toLp {β : ℝ} (g : GroundData β) (K : ℝ) (f : State → ℝ)
    (hf : Measurable f) (hm : MemLp f 2 g.stationary) (B : ℝ) (hB : ∀ U,|f U| ≤ B)
    (hi : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (hs : ∀ᵐ U ∂g.stationary,β*spatialAction U ≤ K → f U=0) :
    let F : completed g K := ⟨hm.toLp f,mem_completed g f hf hm hi K hs⟩
    ((compression g K F : completed g K) : StateL2 g)=
      (cut_memLp g K (transfer g f) (transfer_memLp g f hf B hB)).toLp
        (cut β K (transfer g f)) := by
  change (completed g K).toSubmodule.starProjection (operator g (hm.toLp f))=_
  exact projected_transfer_toLp g K f hf hm B hB

/-- Genuine nonnegative output on the physical high core, verified against the
actual transition measure and native AE representatives. -/
theorem compression_nonnegative {β : ℝ} (g : GroundData β) (K : ℝ) (f : State → ℝ)
    (hf : Measurable f) (hm : MemLp f 2 g.stationary) (B : ℝ) (hB : ∀ U,|f U| ≤ B)
    (hi : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (hs : ∀ᵐ U ∂g.stationary,β*spatialAction U ≤ K → f U=0) (hpos : ∀ U,0 ≤ f U) :
    let F : completed g K := ⟨hm.toLp f,mem_completed g f hf hm hi K hs⟩
    ∀ᵐ U ∂g.stationary,0 ≤ ((compression g K F : completed g K) : StateL2 g) U := by
  dsimp only
  rw [compression_toLp g K f hf hm B hB hi hs]
  filter_upwards [MemLp.coeFn_toLp (cut_memLp g K (transfer g f) (transfer_memLp g f hf B hB))] with U hU
  rw [hU]
  apply Set.indicator_nonneg
  intro V hV
  exact integral_nonneg hpos

/-- The physical action cutoff preserves any specified center-seam even sector. -/
theorem cut_even (β K : ℝ) (f : State → ℝ) (j : Fin 3)
    (he : ∀ U,f (PeriodicCenterSeam.flip j U)=f U) :
    ∀ U,cut β K f (PeriodicCenterSeam.flip j U)=cut β K f U := by
  intro U
  simp only [cut,Set.indicator_apply,Set.mem_ofPred_eq,PeriodicCenterSeam.spatial_action,he]

/-- The actual killed transfer preserves center-seam parity on the explicit core. -/
theorem killed_even {β : ℝ} (g : GroundData β) (K : ℝ) (f : State → ℝ) (j : Fin 3)
    (he : ∀ U,f (PeriodicCenterSeam.flip j U)=f U) :
    ∀ U,cut β K (transfer g f) (PeriodicCenterSeam.flip j U)=cut β K (transfer g f) U := by
  apply cut_even
  intro U
  rw [PeriodicPlaquetteSeamSelection.transfer_flip]
  congr 1
  funext V
  exact he V

end OperatorDerivativeRewrite.Foundation.PeriodicHighActionKernel
