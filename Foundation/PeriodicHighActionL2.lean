import Foundation.PeriodicHighActionControl
import Foundation.BochnerL2Dominated
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
/-! Native L2 high-action control, its explicitly defined closed physical
completion, and the actual compressed resolvent. Hard truncation proves the
unbounded representative result with AE support. The Neumann inverse acts
only on this completed high block; no global mass gap is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicHighActionL2
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicHighActionControl
attribute [local irreducible] spatialAction

private def truncate (n : ℕ) (f : State → ℝ) : State → ℝ :=
  {U | |f U| ≤ (n:ℝ)}.indicator f

private theorem trunc_measurable (n : ℕ) (f : State → ℝ) (hf : Measurable f) :
    Measurable (truncate n f) := hf.indicator (measurableSet_le (measurable_norm.comp hf) measurable_const)
private theorem trunc_memLp {β : ℝ} (g : GroundData β) (n : ℕ) (f : State → ℝ)
    (hf : Measurable f) (hm : MemLp f 2 g.stationary) : MemLp (truncate n f) 2 g.stationary :=
  hm.indicator (measurableSet_le (measurable_norm.comp hf) measurable_const)
private theorem trunc_bound (n : ℕ) (f : State → ℝ) (U : State) : |truncate n f U| ≤ (n:ℝ) := by
  by_cases hU : |f U| ≤ (n:ℝ)
  · have hh : U∈{V : State | |f V| ≤ (n:ℝ)} := hU
    simpa only [truncate,Set.indicator_of_mem hh] using hU
  · have hh : U∉{V : State | |f V| ≤ (n:ℝ)} := hU
    simp only [truncate,Set.indicator_of_notMem hh,abs_zero]
    positivity
private theorem trunc_invariant (n : ℕ) (f : State → ℝ)
    (hi : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    ∀ a U,truncate n f (PeriodicSlabGauge.gaugeAction a U)=truncate n f U := by
  intro a U
  simp only [truncate,Set.indicator_apply,Set.mem_ofPred_eq,hi]
private theorem trunc_support (n : ℕ) (f : State → ℝ) (β K : ℝ)
    (hs : ∀ U,β*spatialAction U ≤ K → f U=0) :
    ∀ U,β*spatialAction U ≤ K → truncate n f U=0 := by
  intro U hU
  simp [truncate,hs U hU]

private theorem trunc_pointwise (f : State → ℝ) (U : State) :
    Tendsto (fun n => truncate n f U) atTop (𝓝 (f U)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt |f U|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hU : |f U| ≤ (n:ℝ) := hN.le.trans (by exact_mod_cast hn)
  have hh : U∈{V : State | |f V| ≤ (n:ℝ)} := hU
  simp only [truncate,Set.indicator_of_mem hh]

/-- Native L2 convergence, including the countable representative identities. -/
private theorem trunc_tendsto {β : ℝ} (g : GroundData β) (f : State → ℝ)
    (hf : Measurable f) (hm : MemLp f 2 g.stationary) :
    Tendsto (fun n => (trunc_memLp g n f hf hm).toLp (truncate n f)) atTop (𝓝 (hm.toLp f)) := by
  let F (n : ℕ) : StateL2 g := (trunc_memLp g n f hf hm).toLp (truncate n f)
  have he (n : ℕ) : (fun U => F n U)=ᵐ[g.stationary] truncate n f := MemLp.coeFn_toLp _
  have hAll : ∀ᵐ U ∂g.stationary,∀ n,F n U=truncate n f U := ae_all_iff.mpr he
  change Tendsto F atTop (𝓝 (hm.toLp f))
  apply BochnerL2Dominated.tendsto_of_ae_norm_bound F (hm.toLp f)
  · intro n
    filter_upwards [he n,MemLp.coeFn_toLp hm] with U hn hU
    rw [hn,hU]
    exact norm_indicator_le_norm_self f U
  · filter_upwards [hAll,MemLp.coeFn_toLp hm] with U hU hF
    change Tendsto (fun n => F n U) atTop (𝓝 ((hm.toLp f) U))
    simp_rw [hU,hF]
    exact trunc_pointwise f U

private theorem pointwise_high_action {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (K : ℝ) (hs : ∀ U,β*spatialAction U ≤ K → f U=0) :
    |inner ℝ (operator g (hm.toLp f)) (hm.toLp f)| ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-K)*‖hm.toLp f‖^2 := by
  let F (n : ℕ) : StateL2 g := (trunc_memLp g n f hf hm).toLp (truncate n f)
  have hT : Tendsto F atTop (𝓝 (hm.toLp f)) := trunc_tendsto g f hf hm
  have hP := (((operator g).continuous.tendsto (hm.toLp f)).comp hT).inner (𝕜 := ℝ) hT
  have hN := (hT.norm.pow 2).const_mul
    ((PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-K))
  apply le_of_tendsto_of_tendsto' hP.abs hN
  intro n
  exact native_high_action_bound hb g (truncate n f) (trunc_measurable n f hf)
    (trunc_memLp g n f hf hm) n (trunc_bound n f) (trunc_invariant n f hInv) K
    (trunc_support n f β K hs)

/-- Unbounded native L2 representatives with pointwise physicality and actual
almost-everywhere high-action support. No boundedness assumption remains. -/
theorem native_high_action_L2 {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (K : ℝ) (hs : ∀ᵐ U ∂g.stationary,β*spatialAction U ≤ K → f U=0) :
    |inner ℝ (operator g (hm.toLp f)) (hm.toLp f)| ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-K)*‖hm.toLp f‖^2 := by
  let A : Set State := {U | K < β*spatialAction U}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (spatial_action_measurable.const_mul β)
  let h := A.indicator f
  have hmeas : Measurable h := hf.indicator hA
  have hmem : MemLp h 2 g.stationary := hm.indicator hA
  have he : h=ᵐ[g.stationary] f := by
    filter_upwards [hs] with U hU
    by_cases ha : U∈A
    · exact Set.indicator_of_mem ha f
    · have hh : β*spatialAction U ≤ K := le_of_not_gt ha
      simp only [h,Set.indicator_of_notMem ha,hU hh]
  have hi : ∀ a U,h (PeriodicSlabGauge.gaugeAction a U)=h U := by
    intro a U
    simp only [h,A,Set.indicator_apply,Set.mem_ofPred_eq,PeriodicSlabGauge.spatial_action_invariant,hInv]
  have hsup : ∀ U,β*spatialAction U ≤ K → h U=0 := by
    intro U hU
    have hh : U∉A := not_lt.mpr hU
    exact Set.indicator_of_notMem hh f
  have hclass : hmem.toLp h=hm.toLp f := (MemLp.toLp_eq_toLp_iff hmem hm).mpr he
  rw [← hclass]
  exact pointwise_high_action hb g h hmeas hmem hi K hsup

theorem native_high_action_L2_coercivity {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (K : ℝ) (hs : ∀ᵐ U ∂g.stationary,β*spatialAction U ≤ K → f U=0) :
    (1-(PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-K))*
      ‖hm.toLp f‖^2 ≤ SelfAdjointContractionIteration.dissipation (operator g) (hm.toLp f) := by
  have hh := (le_abs_self (inner ℝ (operator g (hm.toLp f)) (hm.toLp f))).trans
    (native_high_action_L2 hb g f hf hm hInv K hs)
  unfold SelfAdjointContractionIteration.dissipation
  rw [real_inner_self_eq_norm_sq]
  nlinarith only [hh]

/-- Actual native classes admitting a measurable pointwise physical representative
with almost-everywhere high-action support. No boundedness is imposed. -/
def represented {β : ℝ} (g : GroundData β) (K : ℝ) : Submodule ℝ (StateL2 g) where
  carrier := {F | ∃ f : State → ℝ,Measurable f ∧ ∃ hm : MemLp f 2 g.stationary,
    (∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) ∧
    (∀ᵐ U ∂g.stationary,β*spatialAction U ≤ K → f U=0) ∧ hm.toLp f=F}
  zero_mem' := by
    refine ⟨fun _ => 0,measurable_const,MemLp.zero',fun _ _ => rfl,ae_of_all _ (fun _ _ => rfl),?_⟩
    rfl
  add_mem' := by
    rintro F G ⟨f,hf,hm,hi,hs,hF⟩ ⟨h,hh,hn,hj,ht,hG⟩
    refine ⟨f+h,hf.add hh,hm.add hn,?_,?_,?_⟩
    · intro a U
      simp only [Pi.add_apply,hi,hj]
    · filter_upwards [hs,ht] with U hU hV
      intro hx
      simp only [Pi.add_apply,hU hx,hV hx,zero_add]
    · rw [MemLp.toLp_add hm hn,hF,hG]
  smul_mem' := by
    rintro c F ⟨f,hf,hm,hi,hs,hF⟩
    refine ⟨c • f,hf.const_smul c,hm.const_smul c,?_,?_,?_⟩
    · intro a U
      simp only [Pi.smul_apply,hi]
    · filter_upwards [hs] with U hU
      intro hx
      simp only [Pi.smul_apply,hU hx,smul_zero]
    · rw [MemLp.toLp_const_smul c hm,hF]

/-- The closed native completion of the explicitly represented physical high sector.
No identification with another gauge-quotient realization is assumed. -/
def completed {β : ℝ} (g : GroundData β) (K : ℝ) : ClosedSubmodule ℝ (StateL2 g) where
  toSubmodule := (represented g K).topologicalClosure
  isClosed' := (represented g K).isClosed_topologicalClosure

theorem completed_bound {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) (K : ℝ)
    (F : StateL2 g) (hF : F∈completed g K) :
    |inner ℝ (operator g F) F| ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-K)*‖F‖^2 := by
  have hc : IsClosed {F : StateL2 g | |inner ℝ (operator g F) F| ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-K)*‖F‖^2} :=
    isClosed_le (((operator g).continuous.inner (𝕜 := ℝ) continuous_id).abs)
      (continuous_const.mul (continuous_norm.pow 2))
  apply closure_minimal (t := {F : StateL2 g | |inner ℝ (operator g F) F| ≤
    (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-K)*‖F‖^2})
    (s := (represented g K : Set (StateL2 g))) ?_ hc hF
  rintro G ⟨f,hf,hm,hi,hs,hG⟩
  rw [← hG]
  exact native_high_action_L2 hb g f hf hm hi K hs

/-- Orthogonal compression of the ORIGINAL native stationary operator. -/
def compression {β : ℝ} (g : GroundData β) (K : ℝ) : completed g K →L[ℝ] completed g K :=
  (completed g K).toSubmodule.orthogonalProjectionOnto.comp
    ((operator g).comp (completed g K).toSubmodule.subtypeL)

theorem compression_pairing {β : ℝ} (g : GroundData β) (K : ℝ) (F G : completed g K) :
    inner ℝ (compression g K F) G=inner ℝ (operator g (F : StateL2 g)) (G : StateL2 g) := by
  change inner ℝ ((completed g K).toSubmodule.orthogonalProjectionOnto (operator g (F : StateL2 g))) G=_
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right G _

theorem compression_symmetric {β : ℝ} (g : GroundData β) (K : ℝ) :
    (compression g K).IsSymmetric := by
  intro F G
  change inner ℝ (compression g K F) G=inner ℝ F (compression g K G)
  calc
    _ = inner ℝ (operator g (F : StateL2 g)) (G : StateL2 g) := compression_pairing g K F G
    _ = inner ℝ (F : StateL2 g) (operator g (G : StateL2 g)) := operator_symmetric g F G
    _ = inner ℝ (operator g (G : StateL2 g)) (F : StateL2 g) := real_inner_comm _ _
    _ = inner ℝ (compression g K G) F := (compression_pairing g K G F).symm
    _ = _ := real_inner_comm _ _

theorem compression_norm {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) (K : ℝ) :
    ‖compression g K‖ ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-K) := by
  rw [(compression g K).norm_eq_iSup_rayleighQuotient (compression_symmetric g K)]
  apply ciSup_le
  intro F
  by_cases hF : F=0
  · simp only [hF,ContinuousLinearMap.rayleighQuotient_apply_zero,abs_zero]
    exact (mul_pos (div_pos PeriodicGroundHaarScale.upperConstant_pos
      PeriodicGaugeSaturatedGround.eigenLowerConstant_pos) (Real.exp_pos _)).le
  · have hn : 0 < ‖F‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hF)
    change |inner ℝ (compression g K F) F/‖F‖^2| ≤ _
    rw [abs_div,abs_of_nonneg (sq_nonneg ‖F‖)]
    apply (div_le_iff₀ hn).mpr
    rw [compression_pairing]
    exact completed_bound hb g K F F.property

theorem compression_half {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    ‖compression g (Real.log (2*(PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)))‖ ≤
      (1/2 : ℝ) := by
  let R : ℝ := PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant
  have hR : 0 < R := div_pos PeriodicGroundHaarScale.upperConstant_pos PeriodicGaugeSaturatedGround.eigenLowerConstant_pos
  have he : R*Real.exp (-Real.log (2*R))=(1/2 : ℝ) := by
    rw [Real.exp_neg,Real.exp_log (mul_pos (by norm_num) hR)]
    field_simp [hR.ne']
  exact (compression_norm hb g (Real.log (2*R))).trans_eq he


theorem mem_completed {β : ℝ} (g : GroundData β) (f : State → ℝ) (hf : Measurable f)
    (hm : MemLp f 2 g.stationary) (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (K : ℝ) (hs : ∀ᵐ U ∂g.stationary,β*spatialAction U ≤ K → f U=0) :
    hm.toLp f∈completed g K :=
  (represented g K).le_topologicalClosure ⟨f,hf,hm,hInv,hs,rfl⟩

attribute [local irreducible] represented completed compression

/-- A unique bounded two-sided inverse of the actual completed high block.
The witness is the convergent Neumann series, not an existence axiom. -/
theorem high_resolvent {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    let K : ℝ := Real.log (2*(PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant))
    let C := compression g K
    ∃! R : completed g K →L[ℝ] completed g K,
      (1-C)*R=1 ∧ R*(1-C)=1 ∧ ‖R‖ ≤ 2 := by
  let K : ℝ := Real.log (2*(PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant))
  let C := compression g K
  have hC : ‖C‖ ≤ (1/2 : ℝ) := compression_half hb g
  have hlt : ‖C‖ < 1 := by linarith
  let U := Units.oneSub C hlt
  have hnorm : ‖((↑(U⁻¹)) : completed g K →L[ℝ] completed g K)‖ ≤ 2 := by
    change ‖∑' n : ℕ,C^n‖ ≤ 2
    have hh := tsum_geometric_le_of_norm_lt_one C hlt
    have hI : ‖(1 : completed g K →L[ℝ] completed g K)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hinv : (1-‖C‖)⁻¹ ≤ (2:ℝ) := by
      calc
        _ ≤ 1/(1/2 : ℝ) := by
          simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2)
            (show (1/2:ℝ) ≤ 1-‖C‖ by linarith)
        _ = 2 := by norm_num
    linarith
  have hL : (1-C)*↑(U⁻¹)=1 := U.val_inv
  have hR' : ↑(U⁻¹)*(1-C)=1 := U.inv_val
  refine ⟨↑(U⁻¹),⟨hL,hR',hnorm⟩,?_⟩
  intro R hR
  change (1-C)*R=1 ∧ R*(1-C)=1 ∧ ‖R‖ ≤ 2 at hR
  exact left_inv_eq_right_inv hR.2.1 hL

end OperatorDerivativeRewrite.Foundation.PeriodicHighActionL2
