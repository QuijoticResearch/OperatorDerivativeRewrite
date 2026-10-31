import Foundation.PeriodicPhysicalDirichlet
import Foundation.PeriodicGaugeSaturatedGround
import Foundation.PeriodicLocalEnergyObstruction
/-! Actual high-action physical-core control of the stationary Wilson operator.
Normalized product-Haar kinetic pairing and existing principal-value bounds
retain the constructed ground. Supported-core coercivity is not a global gap
or an extension to the completed supported L2 space. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicHighActionControl
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicPhysicalKineticReduction CubeHaarUpper
attribute [local irreducible] temporalAction spatialAction boundaryHaar kernel

private theorem kinetic_measurable (β : ℝ) : Measurable (fun p : State × State => kineticDensity β p.1 p.2) := by
  unfold kineticDensity
  exact (((temporal_action_joint_measurable.comp (measurable_id.prodMk measurable_const)).const_mul (-β)).exp).div_const _

private theorem kinetic_bounds (β : ℝ) (hb : 0 ≤ β) (U V : State) :
    0 ≤ kineticDensity β U V ∧ kineticDensity β U V ≤ 1/(laplace β^192) := by
  constructor
  · exact (div_pos (Real.exp_pos _) (pow_pos (laplace_pos β hb) _)).le
  · unfold kineticDensity
    apply div_le_div_of_nonneg_right _ (pow_pos (laplace_pos β hb) _).le
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (temporal_action_bounds U V 1).1)

private theorem kinetic_symm (β : ℝ) (U V : State) : kineticDensity β U V=kineticDensity β V U := by
  have ht : temporalAction U V 1=temporalAction V U 1 := by
    unfold temporalAction
    apply Finset.sum_congr rfl
    intro e _
    have he := temporal_swap U V (1 : Gauge) e
    simpa only [inv_one] using congrArg (fun x : ℝ => 1-x) he.symm
  unfold kineticDensity
  rw [ht]

private theorem kinetic_joint (β : ℝ) (hb : 0 ≤ β) (f h : State → ℝ)
    (hf : Measurable f) (hh : Measurable h) (B D : ℝ)
    (hB : ∀ U,|f U| ≤ B) (hD : ∀ U,|h U| ≤ D) :
    Integrable (fun p : State × State => kineticDensity β p.1 p.2*(f p.1*h p.2)) (boundaryHaar.prod boundaryHaar) := by
  apply Integrable.of_bound ((kinetic_measurable β).mul
    ((hf.comp measurable_fst).mul (hh.comp measurable_snd))).aestronglyMeasurable ((1/(laplace β^192))*(|B| *|D|))
  filter_upwards with p
  change ‖kineticDensity β p.1 p.2*(f p.1*h p.2)‖ ≤ (1/(laplace β^192))*(|B| *|D|)
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (kinetic_bounds β hb _ _).1]
  exact mul_le_mul (kinetic_bounds β hb _ _).2
    (mul_le_mul ((hB _).trans (le_abs_self _)) ((hD _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)

private theorem kinetic_quadratic (β : ℝ) (hb : 0 ≤ β) (f : State → ℝ)
    (hf : Measurable f) (B : ℝ) (hB : ∀ U,|f U| ≤ B) :
    |∫ U,∫ V,kineticDensity β U V*(f U*f V) ∂boundaryHaar ∂boundaryHaar| ≤
      ∫ U,f U^2 ∂boundaryHaar := by
  have hs (U : State) : |f U^2| ≤ |B|^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((hB U).trans (le_abs_self _)) 2
  have hi := kinetic_joint β hb f f hf hf B B hB hB
  have hleft := kinetic_joint β hb (fun U => f U^2) (fun _ => 1) (hf.pow_const 2) measurable_const
    (|B|^2) 1 hs (fun _ => by norm_num)
  have hright := kinetic_joint β hb (fun _ => 1) (fun U => f U^2) measurable_const (hf.pow_const 2)
    1 (|B|^2) (fun _ => by norm_num) hs
  have hj := (hleft.add hright).div_const 2
  have hbound := norm_integral_le_of_norm_le (f := fun p : State × State => kineticDensity β p.1 p.2*(f p.1*f p.2)) hj (ae_of_all _ (fun p : State × State => by
    change ‖kineticDensity β p.1 p.2*(f p.1*f p.2)‖ ≤
      (kineticDensity β p.1 p.2*(f p.1^2*1)+kineticDensity β p.1 p.2*(1*f p.2^2))/2
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (kinetic_bounds β hb _ _).1,abs_mul]
    have ha : |f p.1| *|f p.2| ≤ (f p.1^2+f p.2^2)/2 := by
      nlinarith [sq_nonneg (|f p.1|-|f p.2|),sq_abs (f p.1),sq_abs (f p.2)]
    have hm := mul_le_mul_of_nonneg_left ha (kinetic_bounds β hb p.1 p.2).1
    nlinarith only [hm]))
  have hA : (∫ p : State × State,kineticDensity β p.1 p.2*(f p.1^2*1) ∂boundaryHaar.prod boundaryHaar)=
      ∫ U,f U^2 ∂boundaryHaar := by
    rw [integral_prod _ hleft]
    simp only [mul_one]
    simp_rw [mul_comm (kineticDensity β _ _) (_^2),integral_const_mul,kinetic_mass β hb,mul_one]
  have hB' : (∫ p : State × State,kineticDensity β p.1 p.2*(1*f p.2^2) ∂boundaryHaar.prod boundaryHaar)=
      ∫ U,f U^2 ∂boundaryHaar := by
    rw [integral_prod_symm _ hright]
    simp only [one_mul]
    simp_rw [kinetic_symm β,mul_comm (kineticDensity β _ _) (_^2),integral_const_mul,kinetic_mass β hb,mul_one]
  simp only [Pi.add_apply] at hbound
  rw [integral_div,integral_add hleft hright,hA,hB'] at hbound
  rw [integral_prod _ hi,Real.norm_eq_abs] at hbound
  nlinarith only [hbound]

theorem native_kinetic_pairing {β : ℝ} (hb : 0 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (B : ℝ) (hB : ∀ U,|f U| ≤ B) (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    inner ℝ (operator g (hmem.toLp f)) (hmem.toLp f)=
      (laplace β^192/(g.value*g.normalizer))*
        (∫ U,∫ V,kineticDensity β U V*((PeriodicLocalGroundHarnack.dressed g U*f U)*
          (PeriodicLocalGroundHarnack.dressed g V*f V)) ∂boundaryHaar ∂boundaryHaar) := by
  have hq : inner ℝ (operator g (hmem.toLp f)) (hmem.toLp f)=
      ∫ U,f U*(∫ V,f V ∂g.transition U) ∂g.stationary := by
    rw [operator_toLp g f hmem hf B hB,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (transfer_memLp g f hf B hB),MemLp.coeFn_toLp hmem] with U hP hF
    rw [hP,hF]
    rfl
  rw [hq,g.stationary_pairing]
  have hI : pairing β (fun U => g.function U*f U) (fun U => g.function U*f U)=
      laplace β^192*(∫ U,∫ V,kineticDensity β U V*((PeriodicLocalGroundHarnack.dressed g U*f U)*
        (PeriodicLocalGroundHarnack.dressed g V*f V)) ∂boundaryHaar ∂boundaryHaar) := by
    unfold pairing
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with U
    rw [invariant_factorization β hb U (fun V => g.function V*f V) (g.measurable.mul hf) (native_weighted_integrable g f hf hmem)
      (fun a V => by rw [g.invariant,hInv])]
    unfold kinetic
    simp_rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with V
    unfold PeriodicLocalGroundHarnack.dressed
    ring
  rw [hI]
  ring

private theorem dressed_probe {β : ℝ} (hb : 0 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ U,|f U| ≤ B) :
    Measurable (fun U => PeriodicLocalGroundHarnack.dressed g U*f U) ∧
      (∀ U,|PeriodicLocalGroundHarnack.dressed g U*f U| ≤ |g.upper| *|B|) := by
  have hM : Measurable (multiplier β) := (((spatial_action_measurable.const_mul (-β)).div_const 2).exp)
  refine ⟨(hM.mul g.measurable).mul hf,?_⟩
  intro U
  have hM1 : multiplier β U ≤ 1 := by
    unfold multiplier
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (spatial_action_bounds U).1) (by norm_num))
  have hd : |PeriodicLocalGroundHarnack.dressed g U| ≤ |g.upper| := by
    unfold PeriodicLocalGroundHarnack.dressed
    rw [abs_mul,abs_of_pos (show 0 < multiplier β U by unfold multiplier; exact Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right hM1 (abs_nonneg _)).trans (by simpa using (g.bounds U).2.trans (le_abs_self _))
  rw [abs_mul]
  exact mul_le_mul hd ((hB U).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

private theorem native_high_action_raw {β : ℝ} (hb : 0 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (B : ℝ) (hB : ∀ U,|f U| ≤ B) (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (K : ℝ) (hsupport : ∀ U,β*spatialAction U ≤ K → f U=0) :
    |inner ℝ (operator g (hmem.toLp f)) (hmem.toLp f)| ≤
      (laplace β^192/g.value)*Real.exp (-K)*‖hmem.toLp f‖^2 := by
  let H : State → ℝ := fun U => PeriodicLocalGroundHarnack.dressed g U*f U
  have hd := dressed_probe hb g f hf B hB
  have hi : Integrable (fun U => H U^2) boundaryHaar := by
    apply Integrable.of_bound (hd.1.pow_const 2).aestronglyMeasurable ((|g.upper| *|B|)^2)
    filter_upwards with U
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (H U)) (hd.2 U) 2
  have hw := (PeriodicBoundaryHaarReduction.stationary_integrable_iff g (fun U => f U^2)).mp hmem.integrable_sq
  have hpoint (U : State) : H U^2 ≤ Real.exp (-K)*(g.function U^2*f U^2) := by
    by_cases hx : f U=0
    · simp [H,hx]
    · have hs : K < β*spatialAction U := lt_of_not_ge (fun h => hx (hsupport U h))
      have he : (multiplier β U)^2=Real.exp (-β*spatialAction U) := by
        unfold multiplier
        rw [pow_two,← Real.exp_add]
        congr 1
        ring
      have hp := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hs.le))
        (mul_nonneg (sq_nonneg (g.function U)) (sq_nonneg (f U)))
      simp only [neg_mul] at he
      rw [← he] at hp
      dsimp [H,PeriodicLocalGroundHarnack.dressed]
      nlinarith only [hp]
  have hm := integral_mono hi (hw.const_mul (Real.exp (-K))) hpoint
  rw [integral_const_mul] at hm
  have hn := g.stationary_integral (fun U => f U^2)
  rw [← PeriodicTransferVariation.state_norm_square g f hmem] at hn
  have hn' := (eq_div_iff g.normalizer_pos.ne').mp hn
  have hk := (kinetic_quadratic β hb H hd.1 (|g.upper| *|B|) hd.2).trans hm
  have hz : 0 < laplace β^192 := pow_pos (laplace_pos β hb) _
  have hs := mul_le_mul_of_nonneg_left hk (div_pos hz (mul_pos g.value_pos g.normalizer_pos)).le
  rw [native_kinetic_pairing hb g f hf hmem B hB hInv,abs_mul,
    abs_of_pos (div_pos hz (mul_pos g.value_pos g.normalizer_pos))]
  change (laplace β^192/(g.value*g.normalizer))*|∫ U,∫ V,kineticDensity β U V*(H U*H V)
    ∂boundaryHaar ∂boundaryHaar| ≤ _
  rw [← hn'] at hs
  convert hs using 1; field_simp [g.value_pos.ne',g.normalizer_pos.ne']


private theorem relative_normalization {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    laplace β^192/g.value ≤ PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant := by
  have hp : 0 < β := by linarith
  let t : ℝ := 1/Real.sqrt β
  have ht : 0 < t := div_pos zero_lt_one (Real.sqrt_pos.mpr hp)
  have h1 : t ≤ 1 := (div_le_one (Real.sqrt_pos.mpr hp)).mpr
    (by simpa using Real.sqrt_le_sqrt (show (1:ℝ) ≤ β by linarith))
  have ht2 : t^2=1/β := by dsimp [t]; rw [div_pow,one_pow,Real.sq_sqrt hp.le]
  have he : 1/t^2=β := by rw [ht2]; field_simp
  have hu := SU2HaarLaplaceUpper.laplace_scaled_upper 1 t (by norm_num) ht h1
  rw [he] at hu
  have hpow := pow_le_pow_left₀ (laplace_pos β hp.le).le hu 192
  rw [mul_pow] at hpow
  have ht576 : (t^3)^192=1/β^288 := by
    calc
      _ = (t^2)^288 := by ring
      _ = _ := by rw [ht2,div_pow,one_pow]
  rw [ht576] at hpow
  have hz : laplace β^192 ≤ PeriodicGroundHaarScale.upperConstant/β^288 := by
    simpa only [PeriodicGroundHaarScale.upperConstant,mul_one_div] using hpow
  have hl := PeriodicGaugeSaturatedGround.eigenvalue_matching_lower β hb g
  have hR : 0 < PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant :=
    div_pos PeriodicGroundHaarScale.upperConstant_pos PeriodicGaugeSaturatedGround.eigenLowerConstant_pos
  have hm := mul_le_mul_of_nonneg_left hl hR.le
  have hr : (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
      (PeriodicGaugeSaturatedGround.eigenLowerConstant/β^288)=PeriodicGroundHaarScale.upperConstant/β^288 := by
    field_simp [PeriodicGaugeSaturatedGround.eigenLowerConstant_pos.ne']
  rw [hr] at hm
  exact (div_le_iff₀ g.value_pos).mpr (hz.trans hm)

/-- Actual native quadratic-form control on the bounded physical high-action core. -/
theorem native_high_action_bound {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (B : ℝ) (hB : ∀ U,|f U| ≤ B) (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (K : ℝ) (hsupport : ∀ U,β*spatialAction U ≤ K → f U=0) :
    |inner ℝ (operator g (hmem.toLp f)) (hmem.toLp f)| ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-K)*‖hmem.toLp f‖^2 := by
  have hh := native_high_action_raw (show 0 ≤ β by linarith) g f hf hmem B hB hInv K hsupport
  have hs := mul_le_mul_of_nonneg_right (relative_normalization hb g)
    (mul_nonneg (Real.exp_pos (-K)).le (sq_nonneg ‖hmem.toLp f‖))
  exact hh.trans (by simpa only [mul_assoc] using hs)

theorem native_high_action_coercivity {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (B : ℝ) (hB : ∀ U,|f U| ≤ B) (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (K : ℝ) (hsupport : ∀ U,β*spatialAction U ≤ K → f U=0) :
    (1-(PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-K))*
      ‖hmem.toLp f‖^2 ≤ SelfAdjointContractionIteration.dissipation (operator g) (hmem.toLp f) := by
  have hh := (le_abs_self (inner ℝ (operator g (hmem.toLp f)) (hmem.toLp f))).trans
    (native_high_action_bound hb g f hf hmem B hB hInv K hsupport)
  unfold SelfAdjointContractionIteration.dissipation
  rw [real_inner_self_eq_norm_sq]
  nlinarith only [hh]

/-- A fixed action threshold gives one-half native coercivity, uniformly in coupling.
This is a supported-core theorem, not a global spectral-gap or closure assertion. -/
theorem native_high_action_half {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (B : ℝ) (hB : ∀ U,|f U| ≤ B) (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (hsupport : ∀ U,β*spatialAction U ≤
      Real.log (2*(PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)) → f U=0) :
    (1/2 : ℝ)*‖hmem.toLp f‖^2 ≤ SelfAdjointContractionIteration.dissipation (operator g) (hmem.toLp f) := by
  let R : ℝ := PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant
  have hR : 0 < R := div_pos PeriodicGroundHaarScale.upperConstant_pos PeriodicGaugeSaturatedGround.eigenLowerConstant_pos
  have he : R*Real.exp (-Real.log (2*R))=(1/2 : ℝ) := by
    rw [Real.exp_neg,Real.exp_log (mul_pos (by norm_num) hR)]
    field_simp [hR.ne']
  have hh := native_high_action_coercivity hb g f hf hmem B hB hInv (Real.log (2*R)) hsupport
  change (1-R*Real.exp (-Real.log (2*R)))*‖hmem.toLp f‖^2 ≤ _ at hh
  rw [he] at hh
  norm_num at hh ⊢
  exact hh

/-- The earlier cutoff counterexample retains one-half full native coercivity
when its support lies above the fixed high-action threshold. -/
theorem cutoff_full_coercivity {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β)
    (K : ℝ) (hK : 0 ≤ K)
    (hthreshold : Real.log (2*(PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant))
      ≤ 2*K+27648) :
    (1/2 : ℝ)*‖(PeriodicLocalEnergyObstruction.cutoff_memLp g K (by linarith) hK).toLp
      (PeriodicLocalEnergyObstruction.cutoff β K)‖^2 ≤
    SelfAdjointContractionIteration.dissipation (operator g)
      ((PeriodicLocalEnergyObstruction.cutoff_memLp g K (by linarith) hK).toLp
        (PeriodicLocalEnergyObstruction.cutoff β K)) := by
  apply native_high_action_half hb g _ (PeriodicLocalEnergyObstruction.cutoff_continuous β K).measurable
    (PeriodicLocalEnergyObstruction.cutoff_memLp g K (by linarith) hK) (384*β)
  · intro U
    rw [abs_of_nonneg (PeriodicLocalEnergyObstruction.cutoff_bounds β K (by linarith) hK U).1]
    exact (PeriodicLocalEnergyObstruction.cutoff_bounds β K (by linarith) hK U).2
  · exact PeriodicLocalEnergyObstruction.cutoff_gauge β K
  · intro U hU
    unfold PeriodicLocalEnergyObstruction.cutoff
    exact max_eq_left (by linarith)


/-- The actual cutoff localization obstruction cannot serve as a slow trial:
its full native dissipation controls its actual stationary variance. -/
theorem cutoff_variance_coercivity {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β)
    (K : ℝ) (hK : 0 ≤ K)
    (hthreshold : Real.log (2*(PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant))
      ≤ 2*K+27648) :
    (1/2 : ℝ)*variance (PeriodicLocalEnergyObstruction.cutoff β K) g.stationary ≤
    SelfAdjointContractionIteration.dissipation (operator g)
      ((PeriodicLocalEnergyObstruction.cutoff_memLp g K (by linarith) hK).toLp
        (PeriodicLocalEnergyObstruction.cutoff β K)) := by
  have hm := PeriodicLocalEnergyObstruction.cutoff_memLp g K (show 0 ≤ β by linarith) hK
  have hv := variance_eq_sub hm
  simp only [Pi.pow_apply] at hv
  rw [← PeriodicTransferVariation.state_norm_square g _ hm] at hv
  have he := cutoff_full_coercivity hb g K hK hthreshold
  nlinarith only [hv,he,sq_nonneg (∫ U,PeriodicLocalEnergyObstruction.cutoff β K U ∂g.stationary)]

end OperatorDerivativeRewrite.Foundation.PeriodicHighActionControl
