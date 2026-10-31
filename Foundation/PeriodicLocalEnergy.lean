import Foundation.PeriodicPhysicalDirichlet
import Foundation.PeriodicLowActionStationaryMass
/-! Actual physical Dirichlet domination of normalized local increments on
low-action anchors. Genuine Haar translation and stationary domains retain
the constructed ground and eigenvalue. No global spectral bound is asserted. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalEnergy
open QuaternionSU2Representation FourCubePinnedCoercivity PeriodicTemporalSlab PeriodicWilsonSlab
open PeriodicSlabGround PeriodicSlabL2 PeriodicLocalGroundHarnack PeriodicKineticCapLower
open PeriodicPhysicalKineticReduction PeriodicGroundHaarScale SU2WilsonConvolution
attribute [local irreducible] spatialAction temporalAction weight boundaryHaar

def capIncrement (t : ℝ) (f : State → ℝ) (U : State) : ℝ :=
  ∫ h in capBox t,(f (U*h)-f U)^2 ∂boundaryHaar

def localConstant (K : ℝ) : ℝ :=
  (1/(4*Real.pi^2))^384*Real.exp (-4*K-59904)/(2*upperConstant^2)

theorem localConstant_pos (K : ℝ) : 0 < localConstant K := by
  unfold localConstant
  exact div_pos (mul_pos (pow_pos (by positivity) _) (Real.exp_pos _))
    (mul_pos (by norm_num) (sq_pos_of_pos upperConstant_pos))

private theorem delta_bound (f : State → ℝ) (B : ℝ) (hB : ∀ U,|f U| ≤ B) (U V : State) :
    ‖(f V-f U)^2‖ ≤ 4*|B|^2 := by
  have hd : |f V-f U| ≤ 2*|B| := by
    linarith [abs_sub (f V) (f U),hB U,hB V,le_abs_self B]
  have hp := pow_le_pow_left₀ (abs_nonneg (f V-f U)) hd 2
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (f V-f U)]

private theorem cap_measurable (t : ℝ) (f : State → ℝ) (hf : Measurable f) :
    Measurable (capIncrement t f) := by
  have hm : Measurable (fun p : State × State => (f (p.1*p.2)-f p.1)^2) :=
    ((hf.comp (measurable_fst.mul measurable_snd)).sub (hf.comp measurable_fst)).pow_const 2
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private theorem cap_bound (t : ℝ) (f : State → ℝ) (B : ℝ) (hB : ∀ U,|f U| ≤ B) (U : State) :
    ‖capIncrement t f U‖ ≤ 4*|B|^2 := by
  have h := norm_integral_le_of_norm_le_const (μ := boundaryHaar.restrict (capBox t))
    (ae_of_all _ (fun h => delta_bound f B hB U (U*h)))
  have hm : (boundaryHaar.restrict (capBox t)).real Set.univ ≤ 1 := by
    change (boundaryHaar.restrict (capBox t) Set.univ).toReal ≤ 1
    rw [Measure.restrict_apply_univ]
    exact measureReal_le_one
  exact h.trans (by nlinarith [sq_nonneg |B|])

theorem capIncrement_integrable {β : ℝ} (g : GroundData β) (t : ℝ)
    (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ U,|f U| ≤ B) :
    Integrable (capIncrement t f) g.stationary := by
  let : IsProbabilityMeasure g.stationary := g.stationary_probability
  exact Integrable.of_bound (cap_measurable t f hf).aestronglyMeasurable
    (4*|B|^2) (ae_of_all _ (cap_bound t f B hB))

private theorem temporal_cap (U h : State) (t : ℝ) (hh : h∈capBox t) :
    temporalAction U (U*h) 1 ≤ 576*t^2 := by
  have he : temporalAction U (U*h) 1=∑ e : SpatialEdge,defect (h e) := by
    unfold temporalAction
    apply Finset.sum_congr rfl
    intro e _
    unfold temporalWord
    simp only [Pi.one_apply,Pi.mul_apply,mul_one,inv_one]
    have hw : U e*(U e*h e)⁻¹=U e*(h e)⁻¹*(U e)⁻¹ := by group
    rw [hw,defect,halfTrace_conjugate,halfTrace_inv]
  rw [he]
  have hd (e : SpatialEdge) : defect (h e) ≤ 3*t^2 := hh e (Set.mem_univ e)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hd e)
  rw [Finset.sum_const,Finset.card_univ,edge_count,nsmul_eq_mul] at hs
  norm_num only [Nat.cast_ofNat] at hs
  nlinarith only [hs]

private theorem weight_dressed {β : ℝ} (g : GroundData β) (U V : State) :
    g.function U*weight β U V 1*g.function V=
      Real.exp (-β*temporalAction U V 1)*dressed g U*dressed g V := by
  unfold dressed multiplier weight halfAction
  rw [show -β*(spatialAction U/2+temporalAction U V 1+spatialAction V/2)=
    -β*spatialAction U/2+(-β*temporalAction U V 1)+(-β*spatialAction V/2) by ring,
    Real.exp_add,Real.exp_add]
  ring

private theorem local_weight (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (g : GroundData (1/t^2))
    (K : ℝ) (U h : State) (hK : (1/t^2)*spatialAction U ≤ K) (hh : h∈capBox t) :
    ((1/(4*Real.pi^2))^192*Real.exp (-4*K-59904)/upperConstant)*g.function U^2 ≤
      g.function U*weight (1/t^2) U (U*h) 1*g.function (U*h) := by
  let c : ℝ := (1/(4*Real.pi^2))^192*Real.exp (-(3*K+59328))
  have hc : 0 < c := mul_pos (pow_pos (by positivity) _) (Real.exp_pos _)
  have hw (V : State) : 0 < dressed g V := mul_pos (Real.exp_pos _) (g.function_pos V)
  have hcomp : c*dressed g U ≤ upperConstant*dressed g (U*h) :=
    (uniform_local_comparison t ht h1 g U (U*h) K hK (cap_packet U h t ht.le hh)).1
  have hscale : (1/t^2)*t^2=1 := by field_simp
  have htemp : Real.exp (-576) ≤ Real.exp (-(1/t^2)*temporalAction U (U*h) 1) := by
    apply Real.exp_le_exp.mpr
    have hs := mul_le_mul_of_nonneg_left (temporal_cap U h t hh) (show (0 : ℝ) ≤ 1/t^2 by positivity)
    nlinarith
  have hM : Real.exp (-K) ≤ (multiplier (1/t^2) U)^2 := by
    have he : (multiplier (1/t^2) U)^2=Real.exp (-(1/t^2)*spatialAction U) := by
      unfold multiplier
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    rw [he]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsq : Real.exp (-K)*g.function U^2 ≤ dressed g U^2 := by
    unfold dressed
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hM (sq_nonneg _)
  have ha := mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le (Real.exp_pos (-576)).le)
  have hb := mul_le_mul_of_nonneg_left hcomp (mul_nonneg (Real.exp_pos (-576)).le (hw U).le)
  have hd := mul_le_mul_of_nonneg_left htemp
    (mul_nonneg upperConstant_pos.le (mul_nonneg (hw U).le (hw (U*h)).le))
  have hbase : c*Real.exp (-576)*Real.exp (-K)*g.function U^2 ≤
      upperConstant*(g.function U*weight (1/t^2) U (U*h) 1*g.function (U*h)) := by
    rw [weight_dressed]
    nlinarith only [ha,hb,hd]
  have he : c*Real.exp (-576)*Real.exp (-K)=
      (1/(4*Real.pi^2))^192*Real.exp (-4*K-59904) := by
    dsimp [c]
    simp only [mul_assoc,← Real.exp_add]
    congr 2; ring
  rw [he] at hbase
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ upperConstant_pos).mpr (by nlinarith only [hbase])

private theorem state_left_preserving (U : State) :
    MeasurePreserving (fun h : State => U*h) boundaryHaar boundaryHaar := by
  unfold boundaryHaar
  exact measurePreserving_pi (fun _ => law) (fun _ => law)
    (fun e => measurePreserving_mul_left law (U e))

private theorem row_integrable {β : ℝ} (g : GroundData β) (f : State → ℝ)
    (hf : Measurable f) (B : ℝ) (hB : ∀ U,|f U| ≤ B) (U : State) :
    Integrable (fun V => g.function U*(weight β U V 1*(g.function V*(f V-f U)^2))) boundaryHaar := by
  have hm : Measurable (fun V : State => weight β U V 1) :=
    (weight_joint_measurable β).comp ((measurable_const.prodMk measurable_id).prodMk measurable_const)
  apply Integrable.of_bound (measurable_const.mul (hm.mul (g.measurable.mul
    ((hf.sub measurable_const).pow_const 2)))).aestronglyMeasurable
    (|g.upper| *(Real.exp (768*|β|)*(|g.upper| *(4*|B|^2))))
  filter_upwards with V
  have hg (W : State) : ‖g.function W‖ ≤ |g.upper| := by
    simpa only [Real.norm_eq_abs] using (g.bounds W).2.trans (le_abs_self _)
  have hw : ‖weight β U V 1‖ ≤ Real.exp (768*|β|) := by
    rw [Real.norm_eq_abs,abs_of_pos (by unfold weight; exact Real.exp_pos _)]
    exact (weight_bounds β U V 1).2
  exact norm_mul_le_of_le (hg U) (norm_mul_le_of_le hw (norm_mul_le_of_le (hg V) (delta_bound f B hB U V)))

private theorem row_lower (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (g : GroundData (1/t^2))
    (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ U,|f U| ≤ B)
    (K : ℝ) (U : State) (hK : (1/t^2)*spatialAction U ≤ K) :
    ((1/(4*Real.pi^2))^192*Real.exp (-4*K-59904)/upperConstant)*
      g.function U^2*capIncrement t f U ≤
    ∫ V,g.function U*(weight (1/t^2) U V 1*(g.function V*(f V-f U)^2)) ∂boundaryHaar := by
  let C : ℝ := (1/(4*Real.pi^2))^192*Real.exp (-4*K-59904)/upperConstant
  have hrow := row_integrable g f hf B hB U
  have htrans := (state_left_preserving U).integrable_comp_of_integrable hrow
  have hi : Integrable (fun h : State => (f (U*h)-f U)^2) boundaryHaar :=
    Integrable.of_bound (((hf.comp (measurable_const.mul measurable_id)).sub measurable_const).pow_const 2).aestronglyMeasurable
      (4*|B|^2) (ae_of_all _ (fun h => delta_bound f B hB U (U*h)))
  have hm := setIntegral_mono_on (hi.const_mul (C*g.function U^2)).integrableOn
    htrans.integrableOn (capBox_measurable t) (fun h hh => by
      have hx := mul_le_mul_of_nonneg_right (local_weight t ht h1 g K U h hK hh) (sq_nonneg (f (U*h)-f U))
      change C*g.function U^2*(f (U*h)-f U)^2 ≤ _
      dsimp [C]
      nlinarith only [hx])
  rw [integral_const_mul] at hm
  have hfull := setIntegral_le_integral (s := capBox t) htrans
    (ae_of_all _ (fun h => mul_nonneg (g.function_pos U).le (mul_nonneg
      (show 0 ≤ weight (1/t^2) U (U*h) 1 by unfold weight; exact (Real.exp_pos _).le)
      (mul_nonneg (g.function_pos (U*h)).le (sq_nonneg _)))))
  have he := (state_left_preserving U).integral_comp (MeasurableEquiv.mulLeft U).measurableEmbedding
    (fun V => g.function U*(weight (1/t^2) U V 1*(g.function V*(f V-f U)^2)))
  exact hm.trans (hfull.trans_eq he)

private theorem raw_native_lower (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (g : GroundData (1/t^2))
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (B : ℝ) (hB : ∀ U,|f U| ≤ B) (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) (K : ℝ) :
    ((1/(4*Real.pi^2))^192*Real.exp (-4*K-59904)/upperConstant)*
      (∫ U in {U | (1/t^2)*spatialAction U ≤ K},capIncrement t f U ∂g.stationary) ≤
      2*g.value*SelfAdjointContractionIteration.dissipation (operator g) (hmem.toLp f) := by
  let A : Set State := {U | (1/t^2)*spatialAction U ≤ K}
  let C : ℝ := (1/(4*Real.pi^2))^192*Real.exp (-4*K-59904)/upperConstant
  have hA : MeasurableSet A := measurableSet_le (spatial_action_measurable.const_mul (1/t^2)) measurable_const
  have hi := (capIncrement_integrable g t f hf B hB).indicator hA
  have hw := (PeriodicBoundaryHaarReduction.stationary_integrable_iff g (A.indicator (capIncrement t f))).mp hi
  have hrow := (PeriodicPhysicalDirichlet.fixed_energy_integrable g f hf B hB).integral_prod_left
  have hm := integral_mono (hw.const_mul C) hrow (fun U => by
    by_cases hU : U∈A
    · rw [Set.indicator_of_mem hU]
      simpa only [mul_assoc] using row_lower t ht h1 g f hf B hB K U hU
    · rw [Set.indicator_of_notMem hU,mul_zero,mul_zero]
      exact integral_nonneg (fun V => mul_nonneg (g.function_pos U).le (mul_nonneg
        (show 0 ≤ weight (1/t^2) U V 1 by unfold weight; exact (Real.exp_pos _).le)
        (mul_nonneg (g.function_pos V).le (sq_nonneg _)))))
  simp_rw [integral_const_mul] at hm
  have hs := g.stationary_integral (A.indicator (capIncrement t f))
  rw [integral_indicator hA] at hs
  have he := PeriodicPhysicalDirichlet.native_fixed_gauge_dirichlet g f hf hmem B hB hInv
  have he' := (eq_div_iff (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) g.value_pos) g.normalizer_pos).ne').mp he
  have hs' := (eq_div_iff g.normalizer_pos.ne').mp hs
  change C*(∫ U in A,capIncrement t f U ∂g.stationary) ≤ _
  rw [← hs',← he'] at hm
  apply (mul_le_mul_iff_left₀ g.normalizer_pos).mp
  convert hm using 1 <;> ring


/-- Coupling-uniform domination of normalized local squared increments on the
low-action anchor region. This is an actual native physical energy estimate,
not a global Poincare or mass-gap assertion. -/
theorem native_local_lower (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (g : GroundData (1/t^2))
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (B : ℝ) (hB : ∀ U,|f U| ≤ B) (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) (K : ℝ) :
    localConstant K*((∫ U in {U | (1/t^2)*spatialAction U ≤ K},capIncrement t f U ∂g.stationary)/
      boundaryHaar.real (capBox t)) ≤
      SelfAdjointContractionIteration.dissipation (operator g) (hmem.toLp f) := by
  let a : ℝ := 1/(4*Real.pi^2)
  let C : ℝ := a^192*Real.exp (-4*K-59904)/upperConstant
  let m : ℝ := boundaryHaar.real (capBox t)
  let J : ℝ := ∫ U in {U | (1/t^2)*spatialAction U ≤ K},capIncrement t f U ∂g.stationary
  let E : ℝ := SelfAdjointContractionIteration.dissipation (operator g) (hmem.toLp f)
  have ha : 0 < a := by dsimp [a]; positivity
  have hC : 0 < C := div_pos (mul_pos (pow_pos ha _) (Real.exp_pos _)) upperConstant_pos
  have hm : a^192*t^576 ≤ m := by
    have hp := pow_le_pow_left₀ (mul_nonneg ha.le (pow_nonneg ht.le 3))
      (SU2HaarSmallCap.mass_lower t ht.le h1) 192
    rw [mul_pow,show (t^3)^192=t^576 by ring] at hp
    exact hp.trans_eq (capBox_mass t).symm
  have hmp : 0 < m := (mul_pos (pow_pos ha _) (pow_pos ht _)).trans_le hm
  have hval : g.value ≤ upperConstant*t^576 := by
    have hl := eigenvalue_laplace_upper (1/t^2) (by positivity) g
    have hu := SU2HaarLaplaceUpper.laplace_scaled_upper 1 t (by norm_num) ht h1
    have hp := pow_le_pow_left₀ (CubeHaarUpper.laplace_pos (1/t^2) (by positivity)).le hu 192
    rw [mul_pow,show (t^3)^192=t^576 by ring] at hp
    exact hl.trans (by simpa only [upperConstant] using hp)
  have hrel : localConstant K*(2*upperConstant)=C*a^192 := by
    dsimp [localConstant,C,a]
    field_simp [upperConstant_pos.ne']
  have hcoef : localConstant K*(2*g.value) ≤ C*m := by
    calc
      _ ≤ (localConstant K*(2*upperConstant))*t^576 := by
        nlinarith only [mul_le_mul_of_nonneg_left hval (localConstant_pos K).le]
      _ = (C*a^192)*t^576 := by rw [hrel]
      _ = C*(a^192*t^576) := by ring
      _ ≤ C*m := mul_le_mul_of_nonneg_left hm hC.le
  have hJ : 0 ≤ J := integral_nonneg (fun U => integral_nonneg (fun h => sq_nonneg (f (U*h)-f U)))
  have hraw : C*J ≤ 2*g.value*E := raw_native_lower t ht h1 g f hf hmem B hB hInv K
  have hx := mul_le_mul_of_nonneg_left hraw hmp.le
  have hh : localConstant K*(2*g.value)*J ≤ m*(2*g.value*E) := by
    calc
      _ ≤ (C*m)*J := mul_le_mul_of_nonneg_right hcoef hJ
      _ = m*(C*J) := by ring
      _ ≤ _ := hx
  have hscaled : (2*g.value)*(localConstant K*J) ≤ (2*g.value)*(m*E) := by
    nlinarith only [hh]
  have hb : localConstant K*J ≤ m*E :=
    (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0:ℝ)<2) g.value_pos)).mp hscaled
  change localConstant K*(J/m) ≤ E
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hmp).mpr (by nlinarith only [hb])

end OperatorDerivativeRewrite.Foundation.PeriodicLocalEnergy
