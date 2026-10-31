import Foundation.PeriodicKineticCapLower
import Foundation.PeriodicQuarticKernelBlock
/-! Coupling-uniform local comparison for the actual periodic Wilson ground.
Genuine Haar cap averaging, spatial potential bounds and the constructed
eigenfunction equation retain all192 boundary links. Constants depend on this
fixed cell and the low-action bound. No spectral or continuum gap is proved. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalGroundHarnack
open PeriodicPhysicalKineticReduction CubeHaarUpper
open QuaternionSU2Representation FourCubePinnedCoercivity PeriodicTemporalSlab PeriodicWilsonSlab
open PeriodicKineticCapLower PeriodicLoopVariation PeriodicQuarticGaugeOverlap PeriodicQuarticKernelBlock

theorem cap_packet (U h : State) (t : ℝ) (ht : 0 ≤ t) (hh : h∈capBox t) :
    U*h∈packet U (3*t) := by
  intro e
  have hd : defect (h e)≤3*t^2 := hh e (Set.mem_univ e)
  have he := left_distance_isometry (h e) 1 (U e)
  simp only [mul_one] at he
  change distance (U e*h e) (U e)≤3*t
  rw [he]
  have hs := distance_sq (h e) 1
  simp only [inv_one,mul_one] at hs
  have hn : 0 ≤ distance (h e) 1 := norm_nonneg _
  nlinarith [hn]

theorem cap_spatial_upper (U h : State) (t : ℝ) (ht : 0 ≤ t) (hh : h∈capBox t) :
    spatialAction (U*h)≤2*spatialAction U+27648*t^2 := by
  have hs := spatial_packet_upper (U*h) U (3*t) (cap_packet U h t ht hh)
  nlinarith

theorem cap_temporal_upper (U W h : State) (t : ℝ) (ht : 0 ≤ t)
    (hW : W∈packet U (3*t)) (hh : h∈capBox t) :
    temporalAction W (U*h) 1≤3456*t^2 := by
  have hZ := cap_packet U h t ht hh
  have hp (e : SpatialEdge) :
      distance (W e) (PeriodicSlabGauge.gaugeAction 1 (U*h) e)^2 ≤36*t^2 := by
    simp only [PeriodicSlabGauge.gaugeAction,Pi.one_apply,one_mul,inv_one,mul_one]
    have hz := hZ e
    rw [distance_symm] at hz
    have hd : distance (W e) ((U*h) e)≤6*t := by
      linarith [distance_triangle (W e) (U e) ((U*h) e),hW e]
    have hs := pow_le_pow_left₀ (show 0 ≤ distance (W e) ((U*h) e) from norm_nonneg _) hd 2
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hp e)
  rw [Finset.sum_const,Finset.card_univ,edge_count,nsmul_eq_mul,
    PeriodicFlatLocusQuarticObstruction.temporal_distance_identity] at hs
  norm_num at hs
  nlinarith only [hs]

attribute [local irreducible] temporalAction spatialAction

private theorem kinetic_measurable (β : ℝ) :
    Measurable (fun q : State × State => kineticDensity β q.1 q.2) := by
  have hc : Measurable (fun q : State × State => (q,(1 : Gauge))) :=
    measurable_id.prodMk measurable_const
  have hm : Measurable (fun q : State × State => temporalAction q.1 q.2 1) :=
    temporal_action_joint_measurable.comp hc
  have he : Measurable (fun q : State × State => Real.exp (-β*temporalAction q.1 q.2 1)) :=
    (hm.const_mul (-β)).exp
  unfold kineticDensity
  exact he.div_const _

private theorem kinetic_bounds (β : ℝ) (hb : 0 ≤ β) (U V : State) :
    0 < kineticDensity β U V ∧ kineticDensity β U V ≤ 1/(laplace β^192) := by
  constructor
  · exact div_pos (Real.exp_pos _) (pow_pos (laplace_pos β hb) _)
  · exact div_le_div_of_nonneg_right
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb)
        (temporal_action_bounds U V 1).1)) (pow_pos (laplace_pos β hb) _).le

private theorem cap_joint_integrable (β t : ℝ) (hb : 0 ≤ β) (U : State)
    (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ V,|f V| ≤ B) :
    Integrable (fun q : State × State => kineticDensity β (U*q.1) q.2*f q.2)
      ((boundaryHaar.restrict (capBox t)).prod boundaryHaar) := by
  have hm : Measurable (fun q : State × State => kineticDensity β (U*q.1) q.2*f q.2) :=
    ((kinetic_measurable β).comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)).mul
      (hf.comp measurable_snd)
  apply Integrable.of_bound hm.aestronglyMeasurable ((1/(laplace β^192))*|B|)
  filter_upwards with q
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (kinetic_bounds β hb _ _).1]
  exact mul_le_mul (kinetic_bounds β hb _ _).2 ((hB q.2).trans (le_abs_self _))
    (abs_nonneg _) (by positivity)

theorem kinetic_cap_average (β t : ℝ) (hb : 0 ≤ β) (U : State)
    (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ V,|f V| ≤ B)
    (h0 : ∀ V,0 ≤ f V) :
    (QuaternionSU2Representation.law.real (SU2HaarSmallCap.cap t))^192*
      Real.exp (-576*β*t^2)*kinetic β f U ≤
        ∫ h in capBox t,kinetic β f (U*h) ∂boundaryHaar := by
  let A : ℝ := (law.real (SU2HaarSmallCap.cap t))^192*Real.exp (-576*β*t^2)
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg measureReal_nonneg _) (Real.exp_pos _).le
  have hj := cap_joint_integrable β t hb U f hf B hB
  have hi : Integrable (fun V => (∫ h in capBox t,kineticDensity β (U*h) V ∂boundaryHaar)*f V)
      boundaryHaar := by
    simpa only [integral_mul_const] using hj.integral_prod_right
  have hlow := integral_mono_of_nonneg
    (ae_of_all boundaryHaar (fun V => mul_nonneg
      (mul_nonneg hA (kinetic_bounds β hb U V).1.le) (h0 V))) hi
    (ae_of_all boundaryHaar (fun V => mul_le_mul_of_nonneg_right (kinetic_cap_lower β t hb U V) (h0 V)))
  have hs : (∫ h in capBox t,kinetic β f (U*h) ∂boundaryHaar)=
      ∫ V,(∫ h in capBox t,kineticDensity β (U*h) V ∂boundaryHaar)*f V ∂boundaryHaar := by
    simpa only [kinetic,integral_mul_const] using integral_integral_swap
      (f := fun h V : State => kineticDensity β (U*h) V*f V)
      (μ := boundaryHaar.restrict (capBox t)) (ν := boundaryHaar) hj
  change A*kinetic β f U ≤ _
  calc
    _ = ∫ V,(A*kineticDensity β U V)*f V ∂boundaryHaar := by
      unfold kinetic
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with V
      ring
    _ ≤ ∫ V,(∫ h in capBox t,kineticDensity β (U*h) V ∂boundaryHaar)*f V ∂boundaryHaar := hlow
    _ = _ := hs.symm

open PeriodicSlabGround CubeHaarUpper

def dressed {β : ℝ} (g : GroundData β) (U : State) : ℝ := multiplier β U*g.function U

private theorem dressed_pos {β : ℝ} (g : GroundData β) (U : State) : 0 < dressed g U :=
  mul_pos (Real.exp_pos _) (g.function_pos U)
private theorem dressed_measurable {β : ℝ} (g : GroundData β) : Measurable (dressed g) := by
  unfold dressed multiplier
  exact (((spatial_action_measurable.const_mul (-β)).div_const 2).exp).mul g.measurable
private theorem dressed_bound {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (V : State) :
    |dressed g V| ≤ g.upper := by
  rw [abs_of_pos (dressed_pos g V)]
  have hM : multiplier β V ≤ 1 := by
    unfold multiplier
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (spatial_action_bounds V).1) (by norm_num)
  have h := mul_le_mul_of_nonneg_right hM (g.function_pos V).le
  have h' : dressed g V ≤ g.function V := by simpa only [one_mul,dressed] using h
  exact h'.trans ((le_abs_self _).trans (g.bounds V).2)
private theorem dressed_eigen {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (U : State) :
    g.value*dressed g U=laplace β^192*(multiplier β U)^2*kinetic β (dressed g) U := by
  have h := congrArg (fun x : ℝ => x*multiplier β U) (dressed_ground_equation hb g U)
  unfold dressed
  linear_combination -h
private theorem multiplier_square (β : ℝ) (U : State) :
    (multiplier β U)^2=Real.exp (-β*spatialAction U) := by
  unfold multiplier
  rw [pow_two,← Real.exp_add]
  congr 1
  ring
private theorem tw_nonneg {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (U : State) :
    0 ≤ kinetic β (dressed g) U :=
  integral_nonneg (fun V => mul_nonneg (kinetic_bounds β hb U V).1.le (dressed_pos g V).le)
private theorem dressed_cap_integrable {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (U : State) (t : ℝ) :
    Integrable (fun h => dressed g (U*h)) (boundaryHaar.restrict (capBox t)) :=
  Integrable.of_bound ((dressed_measurable g).comp (measurable_const.mul measurable_id)).aestronglyMeasurable
    g.upper (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using dressed_bound hb g (U*h)))

theorem ground_cap_lower {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (U : State)
    (t : ℝ) (ht : 0 ≤ t) :
    (law.real (SU2HaarSmallCap.cap t))^192*Real.exp (-β*(spatialAction U+28224*t^2))*dressed g U ≤
      ∫ h in capBox t,dressed g (U*h) ∂boundaryHaar := by
  let z : ℝ := laplace β^192
  let m : ℝ := (law.real (SU2HaarSmallCap.cap t))^192
  let E0 : ℝ := Real.exp (-β*(2*spatialAction U+27648*t^2))
  let E : ℝ := Real.exp (-β*(spatialAction U+28224*t^2))
  let A : ℝ := m*Real.exp (-576*β*t^2)
  have hz : 0 < z := pow_pos (laplace_pos β hb) _
  have hj := cap_joint_integrable β t hb U (dressed g) (dressed_measurable g) g.upper (dressed_bound hb g)
  have hTi : Integrable (fun h => kinetic β (dressed g) (U*h))
      (boundaryHaar.restrict (capBox t)) := by
    simpa only [kinetic] using hj.integral_prod_left
  have hpoint (h : State) (hh : h∈capBox t) :
      z*E0*kinetic β (dressed g) (U*h) ≤ g.value*dressed g (U*h) := by
    have hM : E0 ≤ (multiplier β (U*h))^2 := by
      rw [multiplier_square]
      apply Real.exp_le_exp.mpr
      have hs := cap_spatial_upper U h t ht hh
      nlinarith [mul_nonneg hb (sub_nonneg.mpr hs)]
    rw [dressed_eigen hb g]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hz.le) (tw_nonneg hb g _)
  have hi := setIntegral_mono_on (hTi.const_mul (z*E0))
    ((dressed_cap_integrable hb g U t).const_mul g.value) (capBox_measurable t) hpoint
  simp only [integral_const_mul] at hi
  have ha := kinetic_cap_average β t hb U (dressed g) (dressed_measurable g) g.upper
    (dressed_bound hb g) (fun V => (dressed_pos g V).le)
  have hbase := (mul_le_mul_of_nonneg_left ha (mul_pos hz (Real.exp_pos _)).le).trans hi
  have he : E0*Real.exp (-576*β*t^2)=E*(multiplier β U)^2 := by
    dsimp [E0,E]
    rw [multiplier_square,← Real.exp_add,← Real.exp_add]
    apply congrArg Real.exp
    ring
  have hre : z*E0*(A*kinetic β (dressed g) U)=g.value*(m*E*dressed g U) := by
    calc
      _ = m*(E0*Real.exp (-576*β*t^2))*(z*kinetic β (dressed g) U) := by dsimp [A]; ring
      _ = m*(E*(multiplier β U)^2)*(z*kinetic β (dressed g) U) := by rw [he]
      _ = (m*E)*(laplace β^192*(multiplier β U)^2*kinetic β (dressed g) U) := by dsimp [z]; ring
      _ = g.value*(m*E*dressed g U) := by rw [← dressed_eigen hb g U]; ring
  change z*E0*(A*kinetic β (dressed g) U) ≤ _ at hbase
  rw [hre] at hbase
  exact (mul_le_mul_iff_right₀ g.value_pos).mp hbase

private theorem state_left_preserving (U : State) :
    MeasurePreserving (fun h : State => U*h) boundaryHaar boundaryHaar := by
  unfold boundaryHaar
  exact measurePreserving_pi (fun _ => law) (fun _ => law)
    (fun e => measurePreserving_mul_left law (U e))

private theorem translated_row_integrable {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (U W : State) :
    Integrable (fun h => kineticDensity β W (U*h)*dressed g (U*h)) boundaryHaar := by
  have hm : Measurable (fun h => kineticDensity β W (U*h)*dressed g (U*h)) :=
    ((kinetic_measurable β).comp (measurable_const.prodMk (measurable_const.mul measurable_id))).mul
      ((dressed_measurable g).comp (measurable_const.mul measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable ((1/(laplace β^192))*|g.upper|)
  filter_upwards with h
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (kinetic_bounds β hb W (U*h)).1]
  exact mul_le_mul (kinetic_bounds β hb W (U*h)).2 ((dressed_bound hb g (U*h)).trans (le_abs_self _))
    (abs_nonneg _) (by positivity)

theorem ground_from_cap_lower {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (U W : State)
    (t : ℝ) (ht : 0 ≤ t) (hW : W∈packet U (3*t)) :
    (multiplier β W)^2*Real.exp (-3456*β*t^2)*
      (∫ h in capBox t,dressed g (U*h) ∂boundaryHaar) ≤ g.value*dressed g W := by
  let z : ℝ := laplace β^192
  let E : ℝ := Real.exp (-3456*β*t^2)
  have hz : 0 < z := pow_pos (laplace_pos β hb) _
  have hpoint (h : State) (hh : h∈capBox t) : E/z ≤ kineticDensity β W (U*h) := by
    unfold kineticDensity
    apply div_le_div_of_nonneg_right _ hz.le
    apply Real.exp_le_exp.mpr
    have hs := cap_temporal_upper U W h t ht hW hh
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hs)]
  have hrow := translated_row_integrable hb g U W
  have hi := setIntegral_mono_on ((dressed_cap_integrable hb g U t).const_mul (E/z))
    hrow.integrableOn (capBox_measurable t)
    (fun h hh => mul_le_mul_of_nonneg_right (hpoint h hh) (dressed_pos g (U*h)).le)
  simp only [integral_const_mul] at hi
  have hfull := setIntegral_le_integral (s := capBox t) hrow
    (ae_of_all _ (fun h => mul_nonneg (kinetic_bounds β hb W (U*h)).1.le (dressed_pos g (U*h)).le))
  have he := (state_left_preserving U).integral_comp (MeasurableEquiv.mulLeft U).measurableEmbedding
    (fun Z : State => kineticDensity β W Z*dressed g Z)
  change (∫ h,kineticDensity β W (U*h)*dressed g (U*h) ∂boundaryHaar)=kinetic β (dressed g) W at he
  have hbase := hi.trans (hfull.trans_eq he)
  have hcoeff : 0 ≤ z*(multiplier β W)^2 := mul_nonneg hz.le (sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hbase hcoeff
  have hleft : z*(multiplier β W)^2*((E/z)*(∫ h in capBox t,dressed g (U*h) ∂boundaryHaar))=
      (multiplier β W)^2*E*(∫ h in capBox t,dressed g (U*h) ∂boundaryHaar) := by
    field_simp
  rw [hleft] at hscaled
  change _ ≤ laplace β^192*(multiplier β W)^2*kinetic β (dressed g) W at hscaled
  rw [← dressed_eigen hb g W] at hscaled
  exact hscaled

theorem ground_local_raw {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (U W : State)
    (t : ℝ) (ht : 0 ≤ t) (hW : W∈packet U (3*t)) :
    (law.real (SU2HaarSmallCap.cap t))^192*
      Real.exp (-β*(spatialAction U+spatialAction W+31680*t^2))*dressed g U ≤ g.value*dressed g W := by
  have h := (mul_le_mul_of_nonneg_left (ground_cap_lower hb g U t ht)
    (mul_nonneg (sq_nonneg (multiplier β W)) (Real.exp_pos (-3456*β*t^2)).le)).trans
      (ground_from_cap_lower hb g U W t ht hW)
  have he : (multiplier β W)^2*Real.exp (-3456*β*t^2)*
      Real.exp (-β*(spatialAction U+28224*t^2))=
      Real.exp (-β*(spatialAction U+spatialAction W+31680*t^2)) := by
    rw [multiplier_square,← Real.exp_add,← Real.exp_add]
    apply congrArg Real.exp
    ring
  have hre : (multiplier β W)^2*Real.exp (-3456*β*t^2)*
      ((law.real (SU2HaarSmallCap.cap t))^192*Real.exp (-β*(spatialAction U+28224*t^2))*dressed g U)=
      (law.real (SU2HaarSmallCap.cap t))^192*
        Real.exp (-β*(spatialAction U+spatialAction W+31680*t^2))*dressed g U := by
    calc
      _ = (law.real (SU2HaarSmallCap.cap t))^192*
        ((multiplier β W)^2*Real.exp (-3456*β*t^2)*Real.exp (-β*(spatialAction U+28224*t^2)))*dressed g U := by ring
      _ = _ := by rw [he]
  rw [hre] at h
  exact h

private theorem eigenvalue_scaled_upper (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1)
    (g : GroundData (1/t^2)) : g.value ≤ PeriodicGroundHaarScale.upperConstant*t^576 := by
  have hl := PeriodicGroundHaarScale.eigenvalue_laplace_upper (1/t^2) (by positivity) g
  have hu := SU2HaarLaplaceUpper.laplace_scaled_upper 1 t (by norm_num) ht h1
  have hp := pow_le_pow_left₀ (laplace_pos (1/t^2) (by positivity)).le hu 192
  rw [mul_pow] at hp
  have he : (t^3)^192=t^576 := by ring
  rw [he] at hp
  exact hl.trans (by simpa only [PeriodicGroundHaarScale.upperConstant] using hp)

private theorem scaled_comparison (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1)
    (g : GroundData (1/t^2)) (U W : State) (L : ℝ)
    (hcost : (1/t^2)*(spatialAction U+spatialAction W+31680*t^2) ≤ L)
    (hraw : (law.real (SU2HaarSmallCap.cap t))^192*
      Real.exp (-(1/t^2)*(spatialAction U+spatialAction W+31680*t^2))*dressed g U ≤
        g.value*dressed g W) :
    (1/(4*Real.pi^2))^192*Real.exp (-L)*dressed g U ≤
      PeriodicGroundHaarScale.upperConstant*dressed g W := by
  have hm := pow_le_pow_left₀
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 1/(4*Real.pi^2)) (pow_nonneg ht.le 3))
    (SU2HaarSmallCap.mass_lower t ht.le h1) 192
  rw [mul_pow] at hm
  have he : (t^3)^192=t^576 := by ring
  rw [he] at hm
  have hE : Real.exp (-L) ≤ Real.exp (-(1/t^2)*(spatialAction U+spatialAction W+31680*t^2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hlow := mul_le_mul_of_nonneg_right
    (mul_le_mul hm hE (Real.exp_pos (-L)).le (pow_nonneg measureReal_nonneg _)) (dressed_pos g U).le
  have hu := mul_le_mul_of_nonneg_right (eigenvalue_scaled_upper t ht h1 g) (dressed_pos g W).le
  have h := hlow.trans (hraw.trans hu)
  have hfinal : t^576*((1/(4*Real.pi^2))^192*Real.exp (-L)*dressed g U) ≤
      t^576*(PeriodicGroundHaarScale.upperConstant*dressed g W) := by
    convert h using 1 <;> ring
  exact (mul_le_mul_iff_right₀ (pow_pos ht 576)).mp hfinal

/-- Uniform comparison for actual constructed grounds on a kinetic-scale
neighborhood of any low-action reference; both directions use the same constant. -/
theorem uniform_local_comparison (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1)
    (g : GroundData (1/t^2)) (U W : State) (K : ℝ)
    (hK : (1/t^2)*spatialAction U ≤ K) (hW : W∈packet U (3*t)) :
    ((1/(4*Real.pi^2))^192*Real.exp (-(3*K+59328))*dressed g U ≤
        PeriodicGroundHaarScale.upperConstant*dressed g W) ∧
    ((1/(4*Real.pi^2))^192*Real.exp (-(3*K+59328))*dressed g W ≤
        PeriodicGroundHaarScale.upperConstant*dressed g U) := by
  have hscale : (1/t^2)*t^2=1 := by field_simp
  have hs := mul_le_mul_of_nonneg_left (spatial_packet_upper W U (3*t) hW)
    (show (0 : ℝ) ≤ 1/t^2 by positivity)
  have hc : (1/t^2)*(spatialAction U+spatialAction W+31680*t^2) ≤ 3*K+59328 := by
    nlinarith
  have hU : U∈packet W (3*t) := by
    intro e
    rw [distance_symm]
    exact hW e
  constructor
  · exact scaled_comparison t ht h1 g U W _ hc (ground_local_raw (by positivity) g U W t ht.le hW)
  · apply scaled_comparison t ht h1 g W U _ _ (ground_local_raw (by positivity) g W U t ht.le hU)
    simpa only [add_comm (spatialAction U) (spatialAction W)] using hc
end OperatorDerivativeRewrite.Foundation.PeriodicLocalGroundHarnack
