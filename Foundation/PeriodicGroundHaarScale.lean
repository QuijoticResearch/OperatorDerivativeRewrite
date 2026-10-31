import Foundation.PeriodicPlaquetteSeamSelection
import Foundation.SU2HaarLaplaceUpper
/-! Genuine temporal Haar row integration for the actual periodic Wilson slab.
The actual constructed principal value has a beta^(-288) upper bound for beta>=1,
using the verified single-link Haar Laplace estimate. The existing lower power384
is not sharpened here; no uniform half-scale ratio or mass gap is inferred.
A cap-volume upper bound records a direct Laplace reuse for future trials. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
namespace OperatorDerivativeRewrite.Foundation.PeriodicGroundHaarScale
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open FourCubePinnedCoercivity CubeHaarUpper
attribute [local irreducible] boundaryHaar gaugeHaar kernel defect weight temporalAction halfAction

def relative (U : State) (a : Gauge) (V : State) (e : SpatialEdge) : SU2 :=
  a e.1*V e*((a (shift e.1 e.2))⁻¹*(U e)⁻¹)

theorem relative_preserving (U : State) (a : Gauge) :
    MeasurePreserving (relative U a) boundaryHaar boundaryHaar := by
  unfold boundaryHaar relative
  exact measurePreserving_pi (fun _ => law) (fun _ => law)
    (fun e => (measurePreserving_mul_right law ((a (shift e.1 e.2))⁻¹*(U e)⁻¹)).comp
      (measurePreserving_mul_left law (a e.1)))

theorem relative_word (U V : State) (a : Gauge) (e : SpatialEdge) :
    relative U a V e=(temporalWord U V a e)⁻¹ := by
  unfold relative temporalWord
  group

theorem temporal_integral (β : ℝ) (U : State) (a : Gauge) :
    (∫ V,Real.exp (-β*temporalAction U V a) ∂boundaryHaar)=laplace β^192 := by
  let f : State → ℝ := fun V => Real.exp (-β*(∑ e : SpatialEdge,defect (V e)))
  let A : State := fun e => a e.1
  let B : State := fun e => (a (shift e.1 e.2))⁻¹*(U e)⁻¹
  have h := (relative_preserving U a).integral_comp
    ((MeasurableEquiv.mulLeft A).trans (MeasurableEquiv.mulRight B)).measurableEmbedding f
  have he (V : State) : f (relative U a V)=Real.exp (-β*temporalAction U V a) := by
    dsimp [f]
    unfold temporalAction
    apply congrArg Real.exp
    apply congrArg (fun x : ℝ => -β*x)
    apply Finset.sum_congr rfl
    intro e _
    rw [relative_word]
    rw [defect_inv]
    unfold defect
    rfl
  change (∫ V,f (relative U a V) ∂boundaryHaar)=∫ V,f V ∂boundaryHaar at h
  simp_rw [he] at h
  rw [h]
  have hf : f=fun V : State => ∏ e,Real.exp (-β*defect (V e)) := by
    funext V
    dsimp [f]
    rw [← Real.exp_sum]
    apply congrArg Real.exp
    exact Finset.mul_sum _ _ _
  rw [hf]
  unfold boundaryHaar
  change (∫ V : SpatialEdge → SU2,∏ e,Real.exp (-β*defect (V e)) ∂Measure.pi (fun _ => law))=_
  have hp := integral_fintype_prod_eq_pow (ι := SpatialEdge) (μ := law)
    (fun X : SU2 => Real.exp (-β*defect X))
  simpa only [laplace,edge_count] using hp

private theorem weight_pair_integrable (β : ℝ) (U : State) :
    Integrable (fun q : State × Gauge => weight β U q.1 q.2) (boundaryHaar.prod gaugeHaar) := by
  have hc : Measurable (fun q : State × Gauge => ((U,q.1),q.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  have hm : Measurable (fun q : State × Gauge => weight β U q.1 q.2) :=
    (weight_joint_measurable β).comp hc
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (768*|β|))
  filter_upwards with q
  rw [Real.norm_eq_abs,abs_of_pos ((Real.exp_pos _).trans_le (weight_bounds β U q.1 q.2).1)]
  exact (weight_bounds β U q.1 q.2).2

private theorem weight_v_integrable (β : ℝ) (U : State) (a : Gauge) :
    Integrable (fun V => weight β U V a) boundaryHaar := by
  have hc : Measurable (fun V : State => ((U,V),a)) :=
    (measurable_const.prodMk measurable_id).prodMk measurable_const
  have hm : Measurable (fun V : State => weight β U V a) :=
    (weight_joint_measurable β).comp hc
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (768*|β|))
  filter_upwards with V
  rw [Real.norm_eq_abs,abs_of_pos ((Real.exp_pos _).trans_le (weight_bounds β U V a).1)]
  exact (weight_bounds β U V a).2

private theorem temporal_v_integrable (β : ℝ) (hb : 0 ≤ β) (U : State) (a : Gauge) :
    Integrable (fun V => Real.exp (-β*temporalAction U V a)) boundaryHaar := by
  have hc : Measurable (fun V : State => ((U,V),a)) :=
    (measurable_const.prodMk measurable_id).prodMk measurable_const
  have hm : Measurable (fun V : State => Real.exp (-β*temporalAction U V a)) :=
    (temporal_action_joint_measurable.comp hc).const_mul (-β) |>.exp
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards with V
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb)
    (temporal_action_bounds U V a).1)

theorem weight_temporal_le (β : ℝ) (hb : 0 ≤ β) (U V : State) (a : Gauge) :
    weight β U V a ≤ Real.exp (-β*temporalAction U V a) := by
  unfold weight
  apply Real.exp_le_exp.mpr
  unfold halfAction
  nlinarith [mul_nonneg hb (spatial_action_bounds U).1,mul_nonneg hb (spatial_action_bounds V).1]

theorem kernel_row_upper (β : ℝ) (hb : 0 ≤ β) (U : State) :
    (∫ V,kernel β U V ∂boundaryHaar) ≤ laplace β^192 := by
  unfold kernel
  rw [integral_integral_swap (weight_pair_integrable β U)]
  have h : (∫ a,∫ V,weight β U V a ∂boundaryHaar ∂gaugeHaar) ≤
      ∫ _ : Gauge,laplace β^192 ∂gaugeHaar := by
    apply integral_mono_of_nonneg (ae_of_all _ (fun a => integral_nonneg (fun V => ((Real.exp_pos _).le.trans (weight_bounds β U V a).1))))
      (integrable_const _) (ae_of_all _ (fun a => ?_))
    rw [← temporal_integral β U a]
    exact integral_mono (weight_v_integrable β U a) (temporal_v_integrable β hb U a)
      (fun V => weight_temporal_le β hb U V a)
  simpa only [integral_const,probReal_univ,one_smul] using h

theorem eigenvalue_laplace_upper (β : ℝ) (hb : 0 ≤ β) (g : GroundData β) :
    g.value ≤ laplace β^192 := by
  have hi : Integrable g.function boundaryHaar := Integrable.of_bound
    g.measurable.aestronglyMeasurable g.upper (ae_of_all _ (fun U => by
      simpa only [Real.norm_eq_abs] using (g.bounds U).2))
  have hl := integral_mono (integrable_const g.lower) hi (fun U => (g.bounds U).1)
  simp only [integral_const,probReal_univ,one_smul] at hl
  have hp : 0 < ∫ U,g.function U ∂boundaryHaar := g.lower_pos.trans_le hl
  have he : pairing β (fun _ => 1) g.function=g.value*(∫ U,g.function U ∂boundaryHaar) := by
    unfold pairing
    simp_rw [g.eigen,one_mul]
    exact integral_const_mul _ _
  have hs := pairing_symmetric β (fun _ => 1) g.function measurable_const g.measurable
    1 g.upper (fun _ => by norm_num) (fun U => (g.bounds U).2)
  have hq : pairing β g.function (fun _ => 1) ≤ laplace β^192*(∫ U,g.function U ∂boundaryHaar) := by
    unfold pairing
    simp_rw [mul_one]
    have h := integral_mono_of_nonneg
      (ae_of_all _ (fun U => mul_nonneg (g.function_pos U).le
        (integral_nonneg (fun V => (kernel_positive β U V).le))))
      (hi.mul_const (laplace β^192)) (ae_of_all _ (fun U =>
        mul_le_mul_of_nonneg_left (kernel_row_upper β hb U) (g.function_pos U).le))
    rw [integral_mul_const] at h
    simpa only [mul_comm] using h
  have h := he.symm.trans_le (hs.trans_le hq)
  nlinarith

def upperConstant : ℝ := (SU2HaarLaplaceUpper.upperConstant 1)^192

theorem upperConstant_pos : 0 < upperConstant := by
  unfold upperConstant
  exact pow_pos (SU2HaarLaplaceUpper.upperConstant_pos 1 (by norm_num)) _

theorem eigenvalue_polynomial_upper (β : ℝ) (hb : 1 ≤ β) (g : GroundData β) :
    g.value ≤ upperConstant/β^288 := by
  have hp : 0 < β := by linarith
  let t : ℝ := 1/Real.sqrt β
  have ht : 0 < t := div_pos zero_lt_one (Real.sqrt_pos.mpr hp)
  have h1 : t ≤ 1 := (div_le_one (Real.sqrt_pos.mpr hp)).mpr (by simpa using Real.sqrt_le_sqrt hb)
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
  exact (eigenvalue_laplace_upper β hp.le g).trans (by simpa only [upperConstant,mul_one_div] using hpow)



open SU2HaarSmallCap

theorem cap_laplace_upper (t : ℝ) (ht : 0<t) :
    law.real (cap t) ≤ Real.exp 3*laplace (1/t^2) := by
  have hi := setIntegral_mono_on
    (integrable_const (Real.exp (-3 : ℝ))).integrableOn
    (laplace_integrable (1/t^2) (by positivity)).integrableOn (cap_measurable t)
    (fun U (hU : U∈cap t) => by
      have hd : defect U/t^2 ≤ 3 := (div_le_iff₀ (sq_pos_of_pos ht)).mpr hU
      apply Real.exp_le_exp.mpr
      calc
        (-3 : ℝ) ≤ -(defect U/t^2) := by linarith
        _ = -(1/t^2)*defect U := by ring)
  rw [setIntegral_const,smul_eq_mul] at hi
  have hj := setIntegral_le_integral (s := cap t)
    (laplace_integrable (1/t^2) (by positivity))
    (ae_of_all law (fun U => (Real.exp_pos (-(1/t^2)*defect U)).le))
  have h : Real.exp (-3 : ℝ)*law.real (cap t) ≤ laplace (1/t^2) := by
    simpa only [laplace,mul_comm] using hi.trans hj
  have hc : Real.exp (3 : ℝ)*Real.exp (-3 : ℝ)=1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    law.real (cap t)=Real.exp 3*(Real.exp (-3)*law.real (cap t)) := by
      rw [← mul_assoc,hc,one_mul]
    _ ≤ Real.exp 3*laplace (1/t^2) := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

theorem cap_polynomial_upper (t : ℝ) (ht : 0<t) (h1 : t≤1) :
    law.real (cap t) ≤ (Real.exp 3*SU2HaarLaplaceUpper.upperConstant 1)*t^3 := by
  have h := mul_le_mul_of_nonneg_left
    (SU2HaarLaplaceUpper.laplace_scaled_upper 1 t (by norm_num) ht h1) (Real.exp_pos (3 : ℝ)).le
  exact (cap_laplace_upper t ht).trans (by simpa only [mul_assoc] using h)

end OperatorDerivativeRewrite.Foundation.PeriodicGroundHaarScale
