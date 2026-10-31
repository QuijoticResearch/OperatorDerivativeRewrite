import Foundation.PeriodicQuarticCurvature
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Prod
/-! The bare three-matrix SU(2) commutator-quartic Gibbs factor has infinite
positive Lebesgue integral on its full nine-dimensional real coordinate space.
A measurable, measure-preserving triangular translation exposes valley boxes
of volume16R and potential at most68. This is an obstruction to replacing a
quantum/transfer zero-mode law by a normalized bare exp(-cV) density. It is NOT
nonexistence of the actual compact Wilson ground law, a divergence of a quantum
heat trace, or a spectral/mass-gap assertion. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.SU2QuarticValleyNonintegrable
abbrev Four := Fin 4 → ℝ
abbrev Base := ℝ × Four
abbrev Config := Base × Four
def baseMeasure : Measure Base := (volume : Measure ℝ).prod volume
def configMeasure : Measure Config := baseMeasure.prod volume
private instance : SFinite baseMeasure := by unfold baseMeasure; infer_instance
def X (p : Config) : Fin 3 → ℝ := ![p.1.1,p.1.2 0,p.1.2 1]
def Y (p : Config) : Fin 3 → ℝ := ![p.1.2 2,p.2 0,p.2 1]
def Z (p : Config) : Fin 3 → ℝ := ![p.1.2 3,p.2 2,p.2 3]
def crossSquare (a b : Fin 3 → ℝ) : ℝ :=
  (a 1*b 2-a 2*b 1)^2+(a 2*b 0-a 0*b 2)^2+(a 0*b 1-a 1*b 0)^2
def potential (p : Config) : ℝ := crossSquare (X p) (Y p)+crossSquare (X p) (Z p)+crossSquare (Y p) (Z p)
def shift (b : Base) : Four := ![b.2 2*b.2 0/b.1,b.2 2*b.2 1/b.1,b.2 3*b.2 0/b.1,b.2 3*b.2 1/b.1]
def shear (p : Config) : Config := (p.1,p.2+shift p.1)
theorem shear_preserving : MeasurePreserving shear configMeasure configMeasure := by
  unfold shear configMeasure
  change MeasurePreserving (fun p : Config => (id p.1,p.2+shift p.1)) (baseMeasure.prod volume) (baseMeasure.prod volume)
  apply (MeasurePreserving.id baseMeasure).skew_product (g := fun b e => e+shift b)
  · unfold shift
    fun_prop
  · filter_upwards with b
    exact (measurePreserving_add_right (volume : Measure Four) (shift b)).map_eq
def box (R : ℝ) : Set Config :=
  ((Icc R (2*R)) ×ˢ (Icc (fun _ => 0) (fun _ => R))) ×ˢ
    (Icc (fun _ => -(1/R)) (fun _ => 1/R))
theorem box_measurable (R : ℝ) : MeasurableSet (box R) := by
  exact (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc
theorem box_volume (R : ℝ) (hR : 0<R) : configMeasure.real (box R)=16*R := by
  unfold Measure.real configMeasure baseMeasure box
  have houter := Measure.prod_prod (μ := (volume : Measure ℝ).prod (volume : Measure Four)) (ν := (volume : Measure Four)) ((Icc R (2*R)) ×ˢ (Icc (fun _ => 0) (fun _ => R))) (Icc (fun _ => -(1/R)) (fun _ => 1/R))
  rw [houter]
  simp only [Measure.prod_prod,Real.volume_Icc,Real.volume_Icc_pi]
  simp only [sub_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal (sub_nonneg.mpr (by linarith : R≤2*R)),
    ENNReal.toReal_ofReal hR.le]
  have hp : 0≤1/R- -(1/R) := by have h := one_div_pos.mpr hR; linarith
  simp only [ENNReal.toReal_ofReal hp,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  field_simp
  <;> ring
theorem mul_error (R a e : ℝ) (hR : 0<R) (ha : |a|≤2*R) (he : |e|≤1/R) : |a*e|≤2 := by
  rw [abs_mul]
  have h := mul_le_mul ha he (abs_nonneg _) (by positivity : 0≤2*R)
  have hh : (2*R)*(1/R)=2 := by field_simp
  exact hh ▸ h
theorem basic_cross (R u v e f : ℝ) (hR : 0<R)
    (hu : |u|≤R) (hv : |v|≤R) (he : |e|≤1/R) (hf : |f|≤1/R) : |u*f-v*e|≤2 := by
  have h1 := mul_le_mul hu hf (abs_nonneg _) hR.le
  have h2 := mul_le_mul hv he (abs_nonneg _) hR.le
  have hh : R*(1/R)=1 := by field_simp
  rw [hh] at h1 h2
  have h := abs_sub (u*f) (v*e)
  rw [abs_mul,abs_mul] at h
  linarith
theorem potential_bound (R : ℝ) (hR : 1≤R) (p : Config) (hp : p∈box R) : potential (shear p)≤68 := by
  rcases hp with ⟨⟨hx,hb⟩,he⟩
  have hr : 0<R := by linarith
  have hxpos : 0<p.1.1 := hr.trans_le hx.1
  have hbabs (i : Fin 4) : |p.1.2 i|≤R := abs_le.mpr ⟨by linarith [(hb.1 i)],hb.2 i⟩
  have heabs (i : Fin 4) : |p.2 i|≤1/R := abs_le.mpr ⟨he.1 i,he.2 i⟩
  have hratio (i : Fin 4) : |p.1.2 i/p.1.1|≤1 := by
    rw [abs_div,abs_of_pos hxpos]
    exact (div_le_one hxpos).mpr ((hbabs i).trans hx.1)
  have h1 := basic_cross R (p.1.2 0) (p.1.2 1) (p.2 0) (p.2 1) hr (hbabs 0) (hbabs 1) (heabs 0) (heabs 1)
  have h2 := basic_cross R (p.1.2 0) (p.1.2 1) (p.2 2) (p.2 3) hr (hbabs 0) (hbabs 1) (heabs 2) (heabs 3)
  have h3 := basic_cross R (p.1.2 2) (p.1.2 3) (p.2 0) (p.2 2) hr (hbabs 2) (hbabs 3) (heabs 0) (heabs 2)
  have h4 := basic_cross R (p.1.2 3) (p.1.2 2) (p.2 3) (p.2 1) hr (hbabs 3) (hbabs 2) (heabs 3) (heabs 1)
  have hxabs : |p.1.1|≤2*R := by rw [abs_of_pos hxpos];exact hx.2
  have hx0 := mul_error R p.1.1 (p.2 0) hr hxabs (heabs 0)
  have hx1 := mul_error R p.1.1 (p.2 1) hr hxabs (heabs 1)
  have hx2 := mul_error R p.1.1 (p.2 2) hr hxabs (heabs 2)
  have hx3 := mul_error R p.1.1 (p.2 3) hr hxabs (heabs 3)
  have ee : |p.2 0*p.2 3-p.2 1*p.2 2|≤2 := by
    have hinv : 1/R≤1 := (div_le_one hr).mpr hR
    have e1 := mul_le_mul (heabs 0) (heabs 3) (abs_nonneg _) (by positivity : 0≤1/R)
    have e2 := mul_le_mul (heabs 1) (heabs 2) (abs_nonneg _) (by positivity : 0≤1/R)
    have hsq : (1/R)*(1/R)≤1 := mul_le_one₀ hinv (by positivity) hinv
    have ha := abs_sub (p.2 0*p.2 3) (p.2 1*p.2 2)
    simp only [abs_mul] at ha
    linarith
  have hm1 : |(p.1.2 2/p.1.1)*(p.1.2 0*p.2 3-p.1.2 1*p.2 2)|≤2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul (hratio 2) h2 (abs_nonneg _) (by norm_num : (0:ℝ)≤1)]
  have hm2 : |(p.1.2 3/p.1.1)*(p.1.2 1*p.2 0-p.1.2 0*p.2 1)|≤2 := by
    rw [abs_mul]
    have ha : |p.1.2 1*p.2 0-p.1.2 0*p.2 1|≤2 := by simpa only [abs_sub_comm] using h1
    nlinarith [mul_le_mul (hratio 3) ha (abs_nonneg _) (by norm_num : (0:ℝ)≤1)]
  have hbig : |(p.1.2 2/p.1.1)*(p.1.2 0*p.2 3-p.1.2 1*p.2 2)+
      (p.1.2 3/p.1.1)*(p.1.2 1*p.2 0-p.1.2 0*p.2 1)+(p.2 0*p.2 3-p.2 1*p.2 2)|≤6 := by
    exact (abs_add_le _ _).trans (by linarith [abs_add_le ((p.1.2 2/p.1.1)*(p.1.2 0*p.2 3-p.1.2 1*p.2 2)) ((p.1.2 3/p.1.1)*(p.1.2 1*p.2 0-p.1.2 0*p.2 1))])
  have heq : potential (shear p)=
      (p.1.2 0*p.2 1-p.1.2 1*p.2 0)^2+(p.1.1*p.2 1)^2+(p.1.1*p.2 0)^2+
      ((p.1.2 0*p.2 3-p.1.2 1*p.2 2)^2+(p.1.1*p.2 3)^2+(p.1.1*p.2 2)^2)+
      (((p.1.2 2/p.1.1)*(p.1.2 0*p.2 3-p.1.2 1*p.2 2)+
       (p.1.2 3/p.1.1)*(p.1.2 1*p.2 0-p.1.2 0*p.2 1)+(p.2 0*p.2 3-p.2 1*p.2 2))^2+
       (p.1.2 3*p.2 1-p.1.2 2*p.2 3)^2+(p.1.2 2*p.2 2-p.1.2 3*p.2 0)^2) := by
    simp only [potential,crossSquare,X,Y,Z,shear,shift,Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons]
    field_simp
    <;> ring
  rw [heq]
  have sq2 (a : ℝ) (ha : |a|≤2) : a^2≤4 := by simpa only [sq_abs,show (2:ℝ)^2=4 by norm_num,show (6:ℝ)^2=36 by norm_num] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  have sq6 (a : ℝ) (ha : |a|≤6) : a^2≤36 := by simpa only [sq_abs,show (2:ℝ)^2=4 by norm_num,show (6:ℝ)^2=36 by norm_num] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  linarith [sq2 _ h1,sq2 _ h2,sq2 _ h3,sq2 _ h4,sq2 _ hx0,sq2 _ hx1,sq2 _ hx2,sq2 _ hx3,sq6 _ hbig]

theorem potential_nonnegative (p : Config) : 0≤potential p := by
  unfold potential crossSquare
  positivity

def weight (c : ℝ) (p : Config) : ℝ := Real.exp (-c*potential p)

theorem weight_continuous (c : ℝ) : Continuous (weight c) := by
  unfold weight potential crossSquare X Y Z
  fun_prop

theorem box_finite (R : ℝ) : configMeasure (box R)≠⊤ := by
  unfold configMeasure baseMeasure box
  have houter := Measure.prod_prod (μ := (volume : Measure ℝ).prod (volume : Measure Four)) (ν := (volume : Measure Four)) ((Icc R (2*R)) ×ˢ (Icc (fun _ => 0) (fun _ => R))) (Icc (fun _ => -(1/R)) (fun _ => 1/R))
  rw [houter]
  simp only [Measure.prod_prod,Real.volume_Icc,Real.volume_Icc_pi]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- An integrable weight would have arbitrarily large mass already in these
positive-measure nine-dimensional valley boxes. No restriction to a null slice. -/
theorem integral_lower_of_integrable (c R : ℝ) (hc : 0≤c) (hR : 1≤R)
    (hf : Integrable (weight c) configMeasure) :
    16*R*Real.exp (-68*c)≤∫ p,weight c (shear p) ∂configMeasure := by
  have hg := shear_preserving.integrable_comp_of_integrable hf
  have hk : IntegrableOn (fun _ : Config => Real.exp (-68*c)) (box R) configMeasure :=
    integrableOn_const (box_finite R)
  have hm := setIntegral_mono_on hk hg.integrableOn (box_measurable R) (fun p hp => by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (potential_bound R hR p hp) hc
    linarith)
  simp only [setIntegral_const,smul_eq_mul] at hm
  rw [box_volume R (by linarith)] at hm
  exact hm.trans (setIntegral_le_integral hg (ae_of_all _ (fun _ => (Real.exp_pos _).le)))

/-- The bare three-matrix SU(2) commutator-quartic Gibbs factor on all nine
real coordinates cannot be normalized against Lebesgue measure. This is NOT
the ground law of the compact Wilson transfer or a quantum heat-kernel trace. -/
theorem not_integrable_weight (c : ℝ) (hc : 0≤c) : ¬Integrable (weight c) configMeasure := by
  intro hf
  let I := ∫ p,weight c (shear p) ∂configMeasure
  let e := Real.exp (-68*c)
  have he : 0<e := Real.exp_pos _
  let R := max 1 ((I+1)/(16*e))
  have hr : 1≤R := le_max_left _ _
  have hl : (I+1)/(16*e)≤R := le_max_right _ _
  have hmul := (div_le_iff₀ (show 0<16*e by positivity)).mp hl
  have h := integral_lower_of_integrable c R hc hr hf
  change 16*R*e≤I at h
  nlinarith



def imaginary (a : Fin 3 → ℝ) : Quaternion ℝ := ⟨0,a 0,a 1,a 2⟩

theorem lie_bracket_norm (a b : Fin 3 → ℝ) :
    Quaternion.normSq (imaginary a*imaginary b-imaginary b*imaginary a)=4*crossSquare a b := by
  norm_num [imaginary,crossSquare,Quaternion.normSq_def',Quaternion.re_mul,
    Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,
    Quaternion.re_sub,Quaternion.imI_sub,Quaternion.imJ_sub,Quaternion.imK_sub]
  ring

theorem potential_lie_brackets (p : Config) :
    4*potential p=Quaternion.normSq (imaginary (X p)*imaginary (Y p)-imaginary (Y p)*imaginary (X p))+
      Quaternion.normSq (imaginary (X p)*imaginary (Z p)-imaginary (Z p)*imaginary (X p))+
      Quaternion.normSq (imaginary (Y p)*imaginary (Z p)-imaginary (Z p)*imaginary (Y p)) := by
  simp only [lie_bracket_norm,potential]
  ring

theorem partition_eq_top (c : ℝ) (hc : 0≤c) :
    (∫⁻ p,ENNReal.ofReal (weight c p) ∂configMeasure)=⊤ := by
  by_contra h
  apply not_integrable_weight c hc
  refine ⟨(weight_continuous c).measurable.aestronglyMeasurable,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => (Real.exp_pos _).le))).mpr
    (lt_top_iff_ne_top.mpr h)


end OperatorDerivativeRewrite.Foundation.SU2QuarticValleyNonintegrable
