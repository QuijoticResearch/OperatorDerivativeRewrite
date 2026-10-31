import Foundation.PeriodicPositiveMassAnchor
import Foundation.PeriodicPlaquetteNoise
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
/-! Logarithmic actual stationary action moments and native local plaquette loss.
Existing Wilson positivity/tails, layer cake and Gamma integration are reused.
All constants are fixed-cell. A single-probe loss is not an iteration-domain
or full center-even spectral-gap theorem. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicLogActionMoment
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
attribute [local irreducible] spatialAction
private instance prob {β : ℝ} (g : GroundData β) : IsProbabilityMeasure g.stationary := g.stationary_probability

def ratio : ℝ := PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant
def shift : ℝ := max 0 (Real.log ratio)
def scaled (β : ℝ) (U : State) : ℝ := β*spatialAction U
def excess (β : ℝ) (U : State) : ℝ := max (scaled β U-shift) 0

theorem ratio_pos : 0 < ratio := div_pos PeriodicGroundHaarScale.upperConstant_pos PeriodicGaugeSaturatedGround.eigenLowerConstant_pos

theorem shift_nonnegative : 0 ≤ shift := le_max_left _ _

theorem ratio_exp_shift : ratio*Real.exp (-shift) ≤ 1 := by
  calc
    _ = Real.exp (Real.log ratio-shift) := by
      rw [Real.exp_sub,Real.exp_log ratio_pos,Real.exp_neg,div_eq_mul_inv]
    _ ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr (le_max_right _ _))

theorem excess_tail {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) (t : ℝ) (ht : 0 ≤ t) :
    g.stationary.real {U | t<excess β U} ≤ Real.exp (-t) := by
  have hset : {U | t<excess β U}=PeriodicHighExcursion.region β (t+shift) := by
    ext U
    simp only [excess,scaled,PeriodicHighExcursion.region,Set.mem_ofPred_eq,lt_max_iff]
    constructor
    · rintro (h|h) <;> linarith
    · intro h; left; linarith
  rw [hset]
  have h := PeriodicPositiveMassAnchor.exponential_tail hb g (t+shift)
  change g.stationary.real (PeriodicHighExcursion.region β (t+shift)) ≤ ratio*Real.exp (-(t+shift)) at h
  calc
    _ ≤ ratio*Real.exp (-(t+shift)) := h
    _ = (ratio*Real.exp (-shift))*Real.exp (-t) := by rw [neg_add,Real.exp_add]; ring
    _ ≤ 1*Real.exp (-t) := mul_le_mul_of_nonneg_right ratio_exp_shift (Real.exp_pos _).le
    _ = _ := one_mul _

private theorem scaled_bound (β : ℝ) (U : State) : |scaled β U| ≤ |β| *384 := by
  rw [scaled,abs_mul,abs_of_nonneg (spatial_action_bounds U).1]
  exact mul_le_mul_of_nonneg_left (spatial_action_bounds U).2 (abs_nonneg β)

theorem scaled_memLp {β : ℝ} (g : GroundData β) (p : ℝ≥0∞) : MemLp (scaled β) p g.stationary :=
  MemLp.of_bound (spatial_action_measurable.const_mul β).aestronglyMeasurable (|β| *384)
    (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using scaled_bound β U))

theorem excess_memLp {β : ℝ} (g : GroundData β) (p : ℝ≥0∞) : MemLp (excess β) p g.stationary := by
  have hm : Measurable (excess β) := ((spatial_action_measurable.const_mul β).sub measurable_const).max measurable_const
  apply MemLp.of_bound hm.aestronglyMeasurable (|β| *384+|shift|)
  filter_upwards with U
  rw [Real.norm_eq_abs]
  have h0 : 0 ≤ excess β U := le_max_right _ _
  rw [abs_of_nonneg h0]
  change max (scaled β U-shift) 0 ≤ |β| *384+|shift|
  apply max_le
  · have h := scaled_bound β U
    linarith [le_abs_self (scaled β U),neg_le_abs shift]
  · exact add_nonneg (mul_nonneg (abs_nonneg β) (by norm_num)) (abs_nonneg shift)

theorem excess_mean {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    (∫ U,excess β U ∂g.stationary) ≤ 1 := by
  have hi := (excess_memLp g 2).integrable (by norm_num)
  rw [hi.integral_eq_integral_meas_lt (ae_of_all _ (fun U => le_max_right _ _))]
  calc
    _ ≤ ∫ t : ℝ in Ioi 0,Real.exp (-t) := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => measureReal_nonneg)) (integrableOn_exp_neg_Ioi 0)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact excess_tail hb g t ht.le
    _ = 1 := integral_exp_neg_Ioi_zero

theorem scaled_mean {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    (∫ U,scaled β U ∂g.stationary) ≤ shift+1 := by
  have hc : Integrable (fun U => shift+excess β U) g.stationary :=
    (integrable_const shift).add ((excess_memLp g 2).integrable (by norm_num))
  have hp (U : State) : scaled β U ≤ shift+excess β U := by
    have h := le_max_left (scaled β U-shift) 0
    change scaled β U ≤ shift+max (scaled β U-shift) 0
    linarith
  have h := integral_mono ((scaled_memLp g 2).integrable (by norm_num)) hc hp
  rw [integral_add (integrable_const shift) ((excess_memLp g 2).integrable (by norm_num))] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  linarith [excess_mean hb g]
private theorem scalar_gamma_one :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-t))*ENNReal.ofReal t)=1 := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-t)*t) (Ioi 0) := by
    have h := Real.GammaIntegral_convergent (by norm_num : 0 < (2:ℝ))
    norm_num at h
    exact h
  have hg : Real.Gamma (2:ℝ)=1 := by simp
  have he : (∫ t : ℝ in Ioi 0,Real.exp (-t)*t)=1 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1) (by norm_num) (by norm_num)
    norm_num [hg] at h
    simpa only [mul_comm] using h
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)] (fun t : ℝ => Real.exp (-t)*t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le ht.le
  have hc := ofReal_integral_eq_lintegral_ofReal hi hn
  rw [he] at hc
  simp only [ENNReal.ofReal_one] at hc
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le] at hc
  exact hc.symm

theorem excess_square {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    (∫ U,excess β U^2 ∂g.stationary) ≤ 2 := by
  have hnon : 0 ≤ᵐ[g.stationary] excess β := ae_of_all _ (fun U => le_max_right _ _)
  have hm := (excess_memLp g 2).aestronglyMeasurable.aemeasurable
  have hl := lintegral_rpow_eq_lintegral_meas_lt_mul g.stationary hnon hm (by norm_num : 0 < (2:ℝ))
  norm_num [Real.rpow_two] at hl
  have ht : (∫⁻ t : ℝ in Ioi 0, g.stationary {U | t<excess β U}*ENNReal.ofReal t) ≤ 1 := by
    calc
      _ ≤ ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-t))*ENNReal.ofReal t := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have htail : g.stationary {U | t<excess β U} ≤ ENNReal.ofReal (Real.exp (-t)) := by
          calc
            _ = ENNReal.ofReal (g.stationary.real {U | t<excess β U}) :=
              (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
            _ ≤ _ := ENNReal.ofReal_le_ofReal (excess_tail hb g t ht.le)
        exact mul_le_mul_of_nonneg_right htail zero_le
      _ = 1 := scalar_gamma_one
  have hbnd : (∫⁻ U,ENNReal.ofReal (excess β U^2) ∂g.stationary) ≤ (2:ℝ≥0∞) := by
    rw [hl]
    calc
      _ ≤ 2*1 := mul_le_mul_of_nonneg_left ht zero_le
      _ = 2 := by norm_num
  have hreal := ENNReal.toReal_mono (by norm_num : (2:ℝ≥0∞) ≠ ∞) hbnd
  rw [← ofReal_integral_eq_lintegral_ofReal (excess_memLp g 2).integrable_sq
    (ae_of_all _ (fun U => sq_nonneg (excess β U))),
    ENNReal.toReal_ofReal (integral_nonneg (fun U => sq_nonneg (excess β U)))] at hreal
  norm_num at hreal
  exact hreal

theorem scaled_square {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    (∫ U,scaled β U^2 ∂g.stationary) ≤ shift^2+2*shift+2 := by
  have hiY := (excess_memLp g 2).integrable (by norm_num)
  have hiY2 := (excess_memLp g 2).integrable_sq
  have hc1 : Integrable (fun U => shift^2+(2*shift)*excess β U) g.stationary :=
    (integrable_const _).add (hiY.const_mul _)
  have hc2 : Integrable (fun U => shift^2+(2*shift)*excess β U+excess β U^2) g.stationary := hc1.add hiY2
  have hp (U : State) : scaled β U^2 ≤ shift^2+(2*shift)*excess β U+excess β U^2 := by
    have hx : 0 ≤ scaled β U := mul_nonneg (by linarith) (spatial_action_bounds U).1
    have hxl : scaled β U ≤ shift+excess β U := by
      have h := le_max_left (scaled β U-shift) 0
      change scaled β U ≤ shift+max (scaled β U-shift) 0
      linarith
    have h := pow_le_pow_left₀ hx hxl 2
    nlinarith only [h]
  have h := integral_mono (scaled_memLp g 2).integrable_sq hc2 hp
  rw [integral_add hc1 hiY2,integral_add (integrable_const _) (hiY.const_mul _),integral_const_mul] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  have hmean := mul_le_mul_of_nonneg_left (excess_mean hb g)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) shift_nonnegative)
  nlinarith [excess_square hb g]

open ProbabilityTheory QuaternionSU2Representation PeriodicCurvatureVariance PeriodicCurvatureTransfer PeriodicSlabL2

def squareConstant : ℝ := shift^2+2*shift+2

theorem squareConstant_pos : 0 < squareConstant := by
  unfold squareConstant
  nlinarith [sq_nonneg shift,shift_nonnegative]

private theorem component_le_sum {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (i : ι) : f i ≤ ∑ j, f j := by
  classical
  exact Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

theorem plaquette_variance {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) (p : SpatialFace) :
    variance (plaquette p) g.stationary ≤ squareConstant/β^2 := by
  have hv := variance_le_expectation_sq (μ := g.stationary)
    (X := fun U => plaquette p U-1) ((plaquette_measurable p).sub measurable_const).aestronglyMeasurable
  rw [variance_sub_const (plaquette_measurable p).aestronglyMeasurable 1] at hv
  simp only [Pi.pow_apply] at hv
  have hpoint (U : State) : β^2*(plaquette p U-1)^2 ≤ scaled β U^2 := by
    have hnn (j : SpatialFace) : 0 ≤ 1-plaquette j U :=
      sub_nonneg.mpr (abs_le.mp (halfTrace_bound (spatialWord U j))).2
    have hd0 : 1-plaquette p U ≤ ∑ j : SpatialFace, (1-plaquette j U) :=
      component_le_sum (fun j : SpatialFace => 1-plaquette j U) hnn p
    have he : (∑ j : SpatialFace, (1-plaquette j U))=spatialAction U := by
      unfold spatialAction
      rfl
    have hd : 1-plaquette p U ≤ spatialAction U := hd0.trans_eq he
    have hn : 0 ≤ 1-plaquette p U := sub_nonneg.mpr (abs_le.mp (halfTrace_bound (spatialWord U p))).2
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn hd 2) (sq_nonneg β)
    dsimp only [scaled]
    nlinarith only [h]
  have h := integral_mono_of_nonneg (ae_of_all _ (fun U => mul_nonneg (sq_nonneg β) (sq_nonneg (plaquette p U-1))))
    (scaled_memLp g 2).integrable_sq (ae_of_all _ hpoint)
  rw [integral_const_mul] at h
  have hh := (mul_le_mul_of_nonneg_left hv (sq_nonneg β)).trans h
  have hm : (∫ U,scaled β U^2 ∂g.stationary) ≤ squareConstant := scaled_square hb g
  have hp : 0 < β := by linarith
  apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
  nlinarith only [hh,hm]

/-- Actual local center-even plaquette probe only; no invariant iteration domain is asserted. -/
theorem plaquette_native_loss {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) (p : SpatialFace) :
    3/(2401*squareConstant) ≤ ‖operator g (normalized g p)-normalized g p‖ ∧
    3/(2401*squareConstant) ≤ SelfAdjointContractionIteration.dissipation (operator g) (normalized g p) ∧
    ‖operator g (normalized g p)‖^2+6/(2401*squareConstant) ≤ 1 := by
  have hp : 0 < β := by linarith
  have hv := plaquette_variance hb g p
  have hV := PeriodicCurvatureVariance.variance_pos g p
  have hs : (1+6*β)^2 ≤ 49*β^2 := by
    have h := mul_nonneg (show 0 ≤ β-1 by linarith) (show 0 ≤ 13*β+1 by linarith)
    nlinarith
  have hden : 0 < 49*(1+6*β)^2 := mul_pos (by norm_num) (sq_pos_of_pos (by linarith))
  have hc : 6/(2401*β^2) ≤ 6/(49*(1+6*β)^2) :=
    div_le_div_of_nonneg_left (by norm_num) hden (by nlinarith only [hs])
  have h1 := div_le_div_of_nonneg_right hc hV.le
  have h2 : (6/(2401*β^2))/(squareConstant/β^2) ≤
      (6/(2401*β^2))/variance (plaquette p) g.stationary :=
    div_le_div_of_nonneg_left
      (div_nonneg (by norm_num : (0:ℝ) ≤ 6) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2401) (sq_nonneg β))) hV hv
  have he : (6/(2401*β^2))/(squareConstant/β^2)=6/(2401*squareConstant) := by
    field_simp [hp.ne',squareConstant_pos.ne']
  rw [he] at h2
  have hr := h2.trans h1
  have hh : 3/(2401*squareConstant) ≤ (6/(49*(1+6*β)^2))/(2*variance (plaquette p) g.stationary) := by
    have heq : (6/(49*(1+6*β)^2))/(2*variance (plaquette p) g.stationary)=
        ((6/(49*(1+6*β)^2))/variance (plaquette p) g.stationary)/2 := by ring
    rw [heq,show 3/(2401*squareConstant)=(6/(2401*squareConstant))/2 by ring]
    exact div_le_div_of_nonneg_right hr (by norm_num)
  refine ⟨hh.trans (PeriodicPlaquetteNoise.normalized_residual_lower β hp.le g p),
    hh.trans (PeriodicPlaquetteNoise.normalized_dirichlet_lower β hp.le g p),?_⟩
  have hn := PeriodicPlaquetteNoise.normalized_norm_loss β hp.le g p
  linarith only [hr,hn]
end OperatorDerivativeRewrite.Foundation.PeriodicLogActionMoment
