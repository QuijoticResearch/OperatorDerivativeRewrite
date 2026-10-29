import Foundation.SU2HemisphereChart
import Foundation.FourCubePinnedConcentration

/-! Actual finite-cell Gaussian domination on a precisely stated Haar-chart cutoff. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeHemisphereCoercivity
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open FourCubePinnedHaar FourCubePinnedCoercivity FourCubePinnedConcentration
open OneSidedPinnedInterior (Free)

theorem chartRate_ge_one (y : Triple) : 1 ≤ chartRate y := by
  unfold chartRate
  nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2)]

theorem radius_sq (y : Triple) : (radius y)^2=chartRate y :=
  Real.sq_sqrt (chartRate_positive y).le

theorem local_defect_lower (y : Triple) (hy : chartRate y ≤ 2) :
    (chartRate y-1)/4 ≤ defect (hemisphereChart y) := by
  have hp := radius_positive y
  have hs := radius_sq y
  have h1 : 1 ≤ radius y := by nlinarith [chartRate_ge_one y]
  have hu : radius y ≤ 3/2 := by nlinarith
  have hd : radius y*(radius y+1) ≤ 4 := by nlinarith
  have hn : 0 ≤ chartRate y-1 := sub_nonneg.mpr (chartRate_ge_one y)
  have he : defect (hemisphereChart y)=
      (chartRate y-1)/(radius y*(radius y+1)) := by
    rw [defect,chart_halfTrace]
    field_simp
    nlinarith
  rw [he]
  exact div_le_div_of_nonneg_left hn (by positivity) hd

abbrev Field := Free → Triple

def chartField (Y : Field) : PinnedState := fun e => hemisphereChart (Y e)
def quadraticMass (Y : Field) : ℝ := ∑ e : Free,(chartRate (Y e)-1)

theorem local_action_lower (Y : Field) (hY : ∀ e,chartRate (Y e) ≤ 2) :
    quadraticMass Y/372 ≤ pinnedAction (chartField Y) := by
  have he (e : Free) : chartRate (Y e)-1 ≤ 12*pinnedAction (chartField Y) := by
    have hl := local_defect_lower (Y e) (hY e)
    have hg := pinned_coordinate_bound (chartField Y) e
    change defect (hemisphereChart (Y e)) ≤ 3*pinnedAction (chartField Y) at hg
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ => he e)
  simp only [Finset.sum_const,Finset.card_univ,OneSidedPinnedInterior.free_card,nsmul_eq_mul] at hs
  have h31 : ((31 : ℕ) : ℝ)=31 := by norm_num
  rw [h31] at hs
  unfold quadraticMass
  linarith

theorem chartRate_smul (t : ℝ) (y : Triple) :
    chartRate (t • y)-1=t^2*(chartRate y-1) := by
  simp [chartRate]
  ring

theorem quadraticMass_smul (t : ℝ) (Y : Field) :
    quadraticMass (t • Y)=t^2*quadraticMass Y := by
  unfold quadraticMass
  simp only [Pi.smul_apply,chartRate_smul,Finset.mul_sum]

theorem scaled_action_lower (β t : ℝ) (hβ : 0 ≤ β) (ht : β*t^2=1)
    (Y : Field) (hY : ∀ e,chartRate (t • Y e) ≤ 2) :
    quadraticMass Y/372 ≤ β*pinnedAction (chartField (t • Y)) := by
  have hh := mul_le_mul_of_nonneg_left (local_action_lower (t • Y) hY) hβ
  rw [quadraticMass_smul] at hh
  have he : β*(t^2*quadraticMass Y/372)=quadraticMass Y/372 := by
    calc
      _ = (β*t^2)*quadraticMass Y/372 := by ring
      _ = _ := by rw [ht]; ring
  rw [he] at hh
  exact hh

theorem scaled_boltzmann_domination (β t : ℝ) (hβ : 0 ≤ β) (ht : β*t^2=1)
    (Y : Field) (hY : ∀ e,chartRate (t • Y e) ≤ 2) :
    Real.exp (-β*pinnedAction (chartField (t • Y))) ≤
      Real.exp (-quadraticMass Y/372) := by
  apply Real.exp_le_exp.mpr
  linarith [scaled_action_lower β t hβ ht Y hY]

theorem quadraticMass_sum_squares (Y : Field) :
    quadraticMass Y=∑ e : Free,∑ a : Fin 3,(Y e a)^2 := by
  unfold quadraticMass
  apply Finset.sum_congr rfl
  intro e _
  simp [chartRate,Fin.sum_univ_three]
  ring

theorem quadraticMass_zero : quadraticMass (0 : Field)=0 := by
  rw [quadraticMass_sum_squares]
  simp

theorem gaussian_envelope_integrable :
    Integrable (fun Y : Field => Real.exp (-quadraticMass Y/372)) := by
  have hi : Integrable (fun y : Triple => Real.exp (-(chartRate y-1)/372)) := by
    have hh := Integrable.fintype_prod (fun _ : Fin 3 =>
      integrable_exp_neg_mul_sq (b := (1/372 : ℝ)) (by norm_num))
    rw [volume_pi]
    convert hh using 1
    funext y
    rw [← Real.exp_sum]
    congr 1
    simp [chartRate,Fin.sum_univ_three]
    ring
  have he : (fun Y : Field => Real.exp (-quadraticMass Y/372))=
      (fun Y => ∏ e : Free,Real.exp (-(chartRate (Y e)-1)/372)) := by
    funext Y
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_div,Finset.sum_neg_distrib]
    rfl
  rw [he,volume_pi]
  exact Integrable.fintype_prod (fun _ : Free => hi)

theorem small_defect_chartRate (U : SU2) (hU : defect U < 1/4) :
    chartRate (coordinates U) ≤ 2 := by
  have hq : 3/4 < halfTrace U := by unfold defect at hU; linarith
  have hH : U ∈ hemisphere := by change 0 < halfTrace U; linarith
  have ht := chart_halfTrace (coordinates U)
  rw [chart_coordinates U hH] at ht
  have hp := radius_positive (coordinates U)
  have hm : halfTrace U*radius (coordinates U)=1 := by rw [ht]; exact inv_mul_cancel₀ hp.ne'
  have hr : radius (coordinates U) ≤ 4/3 := by nlinarith
  have hs := pow_le_pow_left₀ hp.le hr 2
  rw [← radius_sq]
  nlinarith

def localStateDomain : Set PinnedState :=
  {y | ∀ e : Free,0 < halfTrace (y e) ∧ chartRate (coordinates (y e)) ≤ 2}

theorem localStateDomain_measurable : MeasurableSet localStateDomain := by
  have hR : Measurable chartRate := by unfold chartRate; fun_prop
  unfold localStateDomain
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro e
  exact (measurableSet_lt measurable_const
    (halfTrace_measurable.comp (measurable_pi_apply e))).inter
      (measurableSet_le ((hR.comp coordinates_measurable).comp (measurable_pi_apply e))
        measurable_const)

theorem outside_localStateDomain_subset :
    localStateDomainᶜ ⊆ configurationTail (1/4) := by
  intro y hy
  by_contra hn
  apply hy
  intro e
  have hs : defect (y e) < 1/4 := by
    apply lt_of_not_ge
    intro hh
    apply hn
    exact Set.mem_iUnion.mpr ⟨e,hh⟩
  exact ⟨by unfold defect at hs; linarith,small_defect_chartRate (y e) hs⟩

theorem gibbs_outside_cutoff_le_tail (β : ℝ) :
    (gibbs β).real localStateDomainᶜ ≤ (gibbs β).real (configurationTail (1/4)) :=
  measureReal_mono outside_localStateDomain_subset

theorem gibbs_outside_cutoff_tendsto_zero :
    Tendsto (fun β : ℝ => (gibbs β).real localStateDomainᶜ) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun β => measureReal_nonneg))
    (Filter.Eventually.of_forall gibbs_outside_cutoff_le_tail)
  exact gibbs_configuration_tail_tendsto_zero (1/4) (by norm_num)

theorem gibbs_cutoff_tendsto_one :
    Tendsto (fun β : ℝ => (gibbs β).real localStateDomain) atTop (𝓝 1) := by
  have he (β : ℝ) : (gibbs β).real localStateDomain=
      1-(gibbs β).real localStateDomainᶜ := by
    have hh := measureReal_compl (μ := gibbs β) localStateDomain_measurable
    have hn : (gibbs β).real Set.univ=1 := by simp
    rw [hn] at hh
    linarith
  simp_rw [he]
  simpa using tendsto_const_nhds.sub gibbs_outside_cutoff_tendsto_zero

theorem quadraticMass_constant (a : ℝ) :
    quadraticMass (fun _ : Free => (![a,0,0] : Triple))=31*a^2 := by
  rw [quadraticMass_sum_squares]
  change (∑ _ : Free,∑ i : Fin 3,(![a,0,0] : Triple) i^2)=_
  have he : (∑ i : Fin 3,(![a,0,0] : Triple) i^2)=a^2 := by
    norm_num [Fin.sum_univ_three]
  rw [he,Finset.sum_const,Finset.card_univ,OneSidedPinnedInterior.free_card,nsmul_eq_mul]
  norm_num

theorem no_global_affine_quadratic_bound :
    ¬ ∃ c : ℝ,0 < c ∧ ∃ C : ℝ,∀ Y : Field,
      c*quadraticMass Y ≤ pinnedAction (chartField Y)+C := by
  rintro ⟨c,hc,C,h⟩
  let a : ℝ := Real.sqrt ((|C|+145)/(31*c))
  let Y : Field := fun _ => ![a,0,0]
  have ha : a^2=(|C|+145)/(31*c) := Real.sq_sqrt (by positivity)
  have hq : quadraticMass Y=31*((|C|+145)/(31*c)) := by
    change quadraticMass (fun _ : Free => (![a,0,0] : Triple))=_
    rw [quadraticMass_constant,ha]
  have hh := h Y
  have hb := (abs_le.mp (energySource_bound (chartField Y))).1
  unfold energySource at hb
  rw [hq] at hh
  have he : c*(31*((|C|+145)/(31*c)))=|C|+145 := by field_simp
  rw [he] at hh
  linarith [le_abs_self C]

theorem no_global_positive_quadratic_bound :
    ¬ ∃ c : ℝ,0 < c ∧ ∀ Y : Field,c*quadraticMass Y ≤ pinnedAction (chartField Y) := by
  rintro ⟨c,hc,h⟩
  exact no_global_affine_quadratic_bound ⟨c,hc,0,by simpa only [add_zero] using h⟩

end OperatorDerivativeRewrite.Foundation.FourCubeHemisphereCoercivity
