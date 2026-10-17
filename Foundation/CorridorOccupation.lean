import Foundation.CorridorMaximumRegularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Threshold occupation needs control of the threshold level set. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology symmDiff
namespace OperatorDerivativeRewrite.Foundation.CorridorOccupation
set_option backward.isDefEq.respectTransparency false

def below {α : Type*} (f : α → ℝ) (a : ℝ) : Set α := {x | f x<a}
def strip {α : Type*} (f : α → ℝ) (a ε : ℝ) : Set α := {x | |f x-a|≤ε}
def occupation {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (a : ℝ) : ℝ :=
  μ.real (below f a)

theorem disagreement_subset_strip {α : Type*} (f g : α → ℝ) (a ε : ℝ)
    (hb : ∀ x, |f x-g x|≤ε) : below f a ∆ below g a ⊆ strip f a ε := by
  intro x hx
  change |f x-a|≤ε
  obtain ⟨hl, hu⟩ := abs_le.mp (hb x)
  rcases hx with hx | hx
  · have hf : f x<a := hx.1
    have hg : a≤g x := le_of_not_gt hx.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hg : g x<a := hx.1
    have hf : a≤f x := le_of_not_gt hx.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem disagreement_measure_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (a ε : ℝ) (hb : ∀ x, |f x-g x|≤ε) :
    μ (below f a ∆ below g a)≤μ (strip f a ε) :=
  measure_mono (disagreement_subset_strip f g a ε hb)

theorem occupation_difference_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f g : α → ℝ) (a ε : ℝ) (hb : ∀ x, |f x-g x|≤ε) :
    |occupation μ f a-occupation μ g a|≤μ.real (strip f a ε) := by
  have hs := disagreement_subset_strip f g a ε hb
  have hfg : below f a \ below g a ⊆ strip f a ε :=
    fun x hx => hs (Or.inl hx)
  have hgf : below g a \ below f a ⊆ strip f a ε :=
    fun x hx => hs (Or.inr hx)
  apply abs_le.mpr
  constructor
  · have h := (le_measureReal_sdiff (μ := μ) (s₁ := below g a) (s₂ := below f a)).trans
      (measureReal_mono hgf)
    unfold occupation
    linarith
  · exact (le_measureReal_sdiff (μ := μ)).trans (measureReal_mono hfg)

def belowIndicator {α : Type*} (f : α → ℝ) (a : ℝ) : α → ℝ :=
  (below f a).indicator (1 : α → ℝ)

theorem below_measurable {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (hf : Measurable f) (a : ℝ) : MeasurableSet (below f a) :=
  measurableSet_lt hf measurable_const

theorem indicator_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) (a : ℝ) :
    Integrable (belowIndicator f a) μ :=
  (integrable_const 1).indicator (below_measurable hf a)

theorem indicator_norm_le {α : Type*} (f : α → ℝ) (a : ℝ) (x : α) :
    ‖belowIndicator f a x‖≤1 := by
  classical
  by_cases hx : f x<a <;> simp [belowIndicator, below, hx]

theorem integral_indicator_occupation {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ} (hf : Measurable f) (a : ℝ) :
    (∫ x, belowIndicator f a x ∂μ)=occupation μ f a :=
  integral_indicator_one (below_measurable hf a)

theorem indicator_converges_off_threshold {α : Type*} (f : α → ℝ) (fₙ : ℕ → α → ℝ)
    (a : ℝ) (x : α) (hx : f x≠a)
    (hf : Tendsto (fun n => fₙ n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => belowIndicator (fₙ n) a x) atTop (𝓝 (belowIndicator f a x)) := by
  classical
  by_cases hlt : f x<a
  · have hn : ∀ᶠ n in atTop, fₙ n x<a := (tendsto_order.mp hf).2 a hlt
    apply tendsto_const_nhds.congr'
    filter_upwards [hn] with n hn
    simp [belowIndicator, below, hn, hlt]
  · have hgt : a<f x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hx)
    have hn : ∀ᶠ n in atTop, a<fₙ n x := (tendsto_order.mp hf).1 a hgt
    apply tendsto_const_nhds.congr'
    filter_upwards [hn] with n hn
    simp [belowIndicator, below, not_lt_of_gt hn, hlt]

theorem occupation_converges_null_threshold {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (fₙ : ℕ → α → ℝ) (a : ℝ)
    (hm : ∀ n, Measurable (fₙ n)) (hfm : Measurable f)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => fₙ n x) atTop (𝓝 (f x)))
    (hlevel : μ {x | f x=a}=0) :
    Tendsto (fun n => occupation μ (fₙ n) a) atTop (𝓝 (occupation μ f a)) := by
  have hne : ∀ᵐ x ∂μ, f x≠a := by
    apply ae_iff.mpr
    simpa only [not_not] using hlevel
  have hc : ∀ᵐ x ∂μ, Tendsto (fun n => belowIndicator (fₙ n) a x) atTop
      (𝓝 (belowIndicator f a x)) := by
    filter_upwards [hlim, hne] with x hx hn
    exact indicator_converges_off_threshold f fₙ a x hn hx
  have hi := tendsto_integral_of_dominated_convergence (fun _ : α => (1:ℝ))
    (fun n => (indicator_integrable μ (hm n) a).aestronglyMeasurable)
    (integrable_const 1) (fun n => Filter.Eventually.of_forall (indicator_norm_le (fₙ n) a)) hc
  simp only [integral_indicator_occupation μ (hm _) a, integral_indicator_occupation μ hfm a] at hi
  exact hi

abbrev unitTime : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)

theorem unitTime_mass : unitTime univ=1 := by
  simp [unitTime, Real.volume_Icc]

def trajectory (p _t : ℝ) : ℝ := 1/2+p

theorem trajectory_smooth (p : ℝ) : ContDiff ℝ ⊤ (trajectory p) := contDiff_const

theorem trajectory_uniform_difference (p t : ℝ) :
    |trajectory p t-trajectory 0 t|=|p| := by
  unfold trajectory
  congr 1
  ring

theorem trajectory_occupation_negative (p : ℝ) (hp : p<0) :
    occupation unitTime (trajectory p) (1/2)=1 := by
  have hs : below (trajectory p) (1/2)=univ := by
    ext t
    simp only [below, mem_ofPred_eq, mem_univ, iff_true, trajectory]
    linarith
  rw [occupation, hs, measureReal_def, unitTime_mass]
  norm_num

theorem trajectory_occupation_zero : occupation unitTime (trajectory 0) (1/2)=0 := by
  have hs : below (trajectory 0) (1/2)=∅ := by
    ext t
    simp [below, trajectory]
  rw [occupation, hs]
  simp

theorem arbitrarily_close_full_disagreement (δ : ℝ) (hδ : 0<δ) :
    ∃ p : ℝ, |p|<δ ∧ (∀ t : ℝ, 0<trajectory p t ∧ trajectory p t<1) ∧
      |occupation unitTime (trajectory p) (1/2)-occupation unitTime (trajectory 0) (1/2)|=1 := by
  let η : ℝ := min (δ/2) (1/8)
  have hη : 0<η := lt_min (by linarith) (by norm_num)
  have hδb : η≤δ/2 := min_le_left _ _
  have hsmall : η≤1/8 := min_le_right _ _
  refine ⟨-η, ?_, ?_, ?_⟩
  · rw [abs_neg, abs_of_pos hη]
    linarith
  · intro t
    unfold trajectory
    constructor <;> linarith
  · rw [trajectory_occupation_negative _ (neg_neg_of_pos hη), trajectory_occupation_zero]
    norm_num

theorem occupation_not_continuous :
    ¬ContinuousAt (fun p : ℝ => occupation unitTime (trajectory p) (1/2)) 0 := by
  intro hc
  obtain ⟨δ, hδ, hh⟩ := (Metric.continuousAt_iff.mp hc) (1/2) (by norm_num)
  obtain ⟨p, hp, ht, hd⟩ := arbitrarily_close_full_disagreement δ hδ
  have hh' := hh (show dist p 0<δ by simpa [Real.dist_eq] using hp)
  simp only [Real.dist_eq] at hh'
  rw [hd] at hh'
  norm_num at hh'

theorem threshold_atom_identity {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hf : Measurable f) (a : ℝ) :
    (μ.map f) {a}=μ {x | f x=a} := by
  rw [Measure.map_apply hf (measurableSet_singleton a)]
  rfl

theorem counterexample_threshold_mass : unitTime {t | trajectory 0 t=(1/2:ℝ)}=1 := by
  have hs : {t | trajectory 0 t=(1/2:ℝ)}=(univ : Set ℝ) := by
    ext t
    simp [trajectory]
  rw [hs, unitTime_mass]

def sectorEnergy (p : ℝ) (i : Fin 3) (_t : ℝ) : ℝ :=
  if i=0 then 1/2+p else 1/4-p/2

theorem sectorEnergy_smooth (p : ℝ) (i : Fin 3) : ContDiff ℝ ⊤ (sectorEnergy p i) :=
  contDiff_const

theorem sectorEnergy_parameter_continuous (i : Fin 3) (t : ℝ) :
    Continuous (fun p => sectorEnergy p i t) := by
  by_cases hi : i=0 <;> simp only [sectorEnergy, hi, ite_true, ite_false] <;> fun_prop

theorem sectorEnergy_positive (p : ℝ) (hp : |p|≤1/8) (i : Fin 3) (t : ℝ) :
    0<sectorEnergy p i t := by
  obtain ⟨hl, hu⟩ := abs_le.mp hp
  by_cases hi : i=0 <;> simp only [sectorEnergy, hi, ite_true, ite_false] <;> linarith

theorem sectorEnergy_sum (p t : ℝ) : (∑ i : Fin 3, sectorEnergy p i t)=1 := by
  norm_num [Fin.sum_univ_succ, sectorEnergy]
  ring

def sectorConcentration (p t : ℝ) : ℝ :=
  CorridorMaximumRegularity.finiteMaximum Finset.univ Finset.univ_nonempty (sectorEnergy p) t /
    (∑ i : Fin 3, sectorEnergy p i t)

theorem sectorConcentration_eq (p : ℝ) (hp : |p|≤1/8) (t : ℝ) :
    sectorConcentration p t=trajectory p t := by
  rw [sectorConcentration, sectorEnergy_sum, div_one]
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
    intro i hi
    obtain ⟨hl, hu⟩ := abs_le.mp hp
    by_cases hz : i=0 <;> simp only [sectorEnergy, trajectory, hz, ite_true, ite_false] <;> linarith
  · change sectorEnergy p (0 : Fin 3) t≤_
    exact Finset.le_sup' (fun i : Fin 3 => sectorEnergy p i t) (Finset.mem_univ (0 : Fin 3))

theorem finite_sector_arbitrarily_close_failure (δ : ℝ) (hδ : 0<δ) :
    ∃ p : ℝ, |p|<δ ∧ (∀ i t, 0<sectorEnergy p i t) ∧
      |occupation unitTime (sectorConcentration p) (1/2)-
        occupation unitTime (sectorConcentration 0) (1/2)|=1 := by
  have hsmall : 0<min δ (1/8:ℝ) := lt_min hδ (by norm_num)
  obtain ⟨p, hp, ht, hd⟩ := arbitrarily_close_full_disagreement _ hsmall
  have hpbound : |p|≤1/8 := (hp.trans_le (min_le_right _ _)).le
  refine ⟨p, hp.trans_le (min_le_left _ _), sectorEnergy_positive p hpbound, ?_⟩
  have he : sectorConcentration p=trajectory p := funext (sectorConcentration_eq p hpbound)
  have hzero : sectorConcentration 0=trajectory 0 :=
    funext (sectorConcentration_eq 0 (by norm_num))
  rw [he, hzero]
  exact hd

theorem sectorEnergy_strictly_dominant (p : ℝ) (hp : |p|≤1/8) (i : Fin 3)
    (hi : i≠0) (t : ℝ) : sectorEnergy p i t<sectorEnergy p 0 t := by
  have hl := (abs_le.mp hp).1
  simp only [sectorEnergy, hi, ite_false, ite_true]
  linarith

theorem sectorEnergy_uniform_difference (p : ℝ) (i : Fin 3) (t : ℝ) :
    |sectorEnergy p i t-sectorEnergy 0 i t|≤|p| := by
  by_cases hi : i=0
  · have he : sectorEnergy p i t-sectorEnergy 0 i t=p := by
      simp only [sectorEnergy, hi, ite_true]
      ring
    rw [he]
  · have he : sectorEnergy p i t-sectorEnergy 0 i t= -p/2 := by
      simp only [sectorEnergy, hi, ite_false]
      ring
    rw [he, abs_div, abs_neg]
    norm_num

end OperatorDerivativeRewrite.Foundation.CorridorOccupation
