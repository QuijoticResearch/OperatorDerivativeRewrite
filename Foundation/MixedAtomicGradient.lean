import Foundation.ShrinkingSmoothJet
import Foundation.FiniteMeasureL2Dominated
import Foundation.GaussianCore
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Regular

/-! A regular full-support probability law with an atom and a nonclosable smooth derivative. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ContDiff Topology
namespace OperatorDerivativeRewrite.Foundation.MixedAtomicGradient
open SmoothAtomicJet ShrinkingSmoothJet
set_option backward.isDefEq.respectTransparency false

def μ : Measure ℝ := (1/2 : ℝ≥0∞) • GaussianCore.γ + (1/2 : ℝ≥0∞) • Measure.dirac 0

instance μ_probability : IsProbabilityMeasure μ where
  measure_univ := by
    norm_num [μ, Measure.add_apply, Measure.smul_apply]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

instance μ_regular : μ.Regular := by infer_instance

theorem μ_atom : μ {0} = (1/2 : ℝ≥0∞) := by
  have hg : GaussianCore.γ {0} = 0 :=
    (ProbabilityTheory.gaussianReal_absolutelyContinuous 0 (by norm_num)) (by simp)
  norm_num [μ, Measure.add_apply, Measure.smul_apply, hg]

instance μ_openPos : μ.IsOpenPosMeasure := by
  have : GaussianCore.γ.IsOpenPosMeasure :=
    (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)).isOpenPosMeasure
  have : Measure.IsOpenPosMeasure ((1/2 : ℝ≥0∞) • GaussianCore.γ) :=
    Measure.isOpenPosMeasure_smul _ (by norm_num)
  have h : (1/2 : ℝ≥0∞) • GaussianCore.γ ≤ μ := by
    unfold μ
    exact Measure.le_add_right le_rfl
  exact h.isOpenPosMeasure

theorem continuous_representation_unique {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[μ] g) : f = g := by
  change (∀ᵐ x ∂μ, f x = g x) at h
  rw [μ, ae_add_measure_iff] at h
  have hγ : f =ᵐ[GaussianCore.γ] g :=
    (Measure.ae_ennreal_smul_measure_iff (by norm_num)).mp h.1
  exact GaussianCore.continuous_representation_unique hf hg hγ

def coreSpace : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport]⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro r f hf
    exact ⟨contDiff_const.smul hf.1, hf.2.mul_left⟩

abbrev Core := coreSpace

theorem core_memLp (f : Core) (p : ℝ≥0∞) : MemLp f.val p μ :=
  f.property.1.continuous.memLp_of_hasCompactSupport f.property.2

theorem derivative_memLp (f : Core) (p : ℝ≥0∞) : MemLp (deriv f.val) p μ :=
  (f.property.1.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport f.property.2.deriv

def input (f : Core) : Lp ℝ 2 μ := (core_memLp f 2).toLp f.val

def output (f : Core) : Lp ℝ 2 μ := (derivative_memLp f 2).toLp (deriv f.val)

theorem input_injective : Function.Injective input := by
  intro f g h
  apply Subtype.ext
  apply continuous_representation_unique f.property.1.continuous g.property.1.continuous
  exact (MemLp.toLp_eq_toLp_iff _ _).mp h

def rangeDerivative (u : Set.range input) : Lp ℝ 2 μ := output (Classical.choose u.property)

theorem rangeDerivative_spec (u : Set.range input) (f : Core) (hf : input f = u.val) :
    rangeDerivative u = output f := by
  unfold rangeDerivative
  congr 1
  apply input_injective
  exact (Classical.choose_spec u.property).trans hf.symm

def jetCore (n : ℕ) : Core := ⟨jet n, jet_smooth n, jet_compact n⟩

def zeroCore : Core := ⟨0,contDiff_const,by simp [HasCompactSupport]⟩

theorem input_zero : input zeroCore = 0 := MemLp.toLp_zero _

theorem output_zero : output zeroCore = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [MemLp.coeFn_toLp (derivative_memLp zeroCore 2)] with x hx
  change (derivative_memLp zeroCore 2).toLp (deriv zeroCore.val) x = 0
  rw [hx]
  simp [zeroCore]

theorem atom_measurable : Measurable atom := by
  unfold atom
  exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const

theorem atom_bound (x : ℝ) : ‖atom x‖ ≤ 1 := by
  by_cases hx : x = 0 <;> simp [atom,hx]

theorem atom_memLp (p : ℝ≥0∞) : MemLp atom p μ :=
  MemLp.of_bound atom_measurable.aestronglyMeasurable 1 (Eventually.of_forall atom_bound)

def atomClass : Lp ℝ 2 μ := (atom_memLp 2).toLp atom

theorem atomClass_nonzero : atomClass ≠ 0 := by
  intro hz
  have hc : atomClass =ᵐ[μ] 0 := Lp.eq_zero_iff_ae_eq_zero.mp hz
  have h : atom =ᵐ[μ] 0 := (MemLp.coeFn_toLp (atom_memLp 2)).symm.trans hc
  have hs : {x : ℝ | atom x ≠ 0} = {0} := by
    ext x
    by_cases hx : x = 0 <;> simp [atom,hx]
  have hm : μ {x : ℝ | atom x ≠ 0} = 0 := by
    simpa only [Filter.EventuallyEq, ae_iff, Pi.zero_apply] using h
  rw [hs, μ_atom] at hm
  norm_num at hm

theorem input_jets_tendsto_zero : Tendsto (fun n => input (jetCore n)) atTop (nhds 0) := by
  obtain ⟨C,hC,hbound⟩ := uniform_bounds
  have h0 : (core_memLp zeroCore 2).toLp (fun _ => (0 : ℝ)) = 0 := MemLp.toLp_zero _
  have h := FiniteMeasureL2Dominated.toLp_tendsto_of_constant_bound
    (jet) (fun _ => (0 : ℝ)) (fun n => core_memLp (jetCore n) 2) (core_memLp zeroCore 2)
    C (le_trans (by norm_num) hC)
    (fun n => Eventually.of_forall (fun x => (hbound n x).1))
    (Eventually.of_forall (fun _ => by simpa using (le_trans (by norm_num) hC : (0 : ℝ) ≤ C)))
    (Eventually.of_forall jet_tendsto_zero)
  simpa only [input, jetCore, h0] using h

theorem output_jets_tendsto_atom :
    Tendsto (fun n => output (jetCore n)) atTop (nhds atomClass) := by
  obtain ⟨C,hC,hbound⟩ := uniform_bounds
  have h := FiniteMeasureL2Dominated.toLp_tendsto_of_constant_bound
    (fun n => deriv (jet n)) atom (fun n => derivative_memLp (jetCore n) 2) (atom_memLp 2)
    C (le_trans (by norm_num) hC)
    (fun n => Eventually.of_forall (fun x => (hbound n x).2))
    (Eventually.of_forall (fun x => (atom_bound x).trans hC))
    (Eventually.of_forall derivative_tendsto_atom)
  exact h

end OperatorDerivativeRewrite.Foundation.MixedAtomicGradient
