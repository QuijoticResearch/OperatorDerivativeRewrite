import Foundation.HigherHeatLpStepControls
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! Density of actual step controls and uniqueness of the continuous signed marginal extension. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatLpControlExtension
open HigherHeatLpControls HigherHeatLpStepControls HigherHeatStepIntegralRealization

def steps (m : ℕ) [Fact (0 < m)] : Set (Control m) :=
  {u | ∃ (n : ℕ) (s : Fin n → Set ℝ) (hs : ∀ i, MeasurableSet (s i))
    (hf : ∀ i, volume (s i) ≠ ∞) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (c : Fin n → ℝ), control m s hs hf c = u}

theorem simple_representation (m : ℕ) [Fact (0 < m)] (f : SimpleFunc ℝ ℝ)
    (hfp : MemLp f (power m) volume) : hfp.toLp f ∈ steps m := by
  classical
  let I := ↥(f.range.erase 0)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let c : Fin (Fintype.card I) → ℝ := fun i => (e.symm i).val
  let s : Fin (Fintype.card I) → Set ℝ := fun i => f ⁻¹' {c i}
  have hc : Function.Injective c := Subtype.val_injective.comp e.symm.injective
  have hc0 (i : Fin (Fintype.card I)) : c i ≠ 0 :=
    (Finset.mem_erase.mp (e.symm i).property).1
  have hs (i : Fin (Fintype.card I)) : MeasurableSet (s i) := f.measurableSet_fiber _
  have hf (i : Fin (Fintype.card I)) : volume (s i) ≠ ∞ :=
    (SimpleFunc.measure_preimage_lt_top_of_memLp (power_ne_zero m) (power_ne_top m)
      f hfp (c i) (hc0 i)).ne
  have hd : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change f x = c i at hxi
    change f x = c j at hxj
    exact hij (hc (hxi.symm.trans hxj))
  have hr (x : ℝ) : raw s c x = f x := by
    by_cases hx : f x = 0
    · have hout (i : Fin (Fintype.card I)) : x ∉ s i := by
        intro hi
        change f x = c i at hi
        exact hc0 i (hi.symm.trans hx)
      simp only [raw]
      rw [Finset.sum_eq_zero (fun i _ => by simp [hout i]), hx]
    · let z : I := ⟨f x, Finset.mem_erase.mpr ⟨hx, f.mem_range_self x⟩⟩
      let j : Fin (Fintype.card I) := e z
      have hcj : c j = f x := by simp [c, j, z]
      have hj : x ∈ s j := hcj.symm
      unfold raw
      rw [Finset.sum_eq_single j]
      · rw [Set.indicator_of_mem hj, hcj]
      · intro i _ hij
        have hout : x ∉ s i := by
          intro hi
          change f x = c i at hi
          exact hij (hc (hi.symm.trans hcj.symm))
        simp [hout]
      · simp
  refine ⟨Fintype.card I, s, hs, hf, hd, c, ?_⟩
  apply Lp.ext
  filter_upwards [control_ae m s hs hf c, hfp.coeFn_toLp] with x hx hy
  rw [hx, hy, hr]

theorem steps_dense (m : ℕ) [Fact (0 < m)] : Dense (steps m) := by
  apply (Lp.simpleFunc.dense (E := ℝ) (μ := volume) (power_ne_top m)).mono
  intro u hu
  let v : Lp.simpleFunc ℝ (power m) (volume : Measure ℝ) := ⟨u, hu⟩
  let f := Lp.simpleFunc.toSimpleFunc v
  have hf := Lp.simpleFunc.memLp v
  have he : (hf.toLp f : Control m) = u := by
    have hh := congrArg (fun z : Lp.simpleFunc ℝ (power m) (volume : Measure ℝ) => (z : Control m))
      (Lp.simpleFunc.toLp_toSimpleFunc v)
    exact hh
  rw [← he]
  exact simple_representation m f hf

theorem fourier_continuous (m : ℕ) [Fact (0 < m)] (ξ : ℝ) :
    Continuous (fun u : Control m => ∫ᵛ y, HigherHeatCylinderFourier.phase ξ y ∂<•marginal m u) := by
  have he : (fun u : Control m => ∫ᵛ y, HigherHeatCylinderFourier.phase ξ y ∂<•marginal m u) =
      fun u => HigherHeatL2.symbol m (clock m u) ξ := funext (fun u => marginal_fourier m u ξ)
  rw [he]
  have hc : Continuous (fun T : ℝ≥0 => HigherHeatL2.symbol m T ξ) := by
    unfold HigherHeatL2.symbol
    fun_prop
  exact hc.comp (clock_continuous m)

theorem observable_continuous (m : ℕ) [Fact (0 < m)] (a : ℕ → ℝ)
    (q : HigherHeatFourierBanach.TestSpace FourierPathStopping.terminalLevels
      (FourierPathTerminalKernels.frequency a)) (x : ℝ) :
    Continuous (fun u : Control m => ∫ᵛ y, HigherHeatFourierBanach.realize
      FourierPathStopping.terminalLevels (FourierPathTerminalKernels.frequency a) q
        (FourierPathTerminalKernels.shiftedLine x y) ∂<•marginal m u) := by
  have he : (fun u : Control m => ∫ᵛ y, HigherHeatFourierBanach.realize
      FourierPathStopping.terminalLevels (FourierPathTerminalKernels.frequency a) q
        (FourierPathTerminalKernels.shiftedLine x y) ∂<•marginal m u) =
      fun u => HigherHeatFourierBanach.realize FourierPathStopping.terminalLevels
        (FourierPathTerminalKernels.frequency a)
        (HigherHeatFourierPathSemigroup.evolution FourierPathStopping.terminalLevels
          (FourierPathTerminalKernels.frequency a) m (Fact.out) (clock m u) q)
        (FourierPathTerminalKernels.line x) := by
    funext u
    exact (marginal_operator m a u q x).symm
  rw [he]
  exact HigherHeatLpControls.observable_continuous m a q x

theorem extension_unique (m : ℕ) [Fact (0 < m)] (Q : Control m → SignedMeasure ℝ)
    (hQ : ∀ ξ : ℝ, Continuous (fun u => ∫ᵛ y, HigherHeatCylinderFourier.phase ξ y ∂<•Q u))
    (hs : ∀ u ∈ steps m, Q u = marginal m u) (u : Control m) : Q u = marginal m u := by
  apply SignedHeatFourierUniqueness.ext
  intro ξ
  have he : Set.EqOn (fun v => ∫ᵛ y, HigherHeatCylinderFourier.phase ξ y ∂<•Q v)
      (fun v => ∫ᵛ y, HigherHeatCylinderFourier.phase ξ y ∂<•marginal m v) (steps m) := by
    intro v hv
    exact congrArg (fun ν : SignedMeasure ℝ =>
      ∫ᵛ y, HigherHeatCylinderFourier.phase ξ y ∂<•ν) (hs v hv)
  exact he.closure (hQ ξ) (fourier_continuous m ξ) (steps_dense m u)

end OperatorDerivativeRewrite.Foundation.HigherHeatLpControlExtension
