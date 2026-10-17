import Foundation.HigherHeatFourierInnovations

/-! Exact finite-grid Fourier martingale representation on actual signed cylindrical laws. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierCalculus
open HigherHeatL2 HigherHeatCylinderFourier HigherHeatBackwardFourier
open HigherHeatFourierInnovations HigherHeatSignedLaws

def gain (m : ℕ) (T s t : ℝ≥0) (ξ x z : ℝ) : ℂ :=
  symbol m (T-t) ξ*phase ξ x*innovation m (t-s) ξ z

theorem gain_eq_backward_difference (m : ℕ) (T s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ T)
    (ξ x y : ℝ) :
    gain m T s t ξ x (y-x)=backwardCharacter m T t ξ y-backwardCharacter m T s ξ x := by
  simpa only [gain,add_sub_cancel] using (backward_gain_factor m T s t hst ht ξ x (y-x)).symm

def fourierIntegral (m : ℕ) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (ξ : ℝ) (x : ℕ → ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, gain m T (grid j) (grid (j+1)) ξ (x j) (x (j+1)-x j)

theorem integral_eq_backward_difference (m : ℕ) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (hgrid : Monotone grid) (hT : grid n ≤ T) (ξ : ℝ) (x : ℕ → ℝ) :
    fourierIntegral m T grid n ξ x=
      backwardCharacter m T (grid n) ξ (x n)-backwardCharacter m T (grid 0) ξ (x 0) := by
  unfold fourierIntegral
  calc
    _ = ∑ j ∈ Finset.range n,
        (backwardCharacter m T (grid (j+1)) ξ (x (j+1))-
          backwardCharacter m T (grid j) ξ (x j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact gain_eq_backward_difference m T (grid j) (grid (j+1))
        (hgrid (by omega)) ((hgrid (by have := Finset.mem_range.mp hj; omega)).trans hT) ξ (x j) (x (j+1))
    _ = _ := Finset.sum_range_sub (fun j => backwardCharacter m T (grid j) ξ (x j)) n

theorem terminal_representation (m : ℕ) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (hgrid : Monotone grid) (h0 : grid 0=0) (hn : grid n=T) (ξ : ℝ)
    (x : ℕ → ℝ) (hx : x 0=0) :
    phase ξ (x n)-symbol m T ξ=fourierIntegral m T grid n ξ x := by
  rw [integral_eq_backward_difference m T grid n hgrid hn.le,hn,h0,hx,
    backward_terminal,backward_initial]

theorem continuous_path_representation (m : ℕ) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (hgrid : Monotone grid) (h0 : grid 0=0) (hn : grid n=T) (ξ : ℝ)
    (ω : C(ℝ≥0,ℝ)) (hω : ω 0=0) :
    phase ξ (ω T)-symbol m T ξ=fourierIntegral m T grid n ξ (fun j => ω (grid j)) := by
  simpa only [hn] using terminal_representation m T grid n hgrid h0 hn ξ
    (fun j => ω (grid j)) (by simpa only [h0] using hω)

theorem partition_independence (m : ℕ) (T : ℝ≥0)
    (grid grid' : ℕ → ℝ≥0) (n n' : ℕ) (hg : Monotone grid) (hg' : Monotone grid')
    (h0 : grid 0=0) (h0' : grid' 0=0) (hn : grid n=T) (hn' : grid' n'=T)
    (ξ : ℝ) (ω : C(ℝ≥0,ℝ)) (hω : ω 0=0) :
    fourierIntegral m T grid n ξ (fun j => ω (grid j))=
      fourierIntegral m T grid' n' ξ (fun j => ω (grid' j)) := by
  rw [← continuous_path_representation m T grid n hg h0 hn ξ ω hω,
    ← continuous_path_representation m T grid' n' hg' h0' hn' ξ ω hω]

theorem fourier_test_representation {ι : Type*} [Fintype ι] (m : ℕ) (T : ℝ≥0)
    (grid : ℕ → ℝ≥0) (n : ℕ) (hg : Monotone grid) (h0 : grid 0=0) (hn : grid n=T)
    (a : ι → ℂ) (ξ : ι → ℝ) (x : ℕ → ℝ) (hx : x 0=0) :
    fourierTest a ξ (x n)-(∑ i, a i*symbol m T (ξ i))=
      ∑ i, a i*fourierIntegral m T grid n (ξ i) x := by
  simp only [← terminal_representation m T grid n hg h0 hn _ x hx,mul_sub,
    Finset.sum_sub_distrib,fourierTest]

theorem predictable_coefficient_bound (m : ℕ) (T t : ℝ≥0) (ξ x : ℝ) :
    ‖symbol m (T-t) ξ*phase ξ x‖ ≤ 1 := by
  rw [norm_mul,phase_norm,mul_one]
  exact symbol_norm_le m (T-t) ξ

theorem actual_past_gain_zero {ι : Type*} [Fintype ι] (m : ℕ) (hm : 0 < m)
    (times : ι → ℝ≥0) (htimes : ∀ i, 0 < times i) (T s t : ℝ≥0) (hst : s < t) (ξ : ℝ) :
    (∫ᵛ w, gain m T s t ξ (∑ i, w.1 i) w.2
      ∂<•extendedLaw (Measure.pi (fun _ : ι => volume))
        (incrementDensity m hm times htimes) m hm (t-s) (tsub_pos_iff_lt.mpr hst))=0 := by
  exact HigherHeatFourierInnovations.actual_past_gain_zero m hm times htimes (t-s)
    (tsub_pos_iff_lt.mpr hst) ξ (fun w => symbol m (T-t) ξ*phase ξ (∑ i, w i))
    (by unfold phase; fun_prop) 1 (fun w => predictable_coefficient_bound m T t ξ _)

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierCalculus
