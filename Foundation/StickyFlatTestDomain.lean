import Foundation.SmoothFlatC0Approximation
import Foundation.StickyGeneratorLinearGraph
import Mathlib.Analysis.Calculus.Deriv.Support

/-! A dense family of genuine sticky martingale tests. Density here is in C0,
and an explicit boundary-value gap prevents treating this family as a graph core. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology ZeroAtInfty
namespace OperatorDerivativeRewrite.Foundation.StickyFlatTestDomain
open SmoothFlatC0Approximation StickyGeneratorRelation StickyGeneratorLinearGraph
open StickyC2MartingaleProblem StickyBoundaryGeneratorCore
open InfiniteGaussian BrownianMassRandomTimeChange
set_option backward.isDefEq.respectTransparency false

theorem second_zero {F : C₀(ℝ, ℝ)} (hF : F ∈ flatSmooth) :
    deriv (deriv (F : ℝ → ℝ)) 0 = 0 := by
  obtain ⟨c,hc⟩ := hF.2.2
  calc
    _ = deriv (deriv (fun _ : ℝ => c)) 0 := hc.deriv.deriv_eq
    _ = 0 := by simp

def generator (F : C₀(ℝ, ℝ)) (hF : F ∈ flatSmooth) : C₀(ℝ, ℝ) where
  toFun := fun x => (1/2 : ℝ)*deriv (deriv (F : ℝ → ℝ)) x
  continuous_toFun := continuous_const.mul
    (GaussianC2Ito.second_continuous F (hF.1.of_le (by norm_num)))
  zero_at_infty' := hF.2.1.deriv.deriv.mul_left.is_zero_at_infty

theorem generator_zero {F : C₀(ℝ, ℝ)} (hF : F ∈ flatSmooth) :
    generator F hF 0 = 0 := by
  change (1/2 : ℝ)*deriv (deriv (F : ℝ → ℝ)) 0 = 0
  rw [second_zero hF,mul_zero]

theorem boundary_test_eq {F : C₀(ℝ, ℝ)} (hF : F ∈ flatSmooth) (κ : ℝ≥0) :
    boundaryTest F κ = (F : ℝ → ℝ) := by
  funext x
  simp only [boundaryTest,coefficient,second_zero hF,mul_zero,zero_mul,add_zero]

theorem admissible {F : C₀(ℝ, ℝ)} (hF : F ∈ flatSmooth) (κ : ℝ≥0) :
    Admissible κ F (generator F hF) := by
  exact of_boundary_test F (hF.1.of_le (by norm_num)) κ _ _ (boundary_test_eq hF κ).symm rfl

theorem domain_dense (κ : ℝ≥0) :
    Dense {F : C₀(ℝ, ℝ) | ∃ G, Admissible κ F G} := by
  apply flatSmooth_dense.mono
  intro F hF
  exact ⟨generator F hF,admissible hF κ⟩

theorem derivative_bounds {F : C₀(ℝ, ℝ)} (hF : F ∈ flatSmooth) :
    ∃ K0 K1 : ℝ≥0, (∀ x, ‖deriv (F : ℝ → ℝ) x‖₊ ≤ K0) ∧
      (∀ x, ‖deriv (deriv (F : ℝ → ℝ)) x‖₊ ≤ K1) := by
  let D : C₀(ℝ, ℝ) := {
    toFun := deriv (F : ℝ → ℝ)
    continuous_toFun := hF.1.continuous_deriv (by norm_num)
    zero_at_infty' := hF.2.1.deriv.is_zero_at_infty }
  let D2 : C₀(ℝ, ℝ) := {
    toFun := deriv (deriv (F : ℝ → ℝ))
    continuous_toFun := GaussianC2Ito.second_continuous F (hF.1.of_le (by norm_num))
    zero_at_infty' := hF.2.1.deriv.deriv.is_zero_at_infty }
  exact ⟨‖D‖₊,‖D2‖₊,fun x => D.toBCF.nnnorm_coe_le_nnnorm x,
    fun x => D2.toBCF.nnnorm_coe_le_nnnorm x⟩

theorem actual_martingale {F : C₀(ℝ, ℝ)} (hF : F ∈ flatSmooth) (κ : ℝ≥0) :
    Martingale (fun t ω => F (changedPath κ ω t)-F 0-
      ∫ s in 0..(t : ℝ), generator F hF (changedPath κ ω s.toNNReal))
      (augmentedPhysicalPast κ) gaussianProduct := by
  obtain ⟨K0,K1,h0,h1⟩ := derivative_bounds hF
  have hm := generator_martingale F (hF.1.of_le (by norm_num)) K0 K1 h0 h1 κ
  rw [boundary_test_eq hF κ] at hm
  exact hm

theorem graph_generator_gap {F : C₀(ℝ, ℝ)} (hF : F ∈ flatSmooth) (κ : ℝ≥0) :
    (1/4 : ℝ) ≤ ‖generator F hF-StickyVanishingGeneratorPair.generatorC0 κ‖ := by
  have hb := (generator F hF-StickyVanishingGeneratorPair.generatorC0 κ).toBCF.norm_coe_le_norm 0
  change ‖generator F hF 0-StickyVanishingGeneratorPair.generatorC0 κ 0‖ ≤
    ‖generator F hF-StickyVanishingGeneratorPair.generatorC0 κ‖ at hb
  simpa only [generator_zero hF,StickyVanishingGeneratorPair.generator_zero,
    zero_sub,norm_neg,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/4)] using hb

end OperatorDerivativeRewrite.Foundation.StickyFlatTestDomain
