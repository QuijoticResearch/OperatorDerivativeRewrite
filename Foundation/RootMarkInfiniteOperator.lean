import Foundation.RootMarkFiniteEnergyLimit
import Foundation.RootMarkInfiniteIto
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Actual infinite integration is linear on the space of finite-energy predictable coefficients. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RootMarkInfiniteOperator
open RootMarkStochasticIntegral RootMarkL2Integral RootMarkFiniteEnergyLimit
open RootMarkConditionalEnergy
open MarkedRootRenewalProcess (MarkSample marks)

theorem energy_summable_of_converges (a : ℝ) (H : Fin 3 → Coefficients) (Y : Lp ℂ 2 marks)
    (hY : Tendsto (fun n : ℕ => integralL2 a H n) atTop (𝓝 Y)) :
    Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks) := by
  obtain ⟨C,hC⟩ := ((hY.norm.pow 2).cauchySeq.isBounded_range).exists_norm_le
  apply summable_of_sum_range_le (c := C)
    (fun j => integral_nonneg (RootMarkIntegralUniqueness.energy_nonneg a H j))
  intro n
  rw [← integralL2_norm_square]
  have hn := hC (‖integralL2 a H n‖^2) ⟨n,rfl⟩
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖integralL2 a H n‖)] using hn

theorem finite_energy_add (a : ℝ) (H K : Fin 3 → Coefficients)
    (hH : Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks))
    (hK : Summable (fun j : ℕ => ∫ η, energy a K j η ∂marks)) :
    Summable (fun j : ℕ => ∫ η, energy a (H+K) j η ∂marks) := by
  apply energy_summable_of_converges a (H+K)
    (stochasticLimit a H hH+stochasticLimit a K hK)
  have he (n : ℕ) : integralL2 a (H+K) n = integralL2 a H n+integralL2 a K n :=
    (integralOperator a n).map_add H K
  simpa only [he] using (stochasticLimit_tendsto a H hH).add (stochasticLimit_tendsto a K hK)

theorem finite_energy_smul (a : ℝ) (c : ℂ) (H : Fin 3 → Coefficients)
    (hH : Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks)) :
    Summable (fun j : ℕ => ∫ η, energy a (c • H) j η ∂marks) := by
  apply energy_summable_of_converges a (c • H) (c • stochasticLimit a H hH)
  have he (n : ℕ) : integralL2 a (c • H) n = c • integralL2 a H n :=
    (integralOperator a n).map_smul c H
  simpa only [he] using (stochasticLimit_tendsto a H hH).const_smul c

def integrands (a : ℝ) : Submodule ℂ (Fin 3 → Coefficients) where
  carrier := {H | Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks)}
  zero_mem' := by simp [energy]
  add_mem' := fun hH hK => finite_energy_add a _ _ hH hK
  smul_mem' := finite_energy_smul a

def integration (a : ℝ) : integrands a →ₗ[ℂ] Lp ℂ 2 marks where
  toFun H := stochasticLimit a H H.property
  map_add' H K := by
    have ht := (stochasticLimit_tendsto a H H.property).add
      (stochasticLimit_tendsto a K K.property)
    have he (n : ℕ) : integralL2 a (H+K) n = integralL2 a H n+integralL2 a K n :=
      (integralOperator a n).map_add H K
    exact tendsto_nhds_unique (stochasticLimit_tendsto a (H+K) (H+K).property)
      (by simpa only [he, RingHom.id_apply] using ht)
  map_smul' c H := by
    have ht := (stochasticLimit_tendsto a H H.property).const_smul c
    have he (n : ℕ) : integralL2 a (c • H) n = c • integralL2 a H n :=
      (integralOperator a n).map_smul c H
    exact tendsto_nhds_unique (stochasticLimit_tendsto a (c • H) (c • H).property)
      (by simpa only [he, RingHom.id_apply] using ht)

theorem integration_isometry (a : ℝ) (H : integrands a) :
    ‖integration a H‖^2 = ∑' j : ℕ, ∫ η, energy a H j η ∂marks :=
  stochasticLimit_isometry a H H.property

theorem integration_mean_zero (a : ℝ) (H : integrands a) :
    (∫ η, integration a H η ∂marks) = 0 := stochasticLimit_mean_zero a H H.property

theorem integration_surjective_centered (a : ℝ) (ha : a ≠ 0) (Y : Lp ℂ 2 marks)
    (hmean : (∫ η, Y η ∂marks) = 0) : ∃ H : integrands a, integration a H = Y := by
  obtain ⟨H,_,ht,hE⟩ := RootMarkInfiniteIto.infinite_clark_isometry a ha Y hmean
  refine ⟨⟨H,hE.summable⟩,?_⟩
  exact tendsto_nhds_unique (stochasticLimit_tendsto a H hE.summable) ht

end OperatorDerivativeRewrite.Foundation.RootMarkInfiniteOperator
