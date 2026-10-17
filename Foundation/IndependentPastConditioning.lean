import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability

/-! Conditioning on an event in the past preserves an independent future
sigma-algebra and its independence from that past, with actual probability laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace OperatorDerivativeRewrite.Foundation.IndependentPastConditioning
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω)
  [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem event_probability (h₁ : m₁ ≤ m₀) (hI : Indep m₁ m₂ μ)
    (A : Set Ω) (hA : MeasurableSet[m₂] A) (hμA : μ A ≠ 0)
    (S : Set Ω) (hS : MeasurableSet[m₁] S) : μ[|A] S = μ S := by
  rw [cond_apply' (h₁ S hS),
    (hI.symm.indepSet_of_measurableSet hA hS).measure_inter_eq_mul,
    ← mul_assoc,ENNReal.inv_mul_cancel hμA (measure_ne_top μ A),one_mul]

theorem independence (h₁ : m₁ ≤ m₀) (h₂ : m₂ ≤ m₀) (hI : Indep m₁ m₂ μ)
    (A : Set Ω) (hA : MeasurableSet[m₂] A) (hμA : μ A ≠ 0) :
    Indep m₁ m₂ μ[|A] := by
  letI : IsProbabilityMeasure μ[|A] := cond_isProbabilityMeasure hμA
  apply (indep_iff_forall_indepSet μ[|A]).mpr
  intro S T hS hT
  apply (indepSet_iff_measure_inter_eq_mul (h₁ S hS) (h₂ T hT) μ[|A]).mpr
  rw [event_probability m₁ m₂ μ h₁ hI A hA hμA S hS,
    cond_apply' ((h₁ S hS).inter (h₂ T hT)),cond_apply' (h₂ T hT)]
  rw [Set.inter_left_comm,
    (hI.indepSet_of_measurableSet hS (hA.inter hT)).measure_inter_eq_mul]
  ring

theorem map_law {E : Type*} [MeasurableSpace E] (X : Ω → E)
    (hX : Measurable[m₁] X) (h₁ : m₁ ≤ m₀) (hI : Indep m₁ m₂ μ)
    (A : Set Ω) (hA : MeasurableSet[m₂] A) (hμA : μ A ≠ 0) :
    μ[|A].map X = μ.map X := by
  ext B hB
  rw [Measure.map_apply (hX.mono h₁ le_rfl) hB,Measure.map_apply (hX.mono h₁ le_rfl) hB]
  exact event_probability m₁ m₂ μ h₁ hI A hA hμA _ (hX hB)

end OperatorDerivativeRewrite.Foundation.IndependentPastConditioning


/-! Conditioning on a measurable past event preserves an independent future source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.IndependentPastConditioning
variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]

theorem cond_congr (μ : Measure Ω) {E F : Set Ω} (h : E =ᵐ[μ] F) :
    cond μ E = cond μ F := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, measure_congr h, Measure.restrict_congr_set h]

theorem restricted_joint {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → A} {Y : Ω → B}
    (hX : Measurable X) (hY : Measurable Y) (hi : IndepFun X Y μ)
    (E : Set A) (hE : MeasurableSet E) :
    (μ.restrict (X ⁻¹' E)).map (fun ω => (X ω,Y ω)) =
      ((μ.map X).restrict E).prod (μ.map Y) := by
  have he : (fun ω => (X ω,Y ω)) ⁻¹' (E ×ˢ univ) = X ⁻¹' E := by
    ext ω
    simp only [mem_preimage, mem_prod, mem_univ, and_true]
  rw [Measure.restrict_prod_eq_prod_univ,
    ← hi.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    Measure.restrict_map (hX.prodMk hY) (hE.prod MeasurableSet.univ), he]

theorem conditional_joint {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → A} {Y : Ω → B}
    (hX : Measurable X) (hY : Measurable Y) (hi : IndepFun X Y μ)
    (E : Set A) (hE : MeasurableSet E) :
    (cond μ (X ⁻¹' E)).map (fun ω => (X ω,Y ω)) =
      (cond (μ.map X) E).prod (μ.map Y) := by
  rw [ProbabilityTheory.cond, Measure.map_smul _ (hX.prodMk hY).aemeasurable,
    restricted_joint hX hY hi E hE, ProbabilityTheory.cond,
    Measure.prod_smul_left, Measure.map_apply hX hE]

theorem future_law {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → A} {Y : Ω → B}
    (hX : Measurable X) (hY : Measurable Y) (hi : IndepFun X Y μ)
    (E : Set A) (hE : MeasurableSet E) (hp : μ (X ⁻¹' E) ≠ 0) :
    (cond μ (X ⁻¹' E)).map Y = μ.map Y := by
  have hn : (μ.map X) E ≠ 0 := by rwa [Measure.map_apply hX hE]
  have : IsProbabilityMeasure (cond (μ.map X) E) := cond_isProbabilityMeasure hn
  have he := congrArg (fun ν : Measure (A × B) => ν.map Prod.snd)
    (conditional_joint hX hY hi E hE)
  rw [Measure.map_map measurable_snd (hX.prodMk hY), Measure.map_snd_prod,
    measure_univ, one_smul] at he
  exact he

theorem conditional_independent {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    (hi : IndepFun X Y μ) (E : Set A) (hE : MeasurableSet E) (hp : μ (X ⁻¹' E) ≠ 0) :
    IndepFun X Y (cond μ (X ⁻¹' E)) := by
  have : IsProbabilityMeasure (cond μ (X ⁻¹' E)) := cond_isProbabilityMeasure hp
  have hx : (cond μ (X ⁻¹' E)).map X = cond (μ.map X) E := by
    have he := congrArg (fun ν : Measure (A × B) => ν.map Prod.fst)
      (conditional_joint hX hY hi E hE)
    rw [Measure.map_map measurable_fst (hX.prodMk hY), Measure.map_fst_prod,
      measure_univ, one_smul] at he
    exact he
  apply (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mpr
  rw [hx, future_law hX hY hi E hE hp]
  exact conditional_joint hX hY hi E hE

end OperatorDerivativeRewrite.Foundation.IndependentPastConditioning
