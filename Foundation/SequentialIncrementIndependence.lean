import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Process.Adapted
import Mathlib.Data.Finset.Max

/-! A filtration criterion for genuine independent increments. The finite-family
product law is proved by maximal-index induction on actual measurable events. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace OperatorDerivativeRewrite.Foundation.SequentialIncrementIndependence
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem sequential {ι : Type*} [LinearOrder ι] (m : ι → MeasurableSpace Ω)
    (X : ι → Ω → ℝ) (hpast : ∀ i j, j < i → Measurable[m i] (X j))
    (hI : ∀ i, Indep (MeasurableSpace.comap (X i) inferInstance) (m i) μ) :
    iIndepFun X μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro sets hm; simp
  | insert a S hmax ih =>
    intro sets hm
    have ha : a ∉ S := fun h => (lt_irrefl a) (hmax a h)
    have hmS : ∀ i ∈ S, MeasurableSet (sets i) :=
      fun i hi => hm i (Finset.mem_insert_of_mem hi)
    have hA : MeasurableSet[m a] (⋂ i ∈ S, X i ⁻¹' sets i) :=
      MeasurableSet.biInter S.finite_toSet.countable
        (fun i hi => (hpast a i (hmax i hi)) (hmS i hi))
    calc
      μ (⋂ i ∈ insert a S, X i ⁻¹' sets i) =
          μ ((X a ⁻¹' sets a) ∩ ⋂ i ∈ S, X i ⁻¹' sets i) := by congr 1; simp
      _ = μ (X a ⁻¹' sets a)*μ (⋂ i ∈ S, X i ⁻¹' sets i) :=
        ((hI a).indepSet_of_measurableSet
          ⟨sets a,hm a (Finset.mem_insert_self a S),rfl⟩ hA).measure_inter_eq_mul
      _ = μ (X a ⁻¹' sets a)*(∏ i ∈ S, μ (X i ⁻¹' sets i)) := by rw [ih hmS]
      _ = _ := by rw [Finset.prod_insert ha]

theorem of_filtration {T : Type*} [LinearOrder T] (ℱ : Filtration T m₀)
    (X : T → Ω → ℝ) (hX : ∀ t, Measurable[ℱ t] (X t))
    (hI : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω-X s ω) inferInstance) (ℱ s) μ) :
    HasIndepIncrements X μ := by
  intro n t ht
  apply sequential μ (fun i : Fin n => ℱ (t i.castSucc))
    (fun i ω => X (t i.succ) ω-X (t i.castSucc) ω)
  · intro i j hji
    have hj : j.succ ≤ i.castSucc := by
      change j.val+1 ≤ i.val
      exact Nat.succ_le_of_lt hji
    have hj' : j.castSucc ≤ i.castSucc := by
      change j.val ≤ i.val
      exact hji.le
    exact ((hX _).mono (ℱ.mono (ht hj)) le_rfl).sub
      ((hX _).mono (ℱ.mono (ht hj')) le_rfl)
  · intro i
    exact hI _ _ (ht (Fin.castSucc_le_succ i))

end OperatorDerivativeRewrite.Foundation.SequentialIncrementIndependence
