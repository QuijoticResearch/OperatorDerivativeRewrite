import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic

/-! Reassemble native conditional laws over a countable measurable partition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace OperatorDerivativeRewrite.Foundation.CountableConditionalIndependence
variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]

theorem total_probability (μ : Measure Ω) [IsFiniteMeasure μ] (c : Ω → ℕ) (hc : Measurable c) :
    Measure.sum (fun n => μ (c ⁻¹' {n}) • cond μ (c ⁻¹' {n})) = μ := by
  ext E hE
  rw [Measure.sum_apply _ hE]
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [mul_comm (μ _), cond_mul_eq_inter (hc (.singleton _))]
  have hd : Pairwise (fun i j : ℕ => Disjoint (c ⁻¹' {i} ∩ E) (c ⁻¹' {j} ∩ E)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro ω hi hj
    have hi' : c ω = i := by simpa only [mem_preimage, mem_singleton_iff] using hi.1
    have hj' : c ω = j := by simpa only [mem_preimage, mem_singleton_iff] using hj.1
    exact hij (hi'.symm.trans hj')
  have hu : (⋃ n : ℕ, c ⁻¹' {n} ∩ E) = E := by ext ω; simp
  rw [← measure_iUnion hd (fun n => (hc (.singleton n)).inter hE), hu]

theorem map_total (μ : Measure Ω) [IsFiniteMeasure μ] (c : Ω → ℕ) (hc : Measurable c)
    (f : Ω → A) (hf : Measurable f) :
    μ.map f = Measure.sum (fun n => μ (c ⁻¹' {n}) • (cond μ (c ⁻¹' {n})).map f) := by
  calc
    _ = (Measure.sum (fun n => μ (c ⁻¹' {n}) • cond μ (c ⁻¹' {n}))).map f := by
      rw [total_probability μ c hc]
    _ = _ := by
      rw [Measure.map_sum hf.aemeasurable]
      congr 1
      funext n
      exact Measure.map_smul _ hf.aemeasurable

theorem joint_law (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure B)
    [IsProbabilityMeasure ν] (c : Ω → ℕ) (hc : Measurable c) (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y)
    (hlaw : ∀ n, μ (c ⁻¹' {n}) ≠ 0 → (cond μ (c ⁻¹' {n})).map Y = ν)
    (hi : ∀ n, μ (c ⁻¹' {n}) ≠ 0 → IndepFun X Y (cond μ (c ⁻¹' {n}))) :
    μ.map (fun ω => (X ω,Y ω)) = (μ.map X).prod ν := by
  calc
    _ = Measure.sum (fun n => μ (c ⁻¹' {n}) •
        (cond μ (c ⁻¹' {n})).map (fun ω => (X ω,Y ω))) :=
      map_total μ c hc _ (hX.prodMk hY)
    _ = Measure.sum (fun n => (μ (c ⁻¹' {n}) • (cond μ (c ⁻¹' {n})).map X).prod ν) := by
      congr 1
      funext n
      by_cases hn : μ (c ⁻¹' {n}) = 0
      · simp only [hn, zero_smul, Measure.zero_prod]
      · have : IsProbabilityMeasure (cond μ (c ⁻¹' {n})) := cond_isProbabilityMeasure hn
        rw [(hi n hn).map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
          hlaw n hn, Measure.prod_smul_left]
    _ = (Measure.sum (fun n => μ (c ⁻¹' {n}) • (cond μ (c ⁻¹' {n})).map X)).prod ν :=
      (Measure.prod_sum_left _ ν).symm
    _ = _ := by rw [← map_total μ c hc X hX]

theorem future_law (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure B)
    [IsProbabilityMeasure ν] (c : Ω → ℕ) (hc : Measurable c) (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y)
    (hlaw : ∀ n, μ (c ⁻¹' {n}) ≠ 0 → (cond μ (c ⁻¹' {n})).map Y = ν)
    (hi : ∀ n, μ (c ⁻¹' {n}) ≠ 0 → IndepFun X Y (cond μ (c ⁻¹' {n}))) : μ.map Y = ν := by
  have he := congrArg (fun ρ : Measure (A × B) => ρ.map Prod.snd)
    (joint_law μ ν c hc X Y hX hY hlaw hi)
  rw [Measure.map_map measurable_snd (hX.prodMk hY), Measure.map_snd_prod,
    measure_univ, one_smul] at he
  exact he

theorem independent (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure B)
    [IsProbabilityMeasure ν] (c : Ω → ℕ) (hc : Measurable c) (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y)
    (hlaw : ∀ n, μ (c ⁻¹' {n}) ≠ 0 → (cond μ (c ⁻¹' {n})).map Y = ν)
    (hi : ∀ n, μ (c ⁻¹' {n}) ≠ 0 → IndepFun X Y (cond μ (c ⁻¹' {n}))) : IndepFun X Y μ := by
  apply (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mpr
  rw [future_law μ ν c hc X Y hX hY hlaw hi]
  exact joint_law μ ν c hc X Y hX hY hlaw hi

end OperatorDerivativeRewrite.Foundation.CountableConditionalIndependence
