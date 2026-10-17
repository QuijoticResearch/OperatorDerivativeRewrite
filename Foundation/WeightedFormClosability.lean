import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Tactic.FieldSimp

/-! Weighted derivative energy is closable under an explicit closable-operator hypothesis. -/
noncomputable section
open Filter
namespace OperatorDerivativeRewrite.Foundation.WeightedFormClosability
set_option backward.isDefEq.respectTransparency false
variable {V X Y : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def SeqClosable (I : V →ₗ[ℝ] X) (D : V →ₗ[ℝ] Y) : Prop :=
  ∀ f : ℕ → V, Tendsto (fun n => I (f n)) atTop (nhds 0) →
    ∀ y : Y, Tendsto (fun n => D (f n)) atTop (nhds y) → y = 0

def energy (κ : ℝ) (D : V →ₗ[ℝ] Y) (v : V) : ℝ := κ * ‖D v‖^2

def FormClosable (κ : ℝ) (I : V →ₗ[ℝ] X) (D : V →ₗ[ℝ] Y) : Prop :=
  ∀ f : ℕ → V, Tendsto (fun n => I (f n)) atTop (nhds 0) →
    Tendsto (fun q : ℕ × ℕ => energy κ D (f q.1 - f q.2)) atTop (nhds 0) →
    Tendsto (fun n => energy κ D (f n)) atTop (nhds 0)

theorem null_input_zero_derivative {I : V →ₗ[ℝ] X} {D : V →ₗ[ℝ] Y}
    (h : SeqClosable I D) (v : V) (hv : I v = 0) : D v = 0 := by
  apply h (fun _ => v) _ (D v) tendsto_const_nhds
  simpa only [hv] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : X)) atTop (nhds 0))

theorem equal_input_equal_derivative {I : V →ₗ[ℝ] X} {D : V →ₗ[ℝ] Y}
    (h : SeqClosable I D) (v w : V) (hv : I v = I w) : D v = D w := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply null_input_zero_derivative h
  rw [map_sub, hv, sub_self]

theorem energy_tendsto (κ : ℝ) (D : V →ₗ[ℝ] Y) (f : ℕ → V) {y : Y}
    (hf : Tendsto (fun n => D (f n)) atTop (nhds y)) :
    Tendsto (fun n => energy κ D (f n)) atTop (nhds (κ * ‖y‖^2)) :=
  tendsto_const_nhds.mul (hf.norm.pow 2)

theorem energy_cauchy_iff (κ : ℝ) (hκ : 0 < κ) (D : V →ₗ[ℝ] Y) (f : ℕ → V) :
    Tendsto (fun q : ℕ × ℕ => energy κ D (f q.1 - f q.2)) atTop (nhds 0) ↔
      CauchySeq (fun n => D (f n)) := by
  constructor
  · intro he
    apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (he.div_const κ)
    have hval (q : ℕ × ℕ) : Real.sqrt (energy κ D (f q.1 - f q.2) / κ) =
        dist (D (f q.1)) (D (f q.2)) := by
      have hc : energy κ D (f q.1 - f q.2) / κ = ‖D (f q.1 - f q.2)‖^2 := by
        unfold energy
        field_simp [ne_of_gt hκ]
      rw [hc, Real.sqrt_sq (norm_nonneg _), map_sub, ← dist_eq_norm]
    simpa only [Function.comp_def, hval, zero_div, Real.sqrt_zero] using hs
  · intro hc
    have hd := cauchySeq_iff_tendsto_dist_atTop_0.mp hc
    have he : Tendsto (fun q : ℕ × ℕ => κ * dist (D (f q.1)) (D (f q.2))^2)
        atTop (nhds (κ * (0 : ℝ)^2)) := tendsto_const_nhds.mul (hd.pow 2)
    simpa [energy, dist_eq_norm] using he

theorem zero_coefficient (I : V →ₗ[ℝ] X) (D : V →ₗ[ℝ] Y) : FormClosable 0 I D := by
  intro f _ _
  simpa only [energy, zero_mul] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

theorem seqClosable_implies_form [CompleteSpace Y] {I : V →ₗ[ℝ] X} {D : V →ₗ[ℝ] Y}
    (h : SeqClosable I D) (κ : ℝ) (hκ : 0 < κ) : FormClosable κ I D := by
  intro f hf hE
  have hc := (energy_cauchy_iff κ hκ D f).mp hE
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete hc
  have hz := h f hf y hy
  have he := energy_tendsto κ D f hy
  simpa [hz] using he

theorem form_implies_seqClosable {I : V →ₗ[ℝ] X} {D : V →ₗ[ℝ] Y}
    (κ : ℝ) (hκ : 0 < κ) (h : FormClosable κ I D) : SeqClosable I D := by
  intro f hf y hy
  have hc := (energy_cauchy_iff κ hκ D f).mpr hy.cauchySeq
  have he := h f hf hc
  have hv := energy_tendsto κ D f hy
  have hz : κ * ‖y‖^2 = 0 := tendsto_nhds_unique hv he
  have hn : ‖y‖^2 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hκ)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem positive_form_iff_seqClosable [CompleteSpace Y]
    (κ : ℝ) (hκ : 0 < κ) (I : V →ₗ[ℝ] X) (D : V →ₗ[ℝ] Y) :
    FormClosable κ I D ↔ SeqClosable I D :=
  ⟨form_implies_seqClosable κ hκ, fun h => seqClosable_implies_form h κ hκ⟩

theorem seqClosable_implies_nonnegative_form [CompleteSpace Y]
    {I : V →ₗ[ℝ] X} {D : V →ₗ[ℝ] Y} (h : SeqClosable I D)
    (κ : ℝ) (hκ : 0 ≤ κ) : FormClosable κ I D := by
  by_cases hz : κ = 0
  · rw [hz]
    exact zero_coefficient I D
  · exact seqClosable_implies_form h κ (lt_of_le_of_ne hκ (Ne.symm hz))

theorem operator_seqClosable {T : X →ₗ.[ℝ] Y} (hT : T.IsClosable) :
    SeqClosable T.domain.subtype T.toFun := by
  intro f hf y hy
  have hp : Tendsto (fun n => ((f n : X), T (f n))) atTop (nhds (0,y)) :=
    hf.prodMk_nhds hy
  have hx : (0,y) ∈ T.graph.topologicalClosure :=
    mem_closure_of_tendsto hp (Eventually.of_forall (fun n => T.mem_graph (f n)))
  rw [hT.graph_closure_eq_closure_graph] at hx
  exact T.closure.graph_fst_eq_zero_snd hx rfl

theorem operator_formClosable [CompleteSpace Y] {T : X →ₗ.[ℝ] Y}
    (hT : T.IsClosable) (κ : ℝ) (hκ : 0 ≤ κ) :
    FormClosable κ T.domain.subtype T.toFun :=
  seqClosable_implies_nonnegative_form (operator_seqClosable hT) κ hκ

end OperatorDerivativeRewrite.Foundation.WeightedFormClosability
