import Foundation.WeightedFormClosability

/-! A finite-window projection criterion for closability,
with explicit compatibility assumptions. -/
noncomputable section
open Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ProjectedFormClosability
open WeightedFormClosability
set_option backward.isDefEq.respectTransparency false

variable {V X Y ι : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem projected_cauchy (D : V →ₗ[ℝ] Y) (P : V →ₗ[ℝ] V)
    (hP : ∀ v, ‖D (P v)‖ ≤ ‖D v‖) (f : ℕ → V)
    (hf : CauchySeq (fun n => D (f n))) :
    CauchySeq (fun n => D (P (f n))) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hf ε hε
  refine ⟨N,fun m hm n hn => lt_of_le_of_lt ?_ (hN m hm n hn)⟩
  simpa only [dist_eq_norm, map_sub] using hP (f m - f n)

theorem projected_derivatives_tendsto_zero [CompleteSpace Y]
    (I : V →ₗ[ℝ] X) (D : V →ₗ[ℝ] Y)
    (P : V →ₗ[ℝ] V) (Q : X →L[ℝ] X)
    (hcompat : ∀ v, I (P v) = Q (I v))
    (hcontract : ∀ v, ‖D (P v)‖ ≤ ‖D v‖)
    (hlocal : SeqClosable (I.comp P) (D.comp P))
    (f : ℕ → V) (hf : Tendsto (fun n => I (f n)) atTop (𝓝 0))
    (hc : CauchySeq (fun n => D (f n))) :
    Tendsto (fun n => D (P (f n))) atTop (𝓝 0) := by
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete (projected_cauchy D P hcontract f hc)
  have hinput : Tendsto (fun n => (I.comp P) (f n)) atTop (𝓝 0) := by
    have h := (Q.continuous.tendsto 0).comp hf
    simpa only [Function.comp_def, LinearMap.comp_apply, hcompat, map_zero] using h
  have hzero : z = 0 := hlocal f hinput z hz
  simpa only [hzero] using hz

/-- Every core element is fixed by some window; each window is input-continuous,
energy-contracting and locally closable. No ordering or limiting family of windows is needed. -/
theorem seqClosable_of_covering_projections [CompleteSpace Y]
    (I : V →ₗ[ℝ] X) (D : V →ₗ[ℝ] Y)
    (P : ι → V →ₗ[ℝ] V) (Q : ι → X →L[ℝ] X)
    (hcompat : ∀ i v, I (P i v) = Q i (I v))
    (hcontract : ∀ i v, ‖D (P i v)‖ ≤ ‖D v‖)
    (hcover : ∀ v, ∃ i, P i v = v)
    (hlocal : ∀ i, SeqClosable (I.comp (P i)) (D.comp (P i))) :
    SeqClosable I D := by
  intro f hf y hy
  have hp (i : ι) : Tendsto (fun n => D (P i (f n))) atTop (𝓝 0) :=
    projected_derivatives_tendsto_zero I D (P i) (Q i) (hcompat i)
      (hcontract i) (hlocal i) f hf hy.cauchySeq
  have hb (v : V) : ‖D v‖ ≤ ‖y - D v‖ := by
    obtain ⟨i,hi⟩ := hcover v
    have hl : Tendsto (fun n => ‖D (P i (f n - v))‖) atTop (𝓝 ‖D v‖) := by
      simpa only [map_sub, hi, zero_sub, norm_neg] using ((hp i).sub_const (D v)).norm
    have hr := (hy.sub_const (D v)).norm
    apply le_of_tendsto_of_tendsto hl hr
    exact Eventually.of_forall (fun n => by
      simpa only [map_sub] using hcontract i (f n - v))
  have hzero : ‖y‖ ≤ 0 := by
    have hr : Tendsto (fun n => ‖y - D (f n)‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, norm_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).sub hy).norm
    exact le_of_tendsto_of_tendsto hy.norm hr (Eventually.of_forall (fun n => hb (f n)))
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

theorem formClosable_of_covering_projections [CompleteSpace Y]
    (I : V →ₗ[ℝ] X) (D : V →ₗ[ℝ] Y)
    (P : ι → V →ₗ[ℝ] V) (Q : ι → X →L[ℝ] X)
    (hcompat : ∀ i v, I (P i v) = Q i (I v))
    (hcontract : ∀ i v, ‖D (P i v)‖ ≤ ‖D v‖)
    (hcover : ∀ v, ∃ i, P i v = v)
    (hlocal : ∀ i, FormClosable 1 (I.comp (P i)) (D.comp (P i)))
    (κ : ℝ) (hκ : 0 ≤ κ) : FormClosable κ I D := by
  apply seqClosable_implies_nonnegative_form _ κ hκ
  exact seqClosable_of_covering_projections I D P Q hcompat hcontract hcover
    (fun i => form_implies_seqClosable 1 (by norm_num) (hlocal i))

end OperatorDerivativeRewrite.Foundation.ProjectedFormClosability
