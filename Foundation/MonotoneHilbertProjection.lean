import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! Strong measurability of increasing Hilbert projections follows from monotone
energies and real polarization. Continuity of the projection family is not
assumed. Separability is required only for the vector measurability theorem. -/
noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MonotoneHilbertProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (V : ℝ≥0 → Submodule ℝ E) [∀ t, (V t).HasOrthogonalProjection]

def energy (t : ℝ≥0) (x : E) : ℝ := ‖(V t).starProjection x‖^2

theorem energy_mono (hV : Monotone V) (x : E) : Monotone (fun t => energy V t x) := by
  intro s t hst
  have he : (V s).starProjection ((V t).starProjection x) = (V s).starProjection x :=
    DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le (hV hst)) x
  have hn := (V s).norm_starProjection_apply_le ((V t).starProjection x)
  rw [he] at hn
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn

theorem inner_energy (t : ℝ≥0) (x y : E) :
    inner ℝ ((V t).starProjection x) y = (energy V t (x+y)-energy V t (x-y))/4 := by
  have he := (V t).inner_starProjection_left_eq_right ((V t).starProjection x) y
  rw [(V t).starProjection_eq_self_iff.2 ((V t).starProjection_apply_mem x)] at he
  unfold energy
  rw [map_add,map_sub,norm_add_sq_real,norm_sub_sq_real]
  linarith

theorem energy_measurable (hV : Monotone V) (x : E) : Measurable (fun t => energy V t x) :=
  (energy_mono V hV x).measurable

theorem inner_measurable (hV : Monotone V) (x y : E) :
    Measurable (fun t => inner ℝ ((V t).starProjection x) y) := by
  simp_rw [inner_energy]
  exact ((energy_measurable V hV (x+y)).sub (energy_measurable V hV (x-y))).div_const 4

theorem dist_measurable (hV : Monotone V) (x y : E) :
    Measurable (fun t => dist ((V t).starProjection x) y) := by
  have hm := ((energy_measurable V hV x).add_const (‖y‖^2)).sub
    ((inner_measurable V hV x y).const_mul 2)
  have hs := hm.sqrt
  convert hs using 1
  funext t
  simp only [Pi.sub_apply,energy,dist_eq_norm]
  have he : ‖(V t).starProjection x‖^2+‖y‖^2-2*inner ℝ ((V t).starProjection x) y =
      ‖(V t).starProjection x-y‖^2 := by rw [norm_sub_sq_real]; ring
  rw [he,Real.sqrt_sq (norm_nonneg _)]

theorem stronglyMeasurable_projection [SecondCountableTopology E] (hV : Monotone V) (x : E) :
    StronglyMeasurable (fun t => (V t).starProjection x) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hb : IsTopologicalBasis {s : Set E | ∃ y r, 0 < r ∧ s = Metric.ball y r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨y,r,hr,rfl⟩
      exact Metric.isOpen_ball
    · intro y s hy hs
      obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.1 (hs.mem_nhds hy)
      exact ⟨Metric.ball y r,⟨y,r,hr,rfl⟩,Metric.mem_ball_self hr,hsub⟩
  have hm : @Measurable ℝ≥0 E _ (borel E) (fun t => (V t).starProjection x) := by
    rw [hb.borel_eq_generateFrom]
    apply measurable_generateFrom
    rintro s ⟨y,r,hr,rfl⟩
    exact measurableSet_lt (dist_measurable V hV x y) measurable_const
  exact hm.stronglyMeasurable

end OperatorDerivativeRewrite.Foundation.MonotoneHilbertProjection
