import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Order.Cadlag
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! Right-continuous adapted processes are progressively measurable, via ceiling grids. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RightContinuousProgressive

def grid (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := min T ((k : ℝ≥0)/(n+1 : ℕ))

def index (n : ℕ) (r : ℝ≥0) : ℕ := Nat.ceil ((r : ℝ)*((n+1 : ℕ) : ℝ))

def approximate (T : ℝ≥0) (n : ℕ) (r : ℝ≥0) : ℝ≥0 := grid T n (index n r)

theorem index_measurable (n : ℕ) : Measurable (index n) :=
  (measurable_coe_nnreal_real.mul_const _).nat_ceil

theorem grid_le (T : ℝ≥0) (n k : ℕ) : grid T n k ≤ T := min_le_left _ _

theorem approximate_ge (T r : ℝ≥0) (hr : r ≤ T) (n : ℕ) : r ≤ approximate T n r := by
  apply le_min hr
  apply (le_div_iff₀ (by positivity : (0 : ℝ≥0) < ((n+1 : ℕ) : ℝ≥0))).mpr
  exact_mod_cast Nat.le_ceil ((r : ℝ)*((n+1 : ℕ) : ℝ))

theorem approximate_tendsto (T r : ℝ≥0) (hr : r ≤ T) :
    Tendsto (fun n => approximate T n r) atTop (𝓝 r) := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have he := (tendsto_nat_ceil_mul_div_atTop r.coe_nonneg).comp hn
  have hm : Tendsto (fun n : ℕ => min (T : ℝ)
      ((Nat.ceil ((r : ℝ)*((n+1 : ℕ) : ℝ)) : ℝ)/((n+1 : ℕ) : ℝ))) atTop
      (𝓝 (min (T : ℝ) (r : ℝ))) := tendsto_const_nhds.min he
  rw [min_eq_right (show (r : ℝ) ≤ (T : ℝ) from hr)] at hm
  apply NNReal.tendsto_coe.mp
  simpa only [Function.comp_def,approximate,grid,index,NNReal.coe_min,NNReal.coe_div,
    NNReal.coe_natCast] using hm

attribute [local irreducible] grid index approximate

theorem step_measurable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (ℱ : Filtration ℝ≥0 mΩ) (u : ℝ≥0 → Ω → E) (hu : StronglyAdapted ℱ u)
    (T : ℝ≥0) (n : ℕ) :
    @Measurable (Iic T × Ω) E (MeasurableSpace.prod inferInstance (ℱ T)) inferInstance
      (fun p => u (approximate T n p.1) p.2) := by
  let : MeasurableSpace Ω := ℱ T
  have hstep :
      @Measurable (Iic T × Ω) E (MeasurableSpace.prod inferInstance (ℱ T)) inferInstance
        (fun p => u (approximate T n p.1) p.2) := by
    have hm : @Measurable (ℕ × Ω) E (MeasurableSpace.prod inferInstance (ℱ T)) inferInstance
        (fun p => u (grid T n p.1) p.2) :=
      measurable_from_prod_countable_right (fun k =>
        ((hu (grid T n k)).mono (ℱ.mono (grid_le T n k))).measurable)
    have hx : Measurable (fun p : Iic T × Ω => (index n p.1,p.2)) :=
      ((index_measurable n).comp (measurable_subtype_coe.comp measurable_fst)).prodMk
        measurable_snd
    simpa only [Function.comp_def,approximate] using hm.comp hx
  exact hstep

theorem progressive {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (ℱ : Filtration ℝ≥0 mΩ) (u : ℝ≥0 → Ω → E) (hu : StronglyAdapted ℱ u)
    (hr : ∀ ω, IsRightContinuous (fun t => u t ω)) : IsStronglyProgressive ℱ u := by
  intro T
  let : MeasurableSpace Ω := ℱ T
  apply stronglyMeasurable_of_tendsto atTop
    (f := fun n p => u (approximate T n p.1) p.2)
    (fun n => (step_measurable (mΩ := mΩ) ℱ u hu T n).stronglyMeasurable)
  apply tendsto_pi_nhds.mpr
  intro p
  have hge : Tendsto (fun n => approximate T n p.1) atTop (𝓟 (Ici (p.1 : ℝ≥0))) :=
    tendsto_principal.mpr (Eventually.of_forall (fun n => approximate_ge T p.1 p.1.property n))
  have ht := (approximate_tendsto T p.1 p.1.property).inf hge
  simp only [inf_idem] at ht
  exact Filter.Tendsto.comp (continuousWithinAt_Ioi_iff_Ici.mp (hr p.2 p.1)) ht

end OperatorDerivativeRewrite.Foundation.RightContinuousProgressive
