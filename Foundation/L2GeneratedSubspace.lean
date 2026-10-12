import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual L2 pullbacks exhaust the subspace measurable with respect to an
observation map. Doob--Dynkin is applied to measurable representatives; all
identifications of L2 classes are almost everywhere. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  {μ : Measure Ω} {ν : Measure E} {X : Ω → E}

/-- An almost-everywhere measurable factorization of observation maps suffices
to transfer their generated measurable L2 subspaces. -/
theorem aestronglyMeasurable_comap_of_ae_factor
    {V : Type*} [MeasurableSpace V] {Y : Ω → V} {k : V → E}
    (hk : Measurable k) (hXY : X =ᵐ[μ] k ∘ Y) {F : Ω → ℝ}
    (hF : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] F μ) :
    AEStronglyMeasurable[MeasurableSpace.comap Y inferInstance] F μ := by
  obtain ⟨g, hg, he⟩ := hF.stronglyMeasurable_mk.exists_eq_measurable_comp
  have hm : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] (g ∘ k ∘ Y) :=
    (hg.comp_measurable hk).comp_measurable (Measurable.of_comap_le le_rfl)
  apply hm.aestronglyMeasurable.congr
  have hFg : F =ᵐ[μ] g ∘ X := he ▸ hF.ae_eq_mk
  filter_upwards [hFg, hXY] with ω hf hx
  exact (hf.trans (congrArg g hx)).symm

/-- Every L2 class measurable in the observation sigma-algebra is an actual
pullback of an L2 class for the observation law. No injectivity is required. -/
theorem exists_L2_pullback (hX : MeasurePreserving X μ ν) (F : Lp ℝ 2 μ)
    (hF : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] F μ) :
    ∃ g : Lp ℝ 2 ν, Lp.compMeasurePreserving X hX g = F := by
  obtain ⟨g, hg, he⟩ := hF.stronglyMeasurable_mk.exists_eq_measurable_comp
  have hcomp : MemLp (g ∘ X) 2 μ := by
    rw [← he]
    exact (Lp.memLp F).ae_eq hF.ae_eq_mk
  have hmap : MemLp g 2 (Measure.map X μ) :=
    (memLp_map_measure_iff hg.aestronglyMeasurable hX.measurable.aemeasurable).2 hcomp
  have hmem : MemLp g 2 ν := by simpa only [hX.map_eq] using hmap
  refine ⟨hmem.toLp g, Lp.ext ?_⟩
  exact (Lp.coeFn_compMeasurePreserving (hmem.toLp g) hX).trans
    ((hX.quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hmem)).trans
      (he ▸ hF.ae_eq_mk).symm)

/-- Conversely every actual pullback is measurable in the generated sigma-algebra. -/
theorem L2_pullback_aestronglyMeasurable (hX : MeasurePreserving X μ ν)
    (g : Lp ℝ 2 ν) :
    AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (Lp.compMeasurePreserving X hX g) μ := by
  have hm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (g ∘ X) :=
    (Lp.stronglyMeasurable g).comp_measurable (by exact fun _ hs => ⟨_, hs, rfl⟩)
  exact hm.aestronglyMeasurable.congr (Lp.coeFn_compMeasurePreserving g hX).symm

/-- Exact range equality with Mathlib's existing measurable L2 subspace. -/
theorem L2_pullback_range (hX : MeasurePreserving X μ ν) :
    (Lp.compMeasurePreservingₗ ℝ X hX).range =
      lpMeas ℝ ℝ (MeasurableSpace.comap X inferInstance) 2 μ := by
  ext F
  constructor
  · rintro ⟨g, rfl⟩
    exact L2_pullback_aestronglyMeasurable hX g
  · intro hF
    exact exists_L2_pullback hX F hF

/-- Dense approximation for the observation law transfers to every class in
the generated measurable subspace, with exactly the same L2 error. -/
theorem exists_L2_pullback_approx (hX : MeasurePreserving X μ ν)
    {S : Set (Lp ℝ 2 ν)} (hS : Dense S) (F : Lp ℝ 2 μ)
    (hF : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] F μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ S, ‖F - Lp.compMeasurePreserving X hX g‖ < ε := by
  obtain ⟨f, rfl⟩ := exists_L2_pullback hX F hF
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp (hS f) ε hε
  refine ⟨g, hg, ?_⟩
  have he := (Lp.compMeasurePreservingₗᵢ ℝ X hX).norm_map (f - g)
  rw [map_sub] at he
  change ‖Lp.compMeasurePreserving X hX f - Lp.compMeasurePreserving X hX g‖ = _ at he
  rw [he]
  simpa only [dist_eq_norm] using hdist

end OperatorDerivativeRewrite.Foundation
