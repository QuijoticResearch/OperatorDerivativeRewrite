import Foundation.GaussianDyadicGeometry

/-! Measurable continuous modifications of Gaussian-L²-valued continuous
curves from a proved countable dyadic event. The event is a visible hypothesis,
not the desired continuity conclusion. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace OperatorDerivativeRewrite.Foundation.GaussianContinuousModification
open InfiniteGaussian IBMDyadicExtension

variable (F : ℝ → GaussianL2) (θ : ℝ)

def good (ω : SampleSpace) : Prop := ∀ z : ℤ, ∃ N : ℕ, ∀ l ≥ N, ∀ k : Fin (2^l),
  |F (grid z l (k.val+1)) ω - F (grid z l k.val) ω| < θ^l

theorem good_measurable : MeasurableSet {ω | good F θ ω} := by
  unfold good
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  apply MeasurableSet.iInter; intro z
  apply MeasurableSet.iUnion; intro N
  apply MeasurableSet.iInter; intro l
  apply MeasurableSet.iInter; intro _hl
  apply MeasurableSet.iInter; intro k
  exact measurableSet_lt (continuous_abs.measurable.comp
    ((Lp.stronglyMeasurable _).measurable.sub (Lp.stronglyMeasurable _).measurable)) measurable_const

variable (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)

def localPath (z : ℤ) (ω : SampleSpace) : C(UnitInterval, ℝ) :=
  if h : good F θ ω then
    ⟨extension (fun r => F r ω) z, GaussianDyadicGeometry.extension_continuous hθ0 hθ1
      (by obtain ⟨N, hN⟩ := h z
          exact eventually_atTop.mpr ⟨N, fun l hl k => (hN l hl k).le⟩)⟩
  else 0

theorem localPath_measurable (z : ℤ) : Measurable (localPath F θ hθ0 hθ1 z) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro x
  have hm : Measurable (fun ω => extension (fun r => F r ω) z x) :=
    Measurable.limsup fun l => (Lp.stronglyMeasurable _).measurable
  have he : (fun ω => localPath F θ hθ0 hθ1 z ω x) =
      fun ω => if good F θ ω then extension (fun r => F r ω) z x else 0 := by
    funext ω
    by_cases h : good F θ ω <;> simp [localPath, h]
  rw [he]
  exact Measurable.ite (good_measurable F θ) hm measurable_const

theorem localPath_zero (z : ℤ) (ω : SampleSpace) :
    localPath F θ hθ0 hθ1 z ω zeroPoint = if good F θ ω then F z ω else 0 := by
  by_cases hg : good F θ ω
  · simp only [localPath, dite_eq_left hg, ContinuousMap.coe_mk, ite_eq_left hg, extension,
      rounded_zero]
    exact tendsto_const_nhds.limsup_eq
  · simp [localPath, hg]

theorem localPath_one (z : ℤ) (ω : SampleSpace) :
    localPath F θ hθ0 hθ1 z ω onePoint = if good F θ ω then F ((z : ℝ)+1) ω else 0 := by
  by_cases hg : good F θ ω
  · simp only [localPath, dite_eq_left hg, ContinuousMap.coe_mk, ite_eq_left hg, extension,
      rounded_one]
    exact tendsto_const_nhds.limsup_eq
  · simp [localPath, hg]

theorem compatible (ω : SampleSpace) (z w : ℤ) (r : ℝ)
    (hz : r ∈ window z) (hw : r ∈ window w) :
    localPath F θ hθ0 hθ1 z ω (chart z ⟨r, hz⟩) =
      localPath F θ hθ0 hθ1 w ω (chart w ⟨r, hw⟩) := by
  have ordered : ∀ z w : ℤ, ∀ hz : r ∈ window z, ∀ hw : r ∈ window w, z < w →
      localPath F θ hθ0 hθ1 z ω (chart z ⟨r, hz⟩) =
        localPath F θ hθ0 hθ1 w ω (chart w ⟨r, hw⟩) := by
    intro z w hz hw hzw
    have hstep : (z : ℝ)+1 ≤ (w : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hzw)
    have he : (z : ℝ)+1 = (w : ℝ) := by linarith [hz.2, hw.1]
    have hc1 : chart z ⟨r, hz⟩ = onePoint := by apply Subtype.ext; change r-z = 1; linarith [hz.2, hw.1]
    have hc0 : chart w ⟨r, hw⟩ = zeroPoint := by apply Subtype.ext; change r-w = 0; linarith [hz.2, hw.1]
    rw [hc1, hc0, localPath_one, localPath_zero, he]
  rcases lt_trichotomy z w with h | h | h
  · exact ordered z w hz hw h
  · subst w; rfl
  · exact (ordered w z hw hz h).symm

def field (ω : SampleSpace) : ℝ → ℝ :=
  Set.liftCover window (fun z r => localPath F θ hθ0 hθ1 z ω (chart z r))
    (compatible F θ hθ0 hθ1 ω) windows_cover

theorem field_on_window (ω : SampleSpace) (z : ℤ) (r : ℝ) (hr : r ∈ window z) :
    field F θ hθ0 hθ1 ω r = localPath F θ hθ0 hθ1 z ω (chart z ⟨r, hr⟩) :=
  Set.liftCover_of_mem hr

theorem field_continuous (ω : SampleSpace) : Continuous (field F θ hθ0 hθ1 ω) := by
  have hu : Tendsto (fun z : ℤ => (z : ℝ)+1) atBot atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [((tendsto_intCast_atBot_iff.mpr tendsto_id) :
      Tendsto (fun z : ℤ => (z : ℝ)) atBot atBot).eventually
        (eventually_le_atBot (b-1))] with z hz
    linarith
  have hloc : LocallyFinite window := locallyFinite_Icc_of_tendsto tendsto_intCast_atTop_atTop hu
  apply hloc.continuous windows_cover (fun _ => isClosed_Icc)
  intro z
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : Set.domRestrict (window z) (field F θ hθ0 hθ1 ω) =
      fun r => localPath F θ hθ0 hθ1 z ω (chart z r) := by
    funext r; exact field_on_window F θ hθ0 hθ1 ω z r r.property
  rw [he]
  exact (localPath F θ hθ0 hθ1 z ω).continuous.comp (chart_continuous z)

theorem field_coordinate_measurable (r : ℝ) : Measurable (fun ω => field F θ hθ0 hθ1 ω r) := by
  have hr : r ∈ window ⌊r⌋ := ⟨Int.floor_le r, (Int.lt_floor_add_one r).le⟩
  have he : (fun ω => field F θ hθ0 hθ1 ω r) =
      fun ω => localPath F θ hθ0 hθ1 ⌊r⌋ ω (chart ⌊r⌋ ⟨r, hr⟩) := by
    funext ω; exact field_on_window F θ hθ0 hθ1 ω ⌊r⌋ r hr
  rw [he]
  exact (ContinuousMap.measurable_eval _).comp (localPath_measurable F θ hθ0 hθ1 ⌊r⌋)

def path (ω : SampleSpace) : C(ℝ, ℝ) := ⟨field F θ hθ0 hθ1 ω, field_continuous F θ hθ0 hθ1 ω⟩

theorem path_measurable : Measurable (path F θ hθ0 hθ1) :=
  ContinuousMap.measurable_iff_eval.mpr (field_coordinate_measurable F θ hθ0 hθ1)

theorem field_coordinate_ae (hF : Continuous F) (hgood : ∀ᵐ ω ∂gaussianProduct, good F θ ω)
    (r : ℝ) : (fun ω => field F θ hθ0 hθ1 ω r) =ᵐ[gaussianProduct] F r := by
  let z : ℤ := ⌊r⌋
  have hr : r ∈ window z := ⟨Int.floor_le r, (Int.lt_floor_add_one r).le⟩
  let x : UnitInterval := chart z ⟨r, hr⟩
  have hsp : Tendsto (fun l => grid z l (index l x)) atTop (𝓝 r) := by
    have he : (z : ℝ)+x.val = r := by simp [x, chart]
    rw [← he]
    exact grid_index_tendsto z x
  have hclass := tendstoInMeasure_of_tendsto_Lp (hF.continuousAt.tendsto.comp hsp)
  have hsample : ∀ᵐ ω ∂gaussianProduct,
      Tendsto (fun l => F (grid z l (index l x)) ω) atTop (𝓝 (field F θ hθ0 hθ1 ω r)) := by
    filter_upwards [hgood] with ω hω
    rw [field_on_window F θ hθ0 hθ1 ω z r hr]
    simp only [localPath, dite_eq_left hω, ContinuousMap.coe_mk]
    apply GaussianDyadicGeometry.extension_tendsto hθ0 hθ1
    obtain ⟨N, hN⟩ := hω z
    exact eventually_atTop.mpr ⟨N, fun l hl k => (hN l hl k).le⟩
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_ae
    (fun _ => (Lp.stronglyMeasurable _).aestronglyMeasurable) hsample) hclass

end OperatorDerivativeRewrite.Foundation.GaussianContinuousModification
