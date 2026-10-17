import Foundation.SingleConeReality
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Half-energy limits for real-field Fourier concentration in a single cap. -/
noncomputable section
open MeasureTheory Set
open scoped Topology FourierTransform SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.SingleConeEnergyLimit
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

theorem reflected_integral (μ : Measure V) (hμ : MeasurePreserving Neg.neg μ μ)
    (a : V → ℝ) (he : ∀ x, a (-x)=a x) (s : Set V) :
    (∫ x in Neg.neg ⁻¹' s, a x ∂μ) = ∫ x in s, a x ∂μ := by
  have hh := hμ.setIntegral_preimage_emb (Homeomorph.neg V).measurableEmbedding a s
  simpa only [he] using hh

theorem even_density_half_integral (μ : Measure V) (hμ : MeasurePreserving Neg.neg μ μ)
    (a : V → ℝ) (hi : Integrable a μ) (hn : ∀ x, 0≤a x) (he : ∀ x, a (-x)=a x)
    (s : Set V) (hs : MeasurableSet s) (hd : Disjoint s (Neg.neg ⁻¹' s)) :
    2*(∫ x in s, a x ∂μ) ≤ ∫ x, a x ∂μ := by
  have hu := setIntegral_union hd (hs.preimage measurable_neg) hi.integrableOn hi.integrableOn
  have hb := setIntegral_le_integral (s := s ∪ Neg.neg ⁻¹' s) hi (Filter.Eventually.of_forall hn)
  rw [hu, reflected_integral μ hμ a he s] at hb
  linarith

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem direction_measurable : Measurable (SingleConeReality.direction : V → V) :=
  measurable_norm.inv.smul measurable_id

theorem cone_measurable (n : V) (δ : ℝ) : MeasurableSet (SingleConeReality.cone n δ) := by
  have hz : MeasurableSet {ξ : V | ξ≠0} := by
    change MeasurableSet (({(0 : V)} : Set V)ᶜ)
    exact (measurableSet_singleton (0 : V)).compl
  exact hz.inter
    (measurableSet_lt ((direction_measurable.sub measurable_const).norm) measurable_const)

theorem cone_disjoint_reflection (n : V) (δ : ℝ) (hδ : δ≤1) :
    Disjoint (SingleConeReality.cone n δ) (Neg.neg ⁻¹' SingleConeReality.cone n δ) := by
  apply Set.disjoint_left.mpr
  intro ξ hp hm
  exact SingleConeReality.cone_no_antipodes n δ hδ hp hm

variable {ι : Type*} [Fintype ι]

def momentDensity (c : ℝ) (f : 𝓢(V, EuclideanSpace ℂ ι)) (k : ℕ) (ξ : V) : ℝ :=
  (c*‖ξ‖)^k*‖𝓕 f ξ‖^2

def coneMoment (c : ℝ) (f : 𝓢(V, EuclideanSpace ℂ ι)) (k : ℕ) (n : V) (δ : ℝ) : ℝ :=
  ∫ ξ in SingleConeReality.cone n δ, momentDensity c f k ξ

theorem density_integrable (c : ℝ) (f : 𝓢(V, EuclideanSpace ℂ ι)) (k : ℕ) :
    Integrable (momentDensity c f k) volume :=
  SchwartzSpectralEnergies.spectral_integrand_integrable c f k

theorem density_nonneg (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι)) (k : ℕ) (ξ : V) :
    0≤momentDensity c f k ξ :=
  mul_nonneg (pow_nonneg (mul_nonneg hc (norm_nonneg ξ)) k) (sq_nonneg _)

theorem fourier_norm_sq_neg (f : 𝓢(V, EuclideanSpace ℂ ι))
    (hr : ∀ x i, starRingEnd ℂ (f x i)=f x i) (ξ : V) : ‖𝓕 f (-ξ)‖^2=‖𝓕 f ξ‖^2 := by
  simp only [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i hi
  rw [SingleConeReality.fourier_vector_reality f hr ξ i]
  simp

theorem density_even (c : ℝ) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (hr : ∀ x i, starRingEnd ℂ (f x i)=f x i) (k : ℕ) (ξ : V) :
    momentDensity c f k (-ξ)=momentDensity c f k ξ := by
  simp only [momentDensity, norm_neg, fourier_norm_sq_neg f hr]

theorem cone_twice_le_total (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (hr : ∀ x i, starRingEnd ℂ (f x i)=f x i) (k : ℕ) (n : V) (δ : ℝ) (hδ : δ≤1) :
    2*coneMoment c f k n δ ≤ SchwartzSpectralEnergies.spectralMoment c f k := by
  exact even_density_half_integral volume (Measure.measurePreserving_neg volume)
    (momentDensity c f k) (density_integrable c f k) (density_nonneg c hc f k)
    (density_even c f hr k) (SingleConeReality.cone n δ) (cone_measurable n δ)
    (cone_disjoint_reflection n δ hδ)

theorem cone_fraction_le_half (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (hr : ∀ x i, starRingEnd ℂ (f x i)=f x i) (k : ℕ) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hE : 0<SchwartzSpectralEnergies.spectralMoment c f k) :
    coneMoment c f k n δ / SchwartzSpectralEnergies.spectralMoment c f k ≤ (1:ℝ)/2 := by
  apply (div_le_iff₀ hE).mpr
  have hh := cone_twice_le_total c hc f hr k n δ hδ
  linarith

theorem dominance_forces_half_error (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (hr : ∀ x i, starRingEnd ℂ (f x i)=f x i) (k : ℕ) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hE : 0<SchwartzSpectralEnergies.spectralMoment c f k) (ε : ℝ)
    (hdom : (1-ε)*SchwartzSpectralEnergies.spectralMoment c f k ≤ coneMoment c f k n δ) :
    (1:ℝ)/2≤ε := by
  have hh := cone_twice_le_total c hc f hr k n δ hδ
  nlinarith

theorem no_near_total_single_cap (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (hr : ∀ x i, starRingEnd ℂ (f x i)=f x i) (k : ℕ) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hE : 0<SchwartzSpectralEnergies.spectralMoment c f k) (ε : ℝ) (hε : ε<(1:ℝ)/2)
    (hdom : (1-ε)*SchwartzSpectralEnergies.spectralMoment c f k ≤ coneMoment c f k n δ) : False := by
  exact (not_le_of_gt hε) (dominance_forces_half_error c hc f hr k n δ hδ hE ε hdom)

def projectedSpectralClass (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (k : ℕ) (s : Set V) (hs : MeasurableSet s) : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure V) :=
  (MemLp.indicator hs (SchwartzFractionalL2Fields.weighted_memLp c hc f k)).toLp
    (s.indicator (SchwartzFractionalL2Fields.weightedRepresentative c f k))

def projectedPhysicalField (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (k : ℕ) (s : Set V) (hs : MeasurableSet s) : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure V) :=
  𝓕⁻ (projectedSpectralClass c hc f k s hs)

theorem projectedSpectralClass_coeFn (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (k : ℕ) (s : Set V) (hs : MeasurableSet s) :
    projectedSpectralClass c hc f k s hs =ᵐ[volume]
      s.indicator (SchwartzFractionalL2Fields.weightedRepresentative c f k) :=
  (MemLp.indicator hs (SchwartzFractionalL2Fields.weighted_memLp c hc f k)).coeFn_toLp

theorem fourier_projectedPhysicalField (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (k : ℕ) (s : Set V) (hs : MeasurableSet s) :
    𝓕 (projectedPhysicalField c hc f k s hs) = projectedSpectralClass c hc f k s hs :=
  FourierTransform.fourier_fourierInv_eq _

theorem projectedSpectralClass_norm_sq (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (k : ℕ) (s : Set V) (hs : MeasurableSet s) :
    ‖projectedSpectralClass c hc f k s hs‖^2 = ∫ ξ in s, momentDensity c f k ξ := by
  rw [SchwartzFractionalL2Fields.l2_norm_sq_integral]
  calc
    _ = ∫ ξ : V, s.indicator (momentDensity c f k) ξ := by
      apply integral_congr_ae
      filter_upwards [projectedSpectralClass_coeFn c hc f k s hs] with ξ hξ
      rw [hξ]
      by_cases hm : ξ∈s
      · simp only [Set.indicator_of_mem hm,
          SchwartzFractionalL2Fields.weighted_norm_sq c hc, momentDensity]
      · simp [hm]
    _ = _ := integral_indicator hs

theorem projectedPhysicalField_norm_sq (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (k : ℕ) (s : Set V) (hs : MeasurableSet s) :
    ‖projectedPhysicalField c hc f k s hs‖^2 = ∫ ξ in s, momentDensity c f k ξ := by
  have hh := Lp.norm_fourier_eq (projectedPhysicalField c hc f k s hs)
  rw [fourier_projectedPhysicalField] at hh
  rw [← hh, projectedSpectralClass_norm_sq]

theorem real_cap_projection_half (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (hr : ∀ x i, starRingEnd ℂ (f x i)=f x i) (k : ℕ) (n : V) (δ : ℝ) (hδ : δ≤1) :
    2*‖projectedPhysicalField c hc f k (SingleConeReality.cone n δ) (cone_measurable n δ)‖^2 ≤
      SchwartzSpectralEnergies.spectralMoment c f k := by
  rw [projectedPhysicalField_norm_sq]
  exact cone_twice_le_total c hc f hr k n δ hδ

theorem no_real_dominant_cap_projection (c : ℝ) (hc : 0≤c) (f : 𝓢(V, EuclideanSpace ℂ ι))
    (hr : ∀ x i, starRingEnd ℂ (f x i)=f x i) (k : ℕ) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hE : 0<SchwartzSpectralEnergies.spectralMoment c f k) (ε : ℝ) (hε : ε<(1:ℝ)/2)
    (hdom : (1-ε)*SchwartzSpectralEnergies.spectralMoment c f k ≤
      ‖projectedPhysicalField c hc f k (SingleConeReality.cone n δ) (cone_measurable n δ)‖^2) : False := by
  rw [projectedPhysicalField_norm_sq] at hdom
  exact no_near_total_single_cap c hc f hr k n δ hδ hE ε hε hdom

end OperatorDerivativeRewrite.Foundation.SingleConeEnergyLimit
