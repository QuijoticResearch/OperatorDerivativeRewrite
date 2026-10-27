import Foundation.PhysicalHeatSquareBridge
import Mathlib.MeasureTheory.Function.LpOrder

/-! The finite Fourier square cone is dense in the real nonnegative Haar-L² cone.
The completed torus heat multiplier preserves that whole cone exactly under
the mixed-stable active-axis threshold. No pathwise Markov process or Lévy
realization is asserted. -/
open MeasureTheory AddCircle
open scoped NNReal ComplexConjugate BigOperators
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatPositiveCone
open FiniteFourierDifferentialTrace FiniteFourierReality
open FourierCovarianceCriterion
open PhysicalTorusWaveSemigroup WaveTorusCoreBridge PhysicalHeatSquareBridge

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torusSynthesis_denseRange : DenseRange torusSynthesis := by
  have hs : (Submodule.span ℂ (Set.range
      (UnitAddTorus.mFourier (d := Fin 3)))).topologicalClosure ≤
      torusSynthesis.range.topologicalClosure := by
    apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨AddMonoidAlgebra.single k 1, ?_⟩
    simp [torusSynthesis_single]
  have ht : torusSynthesis.range.topologicalClosure = ⊤ := by
    exact top_unique (by simpa only [UnitAddTorus.span_mFourier_closure_eq_top] using hs)
  apply denseRange_iff_closure_range.mpr
  change closure (torusSynthesis.range : Set C(UnitAddTorus (Fin 3), ℂ)) = Set.univ
  rw [← Submodule.topologicalClosure_coe, ht]
  rfl

theorem torusSynthesis_mul (f g : Fourier) (x : UnitAddTorus (Fin 3)) :
    torusSynthesis (f * g) x = torusSynthesis f x * torusSynthesis g x := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f h hf hh => simp [add_mul, map_add, hf, hh, add_mul]
  | single k c =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g h hg hh => simp [mul_add, map_add, hg, hh, mul_add]
    | single l d =>
      simp [AddMonoidAlgebra.single_mul_single, torusSynthesis_single,
        UnitAddTorus.mFourier_add, mul_assoc, mul_comm, mul_left_comm]


theorem torusSynthesis_reflection (f : Fourier) (x : UnitAddTorus (Fin 3)) :
    torusSynthesis (reflection f) x = conj (torusSynthesis f x) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single k c =>
    simp [reflection_single, torusSynthesis_single, UnitAddTorus.mFourier_neg]

theorem torusSynthesis_square (f : Fourier) (x : UnitAddTorus (Fin 3)) :
    torusSynthesis (reflection f * f) x =
      conj (torusSynthesis f x) * torusSynthesis f x := by
  rw [torusSynthesis_mul, torusSynthesis_reflection]

theorem continuous_nonnegative_square_closure
    (g : C(UnitAddTorus (Fin 3), ℂ))
    (hg : ∀ x, (g x).im = 0 ∧ 0 ≤ (g x).re) :
    g ∈ closure (Set.range (fun f : Fourier => torusSynthesis (reflection f * f))) := by
  let s : C(UnitAddTorus (Fin 3), ℂ) :=
    ⟨fun x => (Real.sqrt (g x).re : ℂ),
      Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (Complex.continuous_re.comp g.continuous))⟩
  have hs : star s * s = g := by
    ext x
    have hx := hg x
    apply Complex.ext
    · simpa [s, pow_two] using Real.sq_sqrt hx.2
    · simpa [s] using hx.1.symm
  have hc : Continuous (fun z : C(UnitAddTorus (Fin 3), ℂ) => star z * z) :=
    continuous_star.mul continuous_id
  have hm : star s * s ∈ closure
      (Set.range (fun f : Fourier => star (torusSynthesis f) * torusSynthesis f)) := by
    have h := (hc.range_subset_closure_image_dense torusSynthesis_denseRange)
      ⟨s, rfl⟩
    convert h using 1
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨torusSynthesis f, ⟨f, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨f, rfl⟩, rfl⟩
      exact ⟨f, rfl⟩
  rw [hs] at hm
  convert hm using 1
  congr 1
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨f, ?_⟩
    ext x
    exact (torusSynthesis_square f x).symm
  · rintro ⟨f, rfl⟩
    refine ⟨f, ?_⟩
    ext x
    exact torusSynthesis_square f x

def clip (z : ℂ) : ℂ := ((posPart (z.re) : ℝ) : ℂ)

theorem clip_lipschitz : LipschitzWith 1 clip := by
  have h := (RCLike.lipschitzWith_ofReal (K := ℂ)).comp
      (lipschitzWith_posPart.comp (RCLike.lipschitzWith_re (K := ℂ)))
  convert h using 1
  · norm_num
  · funext z
    simp [clip, Function.comp_def, RCLike.re_to_complex]

theorem clip_zero : clip 0 = 0 := by simp [clip]

def clipL2 : E → E :=
  clip_lipschitz.compLp clip_zero

theorem clipL2_continuous : Continuous clipL2 :=
  clip_lipschitz.continuous_compLp clip_zero

def clipC (g : C(UnitAddTorus (Fin 3), ℂ)) : C(UnitAddTorus (Fin 3), ℂ) :=
  ⟨fun x => clip (g x), clip_lipschitz.continuous.comp g.continuous⟩

theorem clipC_nonnegative (g : C(UnitAddTorus (Fin 3), ℂ)) (x) :
    ((clipC g) x).im = 0 ∧ 0 ≤ ((clipC g) x).re := by
  simp [clipC, clip]

theorem clipL2_toLp (g : C(UnitAddTorus (Fin 3), ℂ)) :
    clipL2 (ContinuousMap.toLp 2 volume ℂ g) =
      ContinuousMap.toLp 2 volume ℂ (clipC g) := by
  apply Lp.ext
  filter_upwards [LipschitzWith.coeFn_compLp clip_lipschitz
      clip_zero (ContinuousMap.toLp 2 volume ℂ g),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (E := ℂ) (p := 2) volume g,
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (E := ℂ) (p := 2) volume (clipC g)]
      with x hx hg hx'
  change (clipL2 (ContinuousMap.toLp 2 volume ℂ g)) x =
    ((ContinuousMap.toLp 2 volume ℂ) (clipC g)) x
  simp only [Function.comp_def] at hx
  rw [hg] at hx
  calc
    _ = clip (g x) := by simpa [clipL2, Function.comp_def] using hx
    _ = (clipC g) x := rfl
    _ = _ := hx'.symm

theorem clipL2_fixed_iff (f : E) :
    clipL2 f = f ↔
      ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume, (f x).im = 0 ∧ 0 ≤ (f x).re := by
  constructor
  · intro hf
    filter_upwards [LipschitzWith.coeFn_compLp clip_lipschitz
        clip_zero f] with x hx
    simp only [Function.comp_def] at hx
    have he : clip (f x) = f x := by
      have hval : (clipL2 f) x = f x := by rw [hf]
      exact hx.symm.trans hval
    constructor
    · have hi := congrArg Complex.im he
      simpa [clip] using hi.symm
    · have hp : 0 ≤ (clip (f x)).re := by simp [clip]
      rw [he] at hp
      exact hp
  · intro hf
    apply Lp.ext
    filter_upwards [LipschitzWith.coeFn_compLp clip_lipschitz
        clip_zero f, hf] with x hx hfx
    change (clip_lipschitz.compLp clip_zero f) x = f x
    simp only [Function.comp_def] at hx
    rw [hx]
    apply Complex.ext
    · simp [clip, posPart_eq_self.mpr hfx.2]
    · simp [clip, hfx.1]

theorem positive_continuous_l2_square_closure
    (g : C(UnitAddTorus (Fin 3), ℂ))
    (hg : ∀ x, (g x).im = 0 ∧ 0 ≤ (g x).re) :
    ContinuousMap.toLp 2 volume ℂ g ∈
      closure (Set.range (fun f : Fourier => lift (reflection f * f))) := by
  have hg0 := continuous_nonnegative_square_closure g hg
  have hm := image_closure_subset_closure_image
    (ContinuousMap.toLp 2 volume ℂ).continuous
      (Set.mem_image_of_mem _ hg0)
  convert hm using 1
  congr 1
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨torusSynthesis (reflection f * f), ⟨f, rfl⟩, ?_⟩
    exact torusSynthesis_toLp _
  · rintro ⟨q, ⟨f, rfl⟩, rfl⟩
    exact ⟨f, (torusSynthesis_toLp _).symm⟩

theorem positive_l2_square_closure (u : E)
    (hu : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (u x).im = 0 ∧ 0 ≤ (u x).re) :
    u ∈ closure (Set.range (fun f : Fourier => lift (reflection f * f))) := by
  have hd : DenseRange (ContinuousMap.toLp 2 volume ℂ :
      C(UnitAddTorus (Fin 3), ℂ) → E) :=
    ContinuousMap.toLp_denseRange ℂ volume ℂ (by simp)
  have hfix := (clipL2_fixed_iff u).mpr hu
  have hm := (clipL2_continuous.range_subset_closure_image_dense hd)
    ⟨u, rfl⟩
  rw [hfix] at hm
  have hs : clipL2 '' Set.range
      (ContinuousMap.toLp 2 volume ℂ : C(UnitAddTorus (Fin 3), ℂ) → E) ⊆
      closure (Set.range (fun f : Fourier => lift (reflection f * f))) := by
    rintro z ⟨q, ⟨g, rfl⟩, rfl⟩
    rw [clipL2_toLp]
    exact positive_continuous_l2_square_closure (clipC g)
      (clipC_nonnegative g)
  exact (by simpa only [closure_closure] using (closure_mono hs) hm)

theorem positive_l2_iff_square_closure (u : E) :
    (∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (u x).im = 0 ∧ 0 ≤ (u x).re) ↔
    u ∈ closure (Set.range (fun f : Fourier => lift (reflection f * f))) := by
  constructor
  · exact positive_l2_square_closure u
  · intro hu
    have hc : IsClosed {v : E | clipL2 v = v} :=
      isClosed_eq clipL2_continuous continuous_id
    have hs : Set.range (fun f : Fourier => lift (reflection f * f)) ⊆
        {v : E | clipL2 v = v} := by
      rintro v ⟨f, rfl⟩
      exact (clipL2_fixed_iff _).mpr (physical_square_input_ae f)
    exact (clipL2_fixed_iff _).mp ((closure_minimal hs hc) hu)

theorem physical_evolution_positive_all (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (t : ℝ≥0) (u : E)
    (hu : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (u x).im = 0 ∧ 0 ≤ (u x).re) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ((evolution r t u) x).im = 0 ∧ 0 ≤ ((evolution r t u) x).re := by
  have hc : IsClosed {v : E | clipL2 (evolution r t v) = evolution r t v} :=
    isClosed_eq (clipL2_continuous.comp (evolution r t).continuous)
      (evolution r t).continuous
  have hs : Set.range (fun f : Fourier => lift (reflection f * f)) ⊆
      {v : E | clipL2 (evolution r t v) = evolution r t v} := by
    rintro v ⟨f, rfl⟩
    exact (clipL2_fixed_iff _).mpr (physical_evolution_square_ae r hr t f)
  have hclosure := (closure_minimal hs hc) (positive_l2_square_closure u hu)
  exact (clipL2_fixed_iff _).mp hclosure

theorem anisotropic_physical_evolution_positive_all
    (a γ : Fin 3 → ℝ) (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j)
    (hactive : ∀ j, 0 < a j → γ j ≤ 2) (t : ℝ≥0) (u : E)
    (hu : ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      (u x).im = 0 ∧ 0 ≤ (u x).re) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
      ((evolution (WaveDiagonalSemigroup.rate a γ ha) t u) x).im = 0 ∧
      0 ≤ ((evolution (WaveDiagonalSemigroup.rate a γ ha) t u) x).re := by
  apply physical_evolution_positive_all
  · change CovarianceSymbol
      (AnisotropicStableGamma.anisotropicSymbol a γ)
    exact AnisotropicMixedThreshold.anisotropic_covariance_of_positive_axes
      a γ ha hγ0 hactive
  · exact hu

theorem anisotropic_stationary_constant
    (a γ : Fin 3 → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hγ0 : ∀ j, 0 < γ j) (t : ℝ≥0) :
    evolution (WaveDiagonalSemigroup.rate a γ ha) t (basis 0) = basis 0 := by
  apply stationary_mode
  apply Subtype.ext
  exact AnisotropicStableGamma.anisotropic_zero a γ hγ0

theorem anisotropic_physical_positive_iff_active
    (a γ : Fin 3 → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hγ0 : ∀ j, 0 < γ j) :
    (∀ (t : ℝ≥0) (u : E),
      (∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
        (u x).im = 0 ∧ 0 ≤ (u x).re) →
      ∀ᵐ x : UnitAddTorus (Fin 3) ∂volume,
        ((evolution (WaveDiagonalSemigroup.rate a γ ha) t u) x).im = 0 ∧
        0 ≤ ((evolution (WaveDiagonalSemigroup.rate a γ ha) t u) x).re) ↔
      ∀ j, 0 < a j → γ j ≤ 2 := by
  constructor
  · intro h
    apply (anisotropic_physical_square_positive_iff_active a γ ha hγ0).mp
    intro t f
    filter_upwards [h t _ (physical_square_input_ae f)] with x hx
    exact hx.2
  · intro hactive t u hu
    exact anisotropic_physical_evolution_positive_all
      a γ ha hγ0 hactive t u hu

end OperatorDerivativeRewrite.Foundation.PhysicalHeatPositiveCone
