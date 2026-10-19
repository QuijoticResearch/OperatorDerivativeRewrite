import Foundation.IBMFoldedTransitionBound
import Foundation.DiagonalAmbientNullity
import Foundation.BrownianSignIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Uniform time-integrated bounds for the actual IBM clock covariance.
The diagonal is removed using product-Lebesgue nullity, not by assigning its
positive finite-mollifier covariance the value zero. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMClockOverlapEnergy
open IBMFoldedTransitionBound
attribute [local irreducible] IBMConstructedSources.clockPath

def window (T : ℝ) : Measure ℝ := volume.restrict (Ioc 0 T)

instance window_finite (T : ℝ) : IsFiniteMeasure (window T) := by unfold window; infer_instance

def halfKernel (T x : ℝ) : ℝ := (Ioc 0 T).indicator (fun y : ℝ => y ^ (-(1/2 : ℝ))) x

theorem halfKernel_nonneg (T x : ℝ) : 0 ≤ halfKernel T x := by
  by_cases hx : x ∈ Ioc 0 T
  · simp only [halfKernel, indicator_of_mem hx]
    exact Real.rpow_nonneg hx.1.le _
  · simp [halfKernel, hx]

theorem halfKernel_measurable (T : ℝ) : Measurable (halfKernel T) := by
  exact (measurable_id.pow_const _).indicator measurableSet_Ioc

theorem halfKernel_integrable {T : ℝ} (hT : 0 ≤ T) : Integrable (halfKernel T) := by
  apply IntegrableOn.integrable_indicator ?_ measurableSet_Ioc
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (by norm_num : -1 < -(1/2 : ℝ))).def'
  simpa only [uIoc_of_le hT] using hi

theorem halfKernel_mass {T : ℝ} (hT : 0 ≤ T) :
    (∫ x, halfKernel T x) = 2 * Real.sqrt T := by
  simp only [halfKernel]
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hT,
    integral_rpow (Or.inl (by norm_num : -1 < -(1/2 : ℝ)))]
  norm_num [← Real.sqrt_eq_rpow]
  ring

def timeKernel (T s t : ℝ) : ℝ := halfKernel T (t-s) + halfKernel T (s-t)

theorem timeKernel_nonneg (T s t : ℝ) : 0 ≤ timeKernel T s t :=
  add_nonneg (halfKernel_nonneg _ _) (halfKernel_nonneg _ _)

theorem timeKernel_measurable (T : ℝ) :
    Measurable (fun p : ℝ × ℝ => timeKernel T p.1 p.2) :=
  ((halfKernel_measurable T).comp (measurable_snd.sub measurable_fst)).add
    ((halfKernel_measurable T).comp (measurable_fst.sub measurable_snd))

theorem timeKernel_row_integrable {T : ℝ} (hT : 0 ≤ T) (s : ℝ) :
    Integrable (timeKernel T s) := by
  have hi := halfKernel_integrable hT
  have hn := hi.comp_neg.comp_sub_right s
  simp only [neg_sub] at hn
  exact (hi.comp_sub_right s).add hn

theorem timeKernel_row_mass {T : ℝ} (hT : 0 ≤ T) (s : ℝ) :
    (∫ t, timeKernel T s t) = 4 * Real.sqrt T := by
  have hi := halfKernel_integrable hT
  have hn := hi.comp_neg.comp_sub_right s
  simp only [neg_sub] at hn
  simp only [timeKernel]
  rw [integral_add (hi.comp_sub_right s) hn]
  have hright : (∫ t, halfKernel T (t-s)) = ∫ t, halfKernel T t := by
    simpa only [sub_eq_neg_add] using integral_add_left_eq_self (μ := volume) (halfKernel T) (-s)
  have hleft : (∫ t, halfKernel T (s-t)) = ∫ t, halfKernel T t := by
    have hneg := integral_neg_eq_self (fun t : ℝ => halfKernel T (s+t)) volume
    simpa only [sub_eq_add_neg] using
      hneg.trans (integral_add_left_eq_self (μ := volume) (halfKernel T) s)
  rw [hright, hleft, halfKernel_mass hT]
  ring

theorem timeKernel_row_bound {T : ℝ} (hT : 0 ≤ T) (s : ℝ) :
    (∫ t, timeKernel T s t ∂window T) ≤ 4 * Real.sqrt T := by
  exact (setIntegral_le_integral (timeKernel_row_integrable hT s)
    (ae_of_all _ (timeKernel_nonneg T s))).trans_eq (timeKernel_row_mass hT s)

theorem timeKernel_integrable {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun p : ℝ × ℝ => timeKernel T p.1 p.2) ((window T).prod (window T)) := by
  apply (integrable_prod_iff (timeKernel_measurable T).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ fun s => (timeKernel_row_integrable hT s).integrableOn, ?_⟩
  have hm := (timeKernel_measurable T).stronglyMeasurable.norm.integral_prod_right'
    (ν := window T)
  apply Integrable.of_bound hm.aestronglyMeasurable (4 * Real.sqrt T)
  exact ae_of_all _ fun s => by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (timeKernel_nonneg T s _)]
    rw [abs_of_nonneg (integral_nonneg (timeKernel_nonneg T s))]
    exact timeKernel_row_bound hT s

theorem timeKernel_integral_bound {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : ℝ × ℝ, timeKernel T p.1 p.2 ∂(window T).prod (window T)) ≤
      4 * T * Real.sqrt T := by
  rw [integral_prod _ (timeKernel_integrable hT)]
  calc
    _ ≤ ∫ _s : ℝ, 4 * Real.sqrt T ∂window T :=
      integral_mono_of_nonneg (ae_of_all _ fun s => integral_nonneg (timeKernel_nonneg T s))
        (integrable_const _) (ae_of_all _ (timeKernel_row_bound hT))
    _ = _ := by simp [window, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hT]; ring

theorem timeKernel_off_diagonal {T s t : ℝ} (hs : s ∈ Ioc 0 T)
    (ht : t ∈ Ioc 0 T) (hne : s ≠ t) :
    timeKernel T s t = |t-s| ^ (-(1/2 : ℝ)) := by
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hp : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hst, by linarith [hs.1, ht.2]⟩
    have hn : s-t ∉ Ioc 0 T := fun h => by linarith [h.1]
    simp [timeKernel, halfKernel, hp, hn, abs_of_pos (sub_pos.mpr hst)]
  · have hp : s-t ∈ Ioc 0 T := ⟨sub_pos.mpr hts, by linarith [ht.1, hs.2]⟩
    have hn : t-s ∉ Ioc 0 T := fun h => by linarith [h.1]
    simp only [timeKernel, halfKernel, indicator_of_notMem hn, indicator_of_mem hp, zero_add,
      abs_of_neg (sub_neg.mpr hts), neg_sub]

theorem peak_nndist (s t : ℝ) :
    peak (nndist t s) = peak 1 * |t-s| ^ (-(1/2 : ℝ)) := by
  simp only [peak, coe_nndist, Real.dist_eq, NNReal.coe_one, mul_one]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), mul_inv_rev,
    Real.rpow_neg (abs_nonneg (t-s)), ← Real.sqrt_eq_rpow]
  ring

def covariance (n m : ℕ) (s t : ℝ) : ℝ :=
  ∫ ω, overlap n m |IBMConstructedSources.clockPath ω s.toNNReal|
    |IBMConstructedSources.clockPath ω t.toNNReal| ∂InfiniteGaussian.gaussianProduct

theorem covariance_nonneg (n m : ℕ) (s t : ℝ) : 0 ≤ covariance n m s t :=
  integral_nonneg fun _ => overlap_nonneg _ _ _ _

theorem covariance_measurable (n m : ℕ) :
    Measurable (fun p : ℝ × ℝ => covariance n m p.1 p.2) := by
  let F : (ℝ × ℝ) → InfiniteGaussian.SampleSpace → ℝ := fun p ω =>
    overlap n m |IBMConstructedSources.clockPath ω p.1.toNNReal|
      |IBMConstructedSources.clockPath ω p.2.toNNReal|
  have hm : Measurable (Function.uncurry F) := by
    apply measurable_uncurry_of_continuous_of_measurable
    · intro ω
      exact (overlap_continuous n m).comp
        ((((IBMConstructedSources.clockPath ω).continuous.comp
          (continuous_real_toNNReal.comp continuous_fst)).abs).prodMk
          (((IBMConstructedSources.clockPath ω).continuous.comp
            (continuous_real_toNNReal.comp continuous_snd)).abs))
    · intro p
      have h₁ : Measurable (fun ω => |IBMConstructedSources.clockPath ω p.1.toNNReal|) :=
        continuous_abs.measurable.comp ((ContinuousMap.measurable_eval p.1.toNNReal).comp
          IBMConstructedSources.clockPath_measurable)
      have h₂ : Measurable (fun ω => |IBMConstructedSources.clockPath ω p.2.toNNReal|) :=
        continuous_abs.measurable.comp ((ContinuousMap.measurable_eval p.2.toNNReal).comp
          IBMConstructedSources.clockPath_measurable)
      exact (overlap_continuous n m).measurable.comp
        (h₁.prodMk h₂)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem covariance_bounded (n m : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ s t, covariance n m s t ≤ M := by
  obtain ⟨M, hM0, hM⟩ := overlap_bounded n m
  refine ⟨M, hM0, fun s t => ?_⟩
  change (∫ ω, overlap n m |IBMConstructedSources.clockPath ω s.toNNReal|
    |IBMConstructedSources.clockPath ω t.toNNReal| ∂InfiniteGaussian.gaussianProduct) ≤ M
  calc
    _ ≤ ∫ _ω, M ∂InfiniteGaussian.gaussianProduct := integral_mono_of_nonneg
      (ae_of_all _ fun ω => overlap_nonneg n m _ _) (integrable_const M)
      (ae_of_all _ fun ω => hM _ _)
    _ = _ := by simp

theorem covariance_integrable (n m : ℕ) (T : ℝ) :
    Integrable (fun p : ℝ × ℝ => covariance n m p.1 p.2) ((window T).prod (window T)) := by
  obtain ⟨M, _, hM⟩ := covariance_bounded n m
  apply Integrable.of_bound (covariance_measurable n m).aestronglyMeasurable M
  exact ae_of_all _ fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (covariance_nonneg _ _ _ _)]
    exact hM _ _

theorem overlap_swap (n m : ℕ) (r q : ℝ) : overlap n m r q = overlap m n q r := by
  unfold overlap
  apply integral_congr_ae
  exact ae_of_all _ fun _ => mul_comm _ _

theorem covariance_swap (n m : ℕ) (s t : ℝ) : covariance n m s t = covariance m n t s := by
  unfold covariance
  exact integral_congr_ae (ae_of_all _ fun _ => overlap_swap _ _ _ _)

theorem covariance_off_diagonal_le (n m : ℕ) {T s t : ℝ}
    (hs : s ∈ Ioc 0 T) (ht : t ∈ Ioc 0 T) (hne : s ≠ t) :
    covariance n m s t ≤ 2 * peak 1 * timeKernel T s t := by
  have hpos (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) (i j : ℕ) :
      covariance i j a b ≤ 2 * peak (nndist b a) := by
    have he : a.toNNReal < b.toNNReal := by
      apply NNReal.coe_lt_coe.mp
      simpa only [Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb] using hab
    simpa only [covariance, Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb] using
      clockPath_overlap_le i j a.toNNReal b.toNNReal he
  rw [timeKernel_off_diagonal hs ht hne]
  rcases lt_or_gt_of_ne hne with hst | hts
  · have h := hpos s t hs.1.le ht.1.le hst n m
    rw [peak_nndist] at h
    nlinarith
  · rw [covariance_swap]
    have h := hpos t s ht.1.le hs.1.le hts m n
    rw [peak_nndist, abs_sub_comm] at h
    nlinarith

theorem window_off_diagonal (T : ℝ) :
    ∀ᵐ p : ℝ × ℝ ∂(window T).prod (window T), p.1 ≠ p.2 := by
  have h := DiagonalAmbientNullity.ae_off_diagonal
  simp only [DiagonalAmbientNullity.plane, DiagonalAmbientNullity.diagonal, mem_ofPred_eq] at h
  rw [window, Measure.prod_restrict]
  exact ae_restrict_of_ae h

theorem covariance_integral_bound (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : ℝ × ℝ, covariance n m p.1 p.2 ∂(window T).prod (window T)) ≤
      8 * peak 1 * T * Real.sqrt T := by
  have hmem : ∀ᵐ p : ℝ × ℝ ∂(window T).prod (window T),
      p.1 ∈ Ioc 0 T ∧ p.2 ∈ Ioc 0 T := by
    rw [window, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  calc
    _ ≤ ∫ p : ℝ × ℝ, (2 * peak 1) * timeKernel T p.1 p.2 ∂(window T).prod (window T) := by
      apply integral_mono_ae (covariance_integrable n m T) ((timeKernel_integrable hT).const_mul _)
      filter_upwards [hmem, window_off_diagonal T] with p hp hne
      exact covariance_off_diagonal_le n m hp.1 hp.2 hne
    _ = (2 * peak 1) * ∫ p : ℝ × ℝ, timeKernel T p.1 p.2 ∂(window T).prod (window T) :=
      integral_const_mul _ _
    _ ≤ (2 * peak 1) * (4 * T * Real.sqrt T) :=
      mul_le_mul_of_nonneg_left (timeKernel_integral_bound hT)
        (mul_nonneg (by norm_num) (peak_nonneg 1))
    _ = _ := by ring

theorem window_pair_mem (T : ℝ) : ∀ᵐ p : ℝ × ℝ ∂(window T).prod (window T),
    p.1 ∈ Ioc 0 T ∧ p.2 ∈ Ioc 0 T := by
  rw [window, Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)

def weightedCovariance (n m : ℕ) (s t : ℝ) : ℝ := min s t * covariance n m s t

theorem weightedCovariance_integrable (n m : ℕ) {T : ℝ} (_hT : 0 ≤ T) :
    Integrable (fun p : ℝ × ℝ => weightedCovariance n m p.1 p.2)
      ((window T).prod (window T)) := by
  apply ((covariance_integrable n m T).const_mul T).mono'
    (((measurable_fst.min measurable_snd).mul (covariance_measurable n m)).aestronglyMeasurable)
  filter_upwards [window_pair_mem T] with p hp
  have hmin : 0 ≤ min p.1 p.2 := le_min hp.1.1.le hp.2.1.le
  have hmax : min p.1 p.2 ≤ T := (min_le_left _ _).trans hp.1.2
  change ‖min p.1 p.2 * covariance n m p.1 p.2‖ ≤ T * covariance n m p.1 p.2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hmin (covariance_nonneg _ _ _ _))]
  exact mul_le_mul_of_nonneg_right hmax (covariance_nonneg _ _ _ _)

theorem weightedCovariance_integral_bound (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : ℝ × ℝ, weightedCovariance n m p.1 p.2 ∂(window T).prod (window T)) ≤
      8 * peak 1 * T ^ 2 * Real.sqrt T := by
  calc
    _ ≤ ∫ p : ℝ × ℝ, T * covariance n m p.1 p.2 ∂(window T).prod (window T) := by
      apply integral_mono_ae (weightedCovariance_integrable n m hT)
        ((covariance_integrable n m T).const_mul T)
      filter_upwards [window_pair_mem T] with p hp
      exact mul_le_mul_of_nonneg_right ((min_le_left p.1 p.2).trans hp.1.2)
        (covariance_nonneg _ _ _ _)
    _ = T * ∫ p : ℝ × ℝ, covariance n m p.1 p.2 ∂(window T).prod (window T) :=
      integral_const_mul _ _
    _ ≤ T * (8 * peak 1 * T * Real.sqrt T) :=
      mul_le_mul_of_nonneg_left (covariance_integral_bound n m hT) hT
    _ = _ := by ring

def signedColumn (n m : ℕ) (p : (ℝ × ℝ) × InfiniteGaussian.SampleSpace) : ℝ :=
  BrownianSignIntegral.signum (IBMConstructedSources.clockPath p.2 p.1.1.toNNReal) *
    BrownianSignIntegral.signum (IBMConstructedSources.clockPath p.2 p.1.2.toNNReal) *
    overlap n m |IBMConstructedSources.clockPath p.2 p.1.1.toNNReal|
      |IBMConstructedSources.clockPath p.2 p.1.2.toNNReal|

theorem signedColumn_measurable (n m : ℕ) : Measurable (signedColumn n m) := by
  have hclock : Measurable (fun p : ℝ × InfiniteGaussian.SampleSpace =>
      IBMConstructedSources.clockPath p.2 p.1.toNNReal) := by
    exact BrownianClockWeightedEnergy.sigma_measurable
  have hs : Measurable (fun p : (ℝ × ℝ) × InfiniteGaussian.SampleSpace =>
      IBMConstructedSources.clockPath p.2 p.1.1.toNNReal) :=
    hclock.comp (measurable_fst.fst.prodMk measurable_snd)
  have ht : Measurable (fun p : (ℝ × ℝ) × InfiniteGaussian.SampleSpace =>
      IBMConstructedSources.clockPath p.2 p.1.2.toNNReal) :=
    hclock.comp (measurable_fst.snd.prodMk measurable_snd)
  have hk : Measurable (fun p : (ℝ × ℝ) × InfiniteGaussian.SampleSpace =>
      overlap n m |IBMConstructedSources.clockPath p.2 p.1.1.toNNReal|
        |IBMConstructedSources.clockPath p.2 p.1.2.toNNReal|) :=
    (overlap_continuous n m).measurable.comp
    ((continuous_abs.measurable.comp hs).prodMk (continuous_abs.measurable.comp ht))
  exact ((BrownianSignIntegral.signum_measurable.comp hs).mul
    (BrownianSignIntegral.signum_measurable.comp ht)).mul hk

def signedCovariance (n m : ℕ) (s t : ℝ) : ℝ :=
  ∫ ω, signedColumn n m ((s,t),ω) ∂InfiniteGaussian.gaussianProduct

theorem signedCovariance_measurable (n m : ℕ) :
    Measurable (fun p : ℝ × ℝ => signedCovariance n m p.1 p.2) :=
  (signedColumn_measurable n m).stronglyMeasurable.integral_prod_right'.measurable

theorem signedCovariance_norm_le (n m : ℕ) (s t : ℝ) :
    ‖signedCovariance n m s t‖ ≤ covariance n m s t := by
  obtain ⟨M, _, hM⟩ := overlap_bounded n m
  have hs : Measurable (fun ω => |IBMConstructedSources.clockPath ω s.toNNReal|) :=
    continuous_abs.measurable.comp ((ContinuousMap.measurable_eval s.toNNReal).comp
      IBMConstructedSources.clockPath_measurable)
  have ht : Measurable (fun ω => |IBMConstructedSources.clockPath ω t.toNNReal|) :=
    continuous_abs.measurable.comp ((ContinuousMap.measurable_eval t.toNNReal).comp
      IBMConstructedSources.clockPath_measurable)
  have hi : Integrable (fun ω => overlap n m |IBMConstructedSources.clockPath ω s.toNNReal|
      |IBMConstructedSources.clockPath ω t.toNNReal|) InfiniteGaussian.gaussianProduct :=
    Integrable.of_bound ((overlap_continuous n m).measurable.comp (hs.prodMk ht)).aestronglyMeasurable M
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (overlap_nonneg _ _ _ _)]
        exact hM _ _)
  apply norm_integral_le_of_norm_le hi
  exact ae_of_all _ fun ω => by
    unfold signedColumn
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (overlap_nonneg n m _ _)]
    have hb := mul_le_mul (BrownianSignIntegral.signum_bound
        (IBMConstructedSources.clockPath ω s.toNNReal))
      (BrownianSignIntegral.signum_bound (IBMConstructedSources.clockPath ω t.toNNReal))
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    exact (mul_le_mul_of_nonneg_right hb (overlap_nonneg n m _ _)).trans_eq (by ring)

/-- The covariance kernel of the candidate reflected-clock derivative, including
the Brownian Cameron-Martin pairing. This definition does not assert membership
in the closed derivative graph. -/
def signedEnergyKernel (n m : ℕ) (s t : ℝ) : ℝ := min s t * signedCovariance n m s t

theorem signedEnergyKernel_time_pairing (n m : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    signedEnergyKernel n m s t =
      inner ℝ (GaussianTimeHilbert.timeVector s.toNNReal) (GaussianTimeHilbert.timeVector t.toNNReal) *
        signedCovariance n m s t := by
  rw [GaussianTimeHilbert.timeVector_inner, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht]
  rfl

theorem signedCovariance_coefficient_formula (n m : ℕ) (s t : ℝ) :
    signedCovariance n m s t =
      ∫ ω, BrownianSignIntegral.signum (IBMConstructedSources.clockPath ω s.toNNReal) *
        BrownianSignIntegral.signum (IBMConstructedSources.clockPath ω t.toNNReal) *
        inner ℝ (IBMGaussianSteinMoments.tripleCoefficient n
          |IBMConstructedSources.clockPath ω s.toNNReal| 1)
          (IBMGaussianSteinMoments.tripleCoefficient m
            |IBMConstructedSources.clockPath ω t.toNNReal| 1) ∂InfiniteGaussian.gaussianProduct := by
  unfold signedCovariance signedColumn
  simp_rw [overlap_eq_coefficient_inner]

theorem signedEnergyKernel_norm_le (n m : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖signedEnergyKernel n m s t‖ ≤ weightedCovariance n m s t := by
  rw [signedEnergyKernel, norm_mul, Real.norm_eq_abs, abs_of_nonneg (le_min hs ht)]
  exact mul_le_mul_of_nonneg_left (signedCovariance_norm_le n m s t) (le_min hs ht)

theorem signedEnergyKernel_integrable (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun p : ℝ × ℝ => signedEnergyKernel n m p.1 p.2)
      ((window T).prod (window T)) := by
  apply (weightedCovariance_integrable n m hT).mono'
    (((measurable_fst.min measurable_snd).mul (signedCovariance_measurable n m)).aestronglyMeasurable)
  filter_upwards [window_pair_mem T] with p hp
  exact signedEnergyKernel_norm_le n m hp.1.1.le hp.2.1.le

/-- Uniform absolute integrability of the genuine signed two-time covariance.
The bound is independent of both mollifier widths. -/
theorem signedEnergyKernel_integral_norm_bound (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ p : ℝ × ℝ, ‖signedEnergyKernel n m p.1 p.2‖ ∂(window T).prod (window T)) ≤
      8 * peak 1 * T ^ 2 * Real.sqrt T := by
  apply le_trans ?_ (weightedCovariance_integral_bound n m hT)
  apply integral_mono_ae (signedEnergyKernel_integrable n m hT).norm
    (weightedCovariance_integrable n m hT)
  filter_upwards [window_pair_mem T] with p hp
  exact signedEnergyKernel_norm_le n m hp.1.1.le hp.2.1.le

end OperatorDerivativeRewrite.Foundation.IBMClockOverlapEnergy
