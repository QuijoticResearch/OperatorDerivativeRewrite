import Foundation.PeriodicCenterSeam
import Foundation.PeriodicGroundHarmonic

/-! Parity of every actual positive periodic ground, proved from its own
Markov transition and the existing bounded reset/mixing estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicGroundSeamParity
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicCenterSeam
open PeriodicGroundHarmonic
variable {beta : ℝ} (g : GroundData beta)

theorem flipped_eigen (i : Fin 3) (U : State) :
    (∫ V,kernel beta U V*g.function (flip i V) ∂boundaryHaar)=g.value*g.function (flip i U) := by
  have h := (flip_haar_preserving i).integral_comp
    (MeasurableEquiv.mulLeft (seam i)).measurableEmbedding
    (fun V => kernel beta (flip i U) V*g.function V)
  change (∫ V,kernel beta (flip i U) (flip i V)*g.function (flip i V) ∂boundaryHaar)=_ at h
  simp_rw [kernel_simultaneous] at h
  exact h.trans (g.eigen (flip i U))

def ratio (i : Fin 3) (U : State) : ℝ := g.function (flip i U)/g.function U

theorem ratio_pos (i : Fin 3) (U : State) : 0 < ratio g i U :=
  div_pos (g.function_pos _) (g.function_pos _)

theorem ratio_measurable (i : Fin 3) : Measurable (ratio g i) :=
  (g.measurable.comp (flip_measurable i)).div g.measurable

theorem ratio_bound (i : Fin 3) (U : State) : |ratio g i U| ≤ g.upper/g.lower := by
  rw [abs_of_pos (ratio_pos g i U)]
  unfold ratio
  have hu : g.function (flip i U) ≤ g.upper := (le_abs_self _).trans (g.bounds _).2
  have hup : 0 < g.upper := (g.function_pos _).trans_le hu
  exact (div_le_div_of_nonneg_right hu (g.function_pos U).le).trans
    (div_le_div_of_nonneg_left hup.le g.lower_pos (g.bounds U).1)

theorem ratio_harmonic (i : Fin 3) (U : State) :
    YMPositiveKernel.average boundaryHaar g.density (ratio g i) U=ratio g i U := by
  rw [average_transition,g.transition_integral]
  have hp (V : State) : g.function V*ratio g i V=g.function (flip i V) := by
    unfold ratio
    field_simp [(g.function_pos V).ne']
  simp_rw [hp]
  rw [flipped_eigen]
  unfold ratio
  field_simp [g.value_pos.ne',(g.function_pos U).ne']

theorem ground_invariant (i : Fin 3) (U : State) : g.function (flip i U)=g.function U := by
  letI : IsProbabilityMeasure g.stationary := g.stationary_probability
  letI : IsMarkovKernel g.transition := g.transition_markov
  let r := ratio g i
  let m : ℝ := ∫ V,r V ∂g.stationary
  let f : State → ℝ := fun V => r V-m
  have hr : Measurable r := ratio_measurable g i
  have hbound (V : State) : |r V| ≤ g.upper/g.lower := ratio_bound g i V
  have hi : Integrable r g.stationary := Integrable.of_bound hr.aestronglyMeasurable
    (g.upper/g.lower) (ae_of_all _ hbound)
  have hf : Measurable f := hr.sub measurable_const
  have hz : (∫ V,f V ∂g.stationary)=0 := by
    change (∫ V,r V-m ∂g.stationary)=0
    rw [integral_sub hi (integrable_const m),integral_const,probReal_univ,one_smul]
    exact sub_self m
  have hb (V : State) : |f V| ≤ g.upper/g.lower+|m| := by
    have h := abs_sub_le (r V) 0 m
    simp only [sub_zero,zero_sub,abs_neg] at h
    exact h.trans (add_le_add (hbound V) le_rfl)
  have hh (V : State) : YMPositiveKernel.average boundaryHaar g.density f V=f V := by
    rw [average_transition]
    have hir : Integrable r (g.transition V) := Integrable.of_bound hr.aestronglyMeasurable
      (g.upper/g.lower) (ae_of_all _ hbound)
    change (∫ W,r W-m ∂g.transition V)=r V-m
    rw [integral_sub hir (integrable_const m),integral_const,probReal_univ,one_smul]
    exact congrArg (fun x : ℝ => x-m)
      ((average_transition g r V).symm.trans (ratio_harmonic g i V))
  have hc (V : State) : ratio g i V=m :=
    sub_eq_zero.mp (centered_harmonic_zero g f hf hz _ hb hh V)
  have hm : 0 < m := (ratio_pos g i 1).trans_eq (hc 1)
  have hp : ratio g i (flip i (1 : State))*ratio g i 1=1 := by
    unfold ratio
    rw [flip_involutive]
    field_simp [(g.function_pos (1 : State)).ne',(g.function_pos (flip i (1 : State))).ne']
  rw [hc,hc] at hp
  have hm1 : m=1 := by nlinarith
  have hU := hc U
  rw [hm1] at hU
  exact (div_eq_iff (g.function_pos U).ne').mp hU |>.trans (one_mul _)

theorem stationary_integral_flip (i : Fin 3) (f : State → ℝ) :
    (∫ U,f (flip i U) ∂g.stationary)=∫ U,f U ∂g.stationary := by
  rw [g.stationary_integral,g.stationary_integral]
  have h := (flip_haar_preserving i).integral_comp
    (MeasurableEquiv.mulLeft (seam i)).measurableEmbedding
    (fun U => g.function U^2*f U)
  change (∫ U,g.function (flip i U)^2*f (flip i U) ∂boundaryHaar)=_ at h
  simp_rw [ground_invariant] at h
  rw [h]

theorem stationary_preserving (i : Fin 3) :
    MeasurePreserving (flip i) g.stationary g.stationary := by
  letI : IsProbabilityMeasure g.stationary := g.stationary_probability
  refine ⟨flip_measurable i,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (flip_measurable i) hs]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have h := stationary_integral_flip g i (s.indicator (fun _ => (1 : ℝ)))
  have hp : (fun U => s.indicator (fun _ => (1 : ℝ)) (flip i U))=
      (flip i ⁻¹' s).indicator (fun _ => (1 : ℝ)) := rfl
  rw [hp] at h
  have hi (t : Set State) (ht : MeasurableSet t) :
      (∫ U,t.indicator (fun _ => (1 : ℝ)) U ∂g.stationary)=g.stationary.real t :=
    integral_indicator_one ht
  rw [hi _ ((flip_measurable i) hs),hi s hs] at h
  exact h

theorem odd_mean_zero (i : Fin 3) (f : State → ℝ)
    (hf : ∀ U,f (flip i U)= -f U) : (∫ U,f U ∂g.stationary)=0 := by
  have h := stationary_integral_flip g i f
  simp_rw [hf] at h
  rw [integral_neg] at h
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicGroundSeamParity
