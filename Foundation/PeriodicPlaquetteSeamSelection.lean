import Foundation.PeriodicPlaquetteScaleObstruction

/-! Exact center-seam selection rules for the actual periodic Wilson transfer.
The bounded measurable Markov iterates agree with native stationary L2 powers.
Every local plaquette is seam-even; first, second and mixed winding probes are
seam-odd. Their native cross-correlations vanish at every finite time lag and
finite real coupling. This separates these probes, not their relaxation rates:
no even-sector spectral gap or continuum mass gap follows. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open PeriodicSlabL2 PeriodicCenterSeam PeriodicGroundSeamParity PeriodicCurvatureVariance
namespace OperatorDerivativeRewrite.Foundation.PeriodicPlaquetteSeamSelection
attribute [local irreducible] boundaryHaar gaugeHaar kernel

theorem density_seam (β : ℝ) (g : GroundData β) (i : Fin 3) (U V : State) :
    g.density (flip i U) (flip i V)=g.density U V := by
  unfold GroundData.density
  rw [kernel_simultaneous,ground_invariant,ground_invariant]

theorem transfer_flip (β : ℝ) (g : GroundData β) (i : Fin 3) (f : State → ℝ) (U : State) :
    transfer g f (flip i U)=transfer g (fun V => f (flip i V)) U := by
  unfold transfer
  rw [g.transition_integral,g.transition_integral,ground_invariant]
  congr 1
  have h := (flip_haar_preserving i).integral_comp
    (MeasurableEquiv.mulLeft (seam i)).measurableEmbedding
    (fun V => kernel β (flip i U) V*(g.function V*f V))
  change (∫ V,kernel β (flip i U) (flip i V)*(g.function (flip i V)*f (flip i V)) ∂boundaryHaar)=_ at h
  simp_rw [kernel_simultaneous,ground_invariant] at h
  exact h.symm

theorem plaquette_even (i : Fin 3) (p : SpatialFace) (U : State) :
    plaquette p (flip i U)=plaquette p U := by
  unfold plaquette
  rw [PeriodicCenterSeam.spatial_word]

theorem even_odd_pairing_zero (β : ℝ) (g : GroundData β) (i : Fin 3) (f h : State → ℝ)
    (hf : ∀ U,f (flip i U)=f U) (hh : ∀ U,h (flip i U)= -h U) :
    (∫ U,f U*h U ∂g.stationary)=0 := by
  apply odd_mean_zero g i
  intro U
  rw [hf,hh]
  ring


def rawSteps {β : ℝ} (g : GroundData β) : ℕ → (State → ℝ) → State → ℝ
  | 0,f => f
  | n+1,f => transfer g (rawSteps g n f)

theorem rawSteps_measurable (β : ℝ) (g : GroundData β) (f : State → ℝ) (hf : Measurable f)
    (n : ℕ) : Measurable (rawSteps g n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact transfer_measurable g _ ih

theorem rawSteps_bound (β : ℝ) (g : GroundData β) (f : State → ℝ) (B : ℝ)
    (hb : ∀ U,|f U| ≤ B) (n : ℕ) (U : State) : |rawSteps g n f U| ≤ B := by
  induction n generalizing U with
  | zero => exact hb U
  | succ n ih => exact transfer_bound g _ B ih U

theorem rawSteps_memLp (β : ℝ) (g : GroundData β) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ U,|f U| ≤ B) (n : ℕ) : MemLp (rawSteps g n f) 2 g.stationary := by
  let := g.stationary_probability
  exact MemLp.of_bound (rawSteps_measurable β g f hf n).aestronglyMeasurable B
    (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using rawSteps_bound β g f B hb n U))

theorem native_steps_toLp (β : ℝ) (g : GroundData β) (f : State → ℝ) (hf : Measurable f)
    (hmem : MemLp f 2 g.stationary) (B : ℝ) (hb : ∀ U,|f U| ≤ B) (n : ℕ) :
    SelfAdjointContractionIteration.steps (operator g) n (hmem.toLp f)=
      (rawSteps_memLp β g f hf B hb n).toLp (rawSteps g n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change operator g (SelfAdjointContractionIteration.steps (operator g) n (hmem.toLp f))=_
    rw [ih,operator_toLp g (rawSteps g n f) (rawSteps_memLp β g f hf B hb n)
      (rawSteps_measurable β g f hf n) B (rawSteps_bound β g f B hb n)]
    rfl

theorem rawSteps_odd (β : ℝ) (g : GroundData β) (i : Fin 3) (h : State → ℝ)
    (hh : ∀ U,h (flip i U)= -h U) (n : ℕ) (U : State) :
    rawSteps g n h (flip i U)= -rawSteps g n h U := by
  induction n generalizing U with
  | zero => exact hh U
  | succ n ih =>
    change transfer g (rawSteps g n h) (flip i U)= -transfer g (rawSteps g n h) U
    rw [transfer_flip]
    unfold transfer
    simp_rw [ih,integral_neg]

theorem native_lag_pairing (β : ℝ) (g : GroundData β) (f h : State → ℝ)
    (hfL : MemLp f 2 g.stationary) (hhL : MemLp h 2 g.stationary)
    (hh : Measurable h) (C : ℝ) (hc : ∀ U,|h U| ≤ C) (n : ℕ) :
    inner ℝ (SelfAdjointContractionIteration.steps (operator g) n (hhL.toLp h)) (hfL.toLp f)=
      ∫ U,f U*rawSteps g n h U ∂g.stationary := by
  rw [native_steps_toLp β g h hh hhL C hc n,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (rawSteps_memLp β g h hh C hc n),MemLp.coeFn_toLp hfL] with U hH hF
  rw [hH,hF]
  rfl

theorem native_even_odd_lag_zero (β : ℝ) (g : GroundData β) (i : Fin 3) (f h : State → ℝ)
    (hfL : MemLp f 2 g.stationary) (hhL : MemLp h 2 g.stationary)
    (hh : Measurable h) (C : ℝ) (hc : ∀ U,|h U| ≤ C)
    (he : ∀ U,f (flip i U)=f U) (ho : ∀ U,h (flip i U)= -h U) (n : ℕ) :
    inner ℝ (SelfAdjointContractionIteration.steps (operator g) n (hhL.toLp h)) (hfL.toLp f)=0 := by
  rw [native_lag_pairing β g f h hfL hhL hh C hc n]
  exact even_odd_pairing_zero β g i f (rawSteps g n h) he (rawSteps_odd β g i h ho n)


open PeriodicCurvatureTransfer PeriodicCenteredHolonomy
theorem plaquette_odd_lag_zero (β : ℝ) (g : GroundData β) (i : Fin 3) (p : SpatialFace)
    (h : State → ℝ) (hhL : MemLp h 2 g.stationary) (hh : Measurable h)
    (C : ℝ) (hc : ∀ U,|h U| ≤ C) (ho : ∀ U,h (flip i U)= -h U) (n : ℕ) :
    inner ℝ (SelfAdjointContractionIteration.steps (operator g) n (hhL.toLp h)) (normalized g p)=0 := by
  have he (U : State) : centered g p (flip i U)=centered g p U := by
    unfold centered
    rw [plaquette_even]
  have hz : inner ℝ (SelfAdjointContractionIteration.steps (operator g) n (hhL.toLp h)) (vector g p)=0 :=
    native_even_odd_lag_zero β g i (centered g p) h (centered_memLp g p) hhL hh C hc he ho n
  rw [normalized,real_inner_smul_right,hz,mul_zero]

theorem first_winding_lag_zero (β : ℝ) (g : GroundData β) (p : SpatialFace) (n : ℕ) :
    inner ℝ (SelfAdjointContractionIteration.steps (operator g) n ((first_memLp g).toLp first))
      (normalized g p)=0 :=
  plaquette_odd_lag_zero β g 0 p first (first_memLp g) first_measurable 1
    (fun _ => halfTrace_bound _) first_odd n

theorem second_winding_lag_zero (β : ℝ) (g : GroundData β) (p : SpatialFace) (n : ℕ) :
    inner ℝ (SelfAdjointContractionIteration.steps (operator g) n ((second_memLp g).toLp second))
      (normalized g p)=0 :=
  plaquette_odd_lag_zero β g 1 p second (second_memLp g) second_measurable 1
    (fun _ => halfTrace_bound _) second_odd n

theorem mixed_winding_lag_zero (β : ℝ) (g : GroundData β) (p : SpatialFace) (n : ℕ) :
    inner ℝ (SelfAdjointContractionIteration.steps (operator g) n ((mixed_memLp g).toLp mixed))
      (normalized g p)=0 :=
  plaquette_odd_lag_zero β g 0 p mixed (mixed_memLp g) mixed_measurable 1
    (fun _ => halfTrace_bound _) mixed_odd n

end OperatorDerivativeRewrite.Foundation.PeriodicPlaquetteSeamSelection
