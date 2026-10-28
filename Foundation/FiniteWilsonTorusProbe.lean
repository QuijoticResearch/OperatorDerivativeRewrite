import Foundation.FiniteWilsonTorusStationary

/-! Centered winding probe in the realized homogeneous torus stationary law.
No full SU2/4D comparison or infinite-volume spectral claim is made. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusProbe
open FiniteWilsonTorusKernel FiniteWilsonTorusStationary

def probe (i : State) : ℝ := if i=0 ∨ i=16 then 1 else if i=8 ∨ i=24 then -1 else 0

def average (f : State → ℝ) (i : State) : ℝ := ∑ j,step i j*f j

def mean (f : State → ℝ) : ℝ := ∑ i,stationary i*f i

def secondMoment (f : State → ℝ) : ℝ := ∑ i,stationary i*f i^2

def lagPairing (f : State → ℝ) : ℝ := ∑ i,stationary i*f i*average f i

private def flat (i : Fin 4) : State := ![0,8,16,24] i

private theorem flat_average (i : Fin 4) :
    average probe (flat i)=probe (flat i)*(225/256)/FiniteWilsonTorusGround.value := by
  have hg := FiniteWilsonTorusGround.ground_positive 0
  have hv := FiniteWilsonTorusGround.value_pos
  fin_cases i <;>
    norm_num [average,probe,flat,step,transfer,amplitude,kinetic,count,difference,
      ground,orbit,Fin.sum_univ_succ] <;>
    field_simp [hg.ne',hv.ne'] <;> ring

theorem probe_mean : mean probe=0 := by
  norm_num [mean,probe,stationary,ground,orbit,Fin.sum_univ_succ]

theorem probe_secondMoment :
    secondMoment probe=4*FiniteWilsonTorusGround.ground 0^2/normalizer := by
  norm_num [secondMoment,probe,stationary,ground,orbit,Fin.sum_univ_succ]
  ring

theorem probe_secondMoment_pos : 0 < secondMoment probe := by
  rw [probe_secondMoment]
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos (FiniteWilsonTorusGround.ground_positive 0))) normalizer_pos

theorem probe_lag :
    lagPairing probe=(225/64)*FiniteWilsonTorusGround.ground 0^2/
      (FiniteWilsonTorusGround.value*normalizer) := by
  have h0 := flat_average 0
  have h1 := flat_average 1
  have h2 := flat_average 2
  have h3 := flat_average 3
  norm_num [flat,probe] at h0 h1 h2 h3
  norm_num [lagPairing,probe,Fin.sum_univ_succ]
  rw [h0,h1,h2,h3]
  norm_num [stationary,ground,orbit]
  ring

theorem probe_rayleigh : lagPairing probe/secondMoment probe=(225/256)/FiniteWilsonTorusGround.value := by
  rw [probe_lag,probe_secondMoment]
  field_simp [normalizer_pos.ne',(FiniteWilsonTorusGround.ground_positive 0).ne',
    FiniteWilsonTorusGround.value_pos.ne']
  <;> ring

theorem stationary_probe_above_quarter : (1/4:ℝ) < lagPairing probe/secondMoment probe := by
  rw [probe_rayleigh]
  exact FiniteWilsonTorusGround.flat_trial_scalar_margin

/-- The actual microscopic probe is invariant under all effective vertex gauges. -/
theorem probe_gauge (g : Fin 8) (u : Fin 256) :
    probe (FiniteWilsonTorusNoise.labelState (FiniteWilsonTorusNoise.gaugeAction g u)) =
      probe (FiniteWilsonTorusNoise.labelState u) := by
  rw [FiniteWilsonTorusNoise.label_gauge]

private def probeInt (i : State) : ℤ := if i=0 ∨ i=16 then 1 else if i=8 ∨ i=24 then -1 else 0

private theorem probe_cast (i : State) : (probeInt i:ℝ)=probe i := by
  unfold probeInt probe
  split_ifs <;> norm_num

private theorem bare_integer_pairing :
    (∑ i : State, ∑ j : State,probeInt i*(count (difference i j):ℤ)*probeInt j)=25600 := by decide

def bareMean (f : State → ℝ) : ℝ := (∑ i,f i)/32

def bareSecondMoment (f : State → ℝ) : ℝ := (∑ i,f i^2)/32

def bareLagPairing (f : State → ℝ) : ℝ := (∑ i,f i*(∑ j,kinetic i j*f j))/32

theorem bare_probe_mean : bareMean probe=0 := by norm_num [bareMean,probe,Fin.sum_univ_succ]

theorem bare_probe_secondMoment : bareSecondMoment probe=1/8 := by
  norm_num [bareSecondMoment,probe,Fin.sum_univ_succ]

theorem bare_probe_lag : bareLagPairing probe=25/2048 := by
  have h : (∑ i : State, ∑ j : State,(probeInt i:ℝ)*(count (difference i j):ℝ)*(probeInt j:ℝ))=25600 := by
    exact_mod_cast bare_integer_pairing
  simp only [probe_cast] at h
  have he : (∑ i,probe i*(∑ j,kinetic i j*probe j))=
      (∑ i : State,∑ j : State,probe i*(count (difference i j):ℝ)*probe j)/65536 := by
    unfold kinetic
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold bareLagPairing
  rw [he,h]
  norm_num

theorem bare_probe_rayleigh : bareLagPairing probe/bareSecondMoment probe=25/256 := by
  rw [bare_probe_lag,bare_probe_secondMoment]
  norm_num

/-- Actual centered observable-wise deterioration under literal equal spatial
Wilson weights. This does not yet assert the full bare centered spectral bound. -/
theorem homogeneous_probe_increases :
    bareLagPairing probe/bareSecondMoment probe < lagPairing probe/secondMoment probe := by
  rw [bare_probe_rayleigh]
  have h := stationary_probe_above_quarter
  linarith

end OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusProbe
