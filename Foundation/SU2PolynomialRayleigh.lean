import Foundation.SU2TiltEnergyResponse

/-! Actual trace-metric energies and first Rayleigh responses for r+a*r² on SU(2).
These are individual test quotients, not the infimum defining a spectral gap. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Quaternion Matrix Matrix.Norms.Operator Topology
namespace OperatorDerivativeRewrite.Foundation.SU2PolynomialRayleigh
open QuaternionSU2Representation SU2TraceHessianModel SU2TiltEnergyResponse
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def observable (a : ℝ) (A : SU2) : ℝ := halfTrace A+a*halfTrace A^2

def observableCurve (a : ℝ) (U : M2) (j : Fin 3) (t : ℝ) : ℝ :=
  traceCurve U j t+a*(traceCurve U j t)^2

theorem observableCurve_derivative (a : ℝ) (U : M2) (j : Fin 3) :
    HasDerivAt (observableCurve a U j)
      ((1+2*a*(traceReal U/2))*traceSlope U j) 0 := by
  have hd := traceCurve_derivative U j
  have hf := hd.add ((hd.pow 2).const_mul a)
  have hz : traceCurve U j 0=traceReal U/2 := by simp [traceCurve]
  rw [hz] at hf
  convert hf using 1 <;> first | rfl | (norm_num; ring)

def frameEnergy (a : ℝ) (A : SU2) : ℝ :=
  ∑ j : Fin 3, (deriv (observableCurve a (A : M2) j) 0)^2

def shape (a r : ℝ) : ℝ := (1+2*a*r)^2*(1-r^2)/4

theorem frameEnergy_shape (a : ℝ) (A : SU2) : frameEnergy a A=shape a (halfTrace A) := by
  obtain ⟨u, rfl⟩ := hom_surjective A
  have hn : Quaternion.normSq (u : ℍ)=1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, one_mul]
  have hi : (u : ℍ).imJ^2+(u : ℍ).imK^2+(u : ℍ).imI^2=1-(u : ℍ).re^2 := by
    rw [Quaternion.normSq_def'] at hn
    linarith
  simp only [frameEnergy, (observableCurve_derivative _ _ _).deriv, halfTrace_map]
  change (∑ j : Fin 3,
    ((1+2*a*(traceReal (QuaternionSU2Representation.repr (u : ℍ))/2))*
      traceSlope (QuaternionSU2Representation.repr (u : ℍ)) j)^2) = _
  simp [repr_halfTrace, traceSlope_repr, imagCoord, Fin.sum_univ_three]
  calc
    _ = (1+2*a*(u : ℍ).re)^2*((u : ℍ).imJ^2+(u : ℍ).imK^2+(u : ℍ).imI^2)/4 := by ring
    _ = _ := by rw [hi]; rfl

theorem observable_measurable (a : ℝ) : Measurable (observable a) :=
  halfTrace_measurable.add (measurable_const.mul (halfTrace_measurable.pow_const 2))

theorem observable_bound (a : ℝ) (A : SU2) : |observable a A| ≤ 1+|a| := by
  have hr := halfTrace_bound A
  have hs : |halfTrace A^2| ≤ 1 := by
    simpa only [abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hr 2
  unfold observable
  calc
    _ ≤ |halfTrace A|+|a*halfTrace A^2| := abs_add_le _ _
    _ ≤ 1+|a| := by rw [abs_mul]; nlinarith [abs_nonneg a]

theorem shape_bound (a r : ℝ) (hr : |r| ≤ 1) :
    0 ≤ shape a r ∧ shape a r ≤ (1+2*|a|)^2/4 := by
  have hs : r^2 ≤ 1 := (sq_le_one_iff_abs_le_one r).mpr hr
  have ha : |1+2*a*r| ≤ 1+2*|a| := by
    calc
      _ ≤ |(1 : ℝ)|+|2*a*r| := abs_add_le _ _
      _ ≤ 1+2*|a| := by rw [abs_mul, abs_mul]; norm_num; nlinarith [abs_nonneg a]
  have hf : (1+2*a*r)^2 ≤ (1+2*|a|)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hp := mul_le_mul hf (show 1-r^2 ≤ 1 by nlinarith)
    (by linarith : 0 ≤ 1-r^2) (sq_nonneg (1+2*|a|))
  constructor
  · unfold shape; positivity
  · unfold shape; nlinarith

theorem frameEnergy_measurable (a : ℝ) : Measurable (frameEnergy a) := by
  have he : frameEnergy a=fun A => shape a (halfTrace A) := funext (frameEnergy_shape a)
  rw [he]
  have hf : Measurable (shape a) := by unfold shape; fun_prop
  exact hf.comp halfTrace_measurable

theorem frameEnergy_bound (a : ℝ) (A : SU2) :
    |frameEnergy a A| ≤ (1+2*|a|)^2/4 := by
  rw [frameEnergy_shape, abs_of_nonneg (shape_bound a _ (halfTrace_bound A)).1]
  exact (shape_bound a _ (halfTrace_bound A)).2

section Haar
variable (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]

/-- A reusable evaluator for actual Haar polynomial integrals through degree five. -/
theorem polynomial_mean (c : Fin 6 → ℝ) :
    (∫ A, ∑ k : Fin 6, c k*halfTrace A^(k : ℕ) ∂ν)=c 0+c 2/4+c 4/8 := by
  rw [integral_finsetSum _ (fun (k : Fin 6) _ =>
    (power_integrable ν (k : ℕ)).const_mul (c k))]
  simp_rw [integral_const_mul]
  obtain ⟨h1,h2,h3,h4,h5⟩ := moment_values ν
  simp [Fin.sum_univ_succ, h1,h2,h3,h4,h5] <;> ring

theorem mean_of_polynomial (f : ℝ → ℝ) (c : Fin 6 → ℝ)
    (hf : ∀ r, f r=∑ k : Fin 6, c k*r^(k : ℕ)) :
    (∫ A, f (halfTrace A) ∂ν)=c 0+c 2/4+c 4/8 := by
  simp_rw [hf]
  exact polynomial_mean ν c

theorem observable_mean (a : ℝ) : (∫ A, observable a A ∂ν)=a/4 := by
  have h := mean_of_polynomial ν (fun r => r+a*r^2) ![0,1,a,0,0,0]
    (by intro r; simp [Fin.sum_univ_succ])
  simpa [observable] using h

theorem observable_cross_mean (a : ℝ) : (∫ A, observable a A*halfTrace A ∂ν)=1/4 := by
  have h := mean_of_polynomial ν (fun r => (r+a*r^2)*r) ![0,0,1,a,0,0]
    (by intro r; simp [Fin.sum_univ_succ]; ring)
  simpa [observable] using h

theorem observable_square_mean (a : ℝ) : (∫ A, (observable a A)^2 ∂ν)=(2+a^2)/8 := by
  have h := mean_of_polynomial ν (fun r => (r+a*r^2)^2) ![0,0,1,2*a,a^2,0]
    (by intro r; simp [Fin.sum_univ_succ]; ring)
  simp only [observable] at *
  rw [h]
  norm_num <;> ring

theorem observable_square_cross_mean (a : ℝ) :
    (∫ A, (observable a A)^2*halfTrace A ∂ν)=a/4 := by
  have h := mean_of_polynomial ν (fun r => (r+a*r^2)^2*r) ![0,0,0,1,2*a,a^2]
    (by intro r; simp [Fin.sum_univ_succ]; ring)
  simp only [observable] at *
  rw [h]
  norm_num <;> ring

theorem energy_mean (a : ℝ) : (∫ A, frameEnergy a A ∂ν)=(3+2*a^2)/16 := by
  have h := mean_of_polynomial ν (shape a) ![1/4,a,a^2-1/4,-a,-a^2,0]
    (by intro r; simp [shape, Fin.sum_univ_succ]; ring)
  simp_rw [frameEnergy_shape]
  rw [h]
  norm_num <;> ring

theorem energy_cross_mean (a : ℝ) : (∫ A, frameEnergy a A*halfTrace A ∂ν)=a/8 := by
  have h := mean_of_polynomial ν (fun r => shape a r*r) ![0,1/4,a,a^2-1/4,-a,-a^2]
    (by intro r; simp [shape, Fin.sum_univ_succ]; ring)
  simp_rw [frameEnergy_shape]
  rw [h]
  norm_num <;> ring

def energy (a t : ℝ) : ℝ :=
  BoundedExponentialTiltResponse.expectation ν halfTrace (frameEnergy a) t
def variance (a t : ℝ) : ℝ :=
  BoundedExponentialTiltResponse.variance ν halfTrace (observable a) t
def rayleigh (a t : ℝ) : ℝ := energy ν a t / variance ν a t

theorem energy_zero (a : ℝ) : energy ν a 0=(3+2*a^2)/16 := by
  rw [energy, BoundedExponentialTiltResponse.expectation_zero, energy_mean]

theorem variance_zero (a : ℝ) : variance ν a 0=(4+a^2)/16 := by
  rw [variance, BoundedExponentialTiltResponse.variance,
    BoundedExponentialTiltResponse.expectation_zero,
    BoundedExponentialTiltResponse.expectation_zero, observable_square_mean, observable_mean]
  ring

theorem energy_derivative (a : ℝ) : HasDerivAt (energy ν a) (a/8) 0 := by
  have hd := BoundedExponentialTiltResponse.expectation_hasDerivAt_zero ν halfTrace
    (frameEnergy a) halfTrace_measurable (frameEnergy_measurable a) halfTrace_bound
    ((1+2*|a|)^2/4) (by positivity) (frameEnergy_bound a)
  rw [energy_cross_mean, (moment_values ν).1, mul_zero, sub_zero] at hd
  exact hd

theorem variance_derivative (a : ℝ) : HasDerivAt (variance ν a) (a/8) 0 := by
  have hd := BoundedExponentialTiltResponse.variance_hasDerivAt_zero ν halfTrace
    (observable a) halfTrace_measurable (observable_measurable a) halfTrace_bound
    (1+|a|) (by positivity) (observable_bound a)
  simp only [(moment_values ν).1, observable_mean, observable_cross_mean,
    observable_square_cross_mean, mul_zero, sub_zero] at hd
  convert hd using 1 <;> first | rfl | ring

theorem rayleigh_zero (a : ℝ) : rayleigh ν a 0=(3+2*a^2)/(4+a^2) := by
  rw [rayleigh, energy_zero, variance_zero]
  have hn : 4+a^2 ≠ 0 := by positivity
  field_simp [hn]
  <;> ring

theorem rayleigh_derivative (a : ℝ) :
    HasDerivAt (rayleigh ν a) (2*a*(1-a^2)/(4+a^2)^2) 0 := by
  have hv : variance ν a 0 ≠ 0 := by rw [variance_zero]; positivity
  have hd := (energy_derivative ν a).div (variance_derivative ν a) hv
  rw [energy_zero, variance_zero] at hd
  convert hd using 1 <;> first | rfl | (field_simp; ring)

theorem opposite_responses :
    HasDerivAt (rayleigh ν (1/2)) (12/289) 0 ∧
      HasDerivAt (rayleigh ν 2) (-3/16) 0 := by
  constructor
  · convert rayleigh_derivative ν (1/2) using 1 <;> norm_num
  · convert rayleigh_derivative ν 2 using 1 <;> norm_num

theorem positive_derivative_eventually (f : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt f d 0) (hpos : 0 < d) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f 0 < f t := by
  have hs := hd.tendsto_slope_zero_right.eventually (eventually_gt_nhds hpos)
  filter_upwards [hs, self_mem_nhdsWithin] with t hs ht
  simp only [zero_add, smul_eq_mul] at hs
  have htinv : 0 ≤ t⁻¹ := le_of_lt (inv_pos.mpr ht)
  by_contra h
  have hn : f t-f 0 ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
  have := mul_nonpos_of_nonneg_of_nonpos htinv hn
  linarith

theorem negative_derivative_eventually (f : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt f d 0) (hneg : d < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < f 0 := by
  have he := positive_derivative_eventually (fun t => -f t) (-d) hd.neg (by linarith)
  filter_upwards [he] with t ht
  linarith

theorem energy_variance_eventually_increase (a : ℝ) (ha : 0 < a) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), energy ν a 0 < energy ν a t ∧
      variance ν a 0 < variance ν a t := by
  have he := positive_derivative_eventually _ _ (energy_derivative ν a) (by positivity)
  have hv := positive_derivative_eventually _ _ (variance_derivative ν a) (by positivity)
  filter_upwards [he,hv] with t he hv using ⟨he,hv⟩

theorem rayleigh_eventually_increase (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), rayleigh ν a 0 < rayleigh ν a t := by
  apply positive_derivative_eventually _ _ (rayleigh_derivative ν a)
  have hs : 0 < 1-a^2 := by nlinarith
  positivity

theorem rayleigh_eventually_decrease (a : ℝ) (ha : 1 < a) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), rayleigh ν a t < rayleigh ν a 0 := by
  apply negative_derivative_eventually _ _ (rayleigh_derivative ν a)
  have ha0 : 0 < a := by linarith
  have hs : 1-a^2 < 0 := by nlinarith
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hs) (by positivity)

/-- At the same arbitrarily small positive tilt, both energies and variances
increase while the two individual Rayleigh quotients move in opposite directions. -/
theorem simultaneous_opposite_changes (ε : ℝ) (hε : 0 < ε) :
    ∃ t, 0 < t ∧ t < ε ∧
      energy ν (1/2) 0 < energy ν (1/2) t ∧
      variance ν (1/2) 0 < variance ν (1/2) t ∧
      rayleigh ν (1/2) 0 < rayleigh ν (1/2) t ∧
      energy ν 2 0 < energy ν 2 t ∧ variance ν 2 0 < variance ν 2 t ∧
      rayleigh ν 2 t < rayleigh ν 2 0 := by
  have he := energy_variance_eventually_increase ν (1/2) (by norm_num)
  have hv := energy_variance_eventually_increase ν 2 (by norm_num)
  have hq := rayleigh_eventually_increase ν (1/2) (by norm_num) (by norm_num)
  have hr := rayleigh_eventually_decrease ν 2 (by norm_num)
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε :=
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < ε ∧
      energy ν (1/2) 0 < energy ν (1/2) t ∧
      variance ν (1/2) 0 < variance ν (1/2) t ∧
      rayleigh ν (1/2) 0 < rayleigh ν (1/2) t ∧
      energy ν 2 0 < energy ν 2 t ∧ variance ν 2 0 < variance ν 2 t ∧
      rayleigh ν 2 t < rayleigh ν 2 0 := by
    filter_upwards [he,hv,hq,hr,hb,self_mem_nhdsWithin] with t he hv hq hr hb ht
    exact ⟨ht,hb,he.1,he.2,hq,hv.1,hv.2,hr⟩
  exact hall.exists

end Haar
end OperatorDerivativeRewrite.Foundation.SU2PolynomialRayleigh
