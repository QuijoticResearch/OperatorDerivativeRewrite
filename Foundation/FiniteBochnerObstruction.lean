import Foundation.AnisotropicMixedThreshold
/-! A finite exponential-multiplier obstruction. Positive zero-sum energy
forces a negative sampled quadratic form at some positive time, by the
right derivative of the exponential energy at zero. In particular every
active superquadratic coordinate in the anisotropic stable symbol fails
finite positive definiteness of its heat multiplier at some time. An explicit
cubic example uses time log(10/9). This does not by itself identify a
physical-space Markov semigroup or a stochastic process. -/
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace
open Filter Set
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteBochnerObstruction

def tri : Fin 3 → ℤ := ![0,1,2]
def c : Fin 3 → ℝ := ![1,-2,1]
def time : ℝ := Real.log (10/9)
def multiplier (t : ℝ) (i j : Fin 3) : ℝ :=
  Real.exp (-t * |((tri j-tri i : ℤ) : ℝ)|^3)

theorem time_pos : 0 < time := by
  exact Real.log_pos (by norm_num : (1:ℝ)<10/9)

theorem exp_time : Real.exp (-time) = (9/10 : ℝ) := by
  rw [time,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<10/9)]
  norm_num

theorem exp_eight : Real.exp (-time*8) = (9/10 : ℝ)^8 := by
  have h : -time*8 = (8:ℕ)*(-time) := by ring
  rw [h,Real.exp_nat_mul,exp_time]

theorem negative_energy :
    AnchoredCovariance.energy (multiplier time) c < 0 := by
  have he : Real.exp (-(time*8)) = (9/10 : ℝ)^8 := by
    simpa only [neg_mul] using exp_eight
  unfold AnchoredCovariance.energy multiplier c tri
  norm_num [Fin.sum_univ_succ,Real.exp_zero,exp_time,he]

theorem multiplier_not_psd :
    ¬ Matrix.PosSemidef (multiplier time) := by
  intro h
  have hh : 0 ≤ AnchoredCovariance.energy (multiplier time) c := by
    simpa only [AnchoredCovariance.energy,dotProduct,Matrix.mulVec,
      Pi.star_apply,star_trivial,Finset.mul_sum,mul_assoc,
      mul_left_comm,mul_comm] using h.dotProduct_mulVec_nonneg c
  exact (not_le_of_gt negative_energy) hh

def expEnergy (d : Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * Real.exp (-t*d i j)

theorem expEnergy_deriv (d : Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ) :
    HasDerivAt (expEnergy d w) (-AnchoredCovariance.energy d w) 0 := by
  have ht (i j : Fin 3) : HasDerivAt
      (fun t : ℝ => w i * w j * Real.exp (-t*d i j))
      (-(w i*w j*d i j)) 0 := by
    have hl : HasDerivAt (fun t : ℝ => -t*d i j) (-(d i j)) 0 := by
      convert (hasDerivAt_id (0:ℝ)).neg.mul_const (d i j) using 1
      · funext t; simp [id]
      · ring
    convert ((Real.hasDerivAt_exp (-(0:ℝ)*d i j)).comp 0 hl).const_mul (w i*w j) using 1 <;>
      simp
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht i j))
  change HasDerivAt (fun t : ℝ => ∑ i, ∑ j, w i*w j*Real.exp (-t*d i j))
    (-∑ i, ∑ j, w i*w j*d i j) 0
  simpa only [Finset.sum_neg_distrib] using h

theorem expEnergy_zero (d : Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (hw : ∑ i, w i = 0) : expEnergy d w 0 = 0 := by
  calc
    expEnergy d w 0 = (∑ i, w i) * (∑ j, w j) := by
      simp only [expEnergy,zero_mul,neg_zero,Real.exp_zero,mul_one]
      change (∑ i, ∑ j, w i * w j) = _
      exact (Fintype.sum_mul_sum w w).symm
    _ = 0 := by rw [hw]; ring

theorem expEnergy_eventually_negative (d : Fin 3 → Fin 3 → ℝ)
    (w : Fin 3 → ℝ) (hw : ∑ i, w i = 0)
    (hd : 0 < AnchoredCovariance.energy d w) :
    ∃ t : ℝ, 0 < t ∧ expEnergy d w t < 0 := by
  have hlim := (expEnergy_deriv d w).tendsto_slope_zero_right
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),
      t⁻¹ * expEnergy d w t < 0 := by
    have h := hlim.eventually (Iio_mem_nhds (neg_lt_zero.mpr hd))
    simpa [expEnergy_zero d w hw] using h
  obtain ⟨t, hn, ht⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨t,ht,?_⟩
  by_contra hnot
  have hf : 0 ≤ expEnergy d w t := le_of_not_gt hnot
  have hm := mul_nonneg (inv_pos.mpr ht).le hf
  linarith

theorem non_psd_at_some_time (d : Fin 3 → Fin 3 → ℝ)
    (w : Fin 3 → ℝ) (hw : ∑ i, w i = 0)
    (hd : 0 < AnchoredCovariance.energy d w) :
    ∃ t : ℝ, 0 < t ∧
      ¬ Matrix.PosSemidef (fun i j => Real.exp (-t*d i j)) := by
  obtain ⟨t,ht,hn⟩ := expEnergy_eventually_negative d w hw hd
  refine ⟨t,ht,?_⟩
  intro hp
  have hnonneg : 0 ≤ expEnergy d w t := by
    simpa only [expEnergy,dotProduct,Matrix.mulVec,Pi.star_apply,
      star_trivial,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using
      hp.dotProduct_mulVec_nonneg w
  linarith

theorem mixed_active_not_psd (a γ : Fin 3 → ℝ)
    (hγ0 : ∀ j, 0 < γ j) (j : Fin 3) (ha : 0 < a j)
    (hγgt : 2 < γ j) :
    ∃ t : ℝ, 0 < t ∧
      ¬ Matrix.PosSemidef (fun i l : Fin 3 => Real.exp
        (-t * AnisotropicStableGamma.anisotropicSymbol a γ
          (AnisotropicMixedThreshold.axisTriple j l-
            AnisotropicMixedThreshold.axisTriple j i))) := by
  have hp : (4:ℝ) < 2^(γ j) := by
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hγgt
    norm_num at hh
    exact hh
  have hd : 0 < AnchoredCovariance.energy
      (fun i l => AnisotropicStableGamma.anisotropicSymbol a γ
        (AnisotropicMixedThreshold.axisTriple j l-
          AnisotropicMixedThreshold.axisTriple j i))
      AnisotropicStableEndpoint.tripleWeights := by
    rw [AnisotropicMixedThreshold.mixed_triple_energy a γ hγ0 j]
    apply mul_pos ha
    linarith
  exact non_psd_at_some_time _ _ AnisotropicStableEndpoint.triple_sum hd

end OperatorDerivativeRewrite.Foundation.FiniteBochnerObstruction
