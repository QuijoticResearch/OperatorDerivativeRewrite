import Foundation.SU2StationaryMinorization
import Foundation.CauchyPoissonMixtureEntropy

noncomputable section
open MeasureTheory ProbabilityTheory Filter InformationTheory
open scoped ENNReal NNReal
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.MeasurableExponentialKernel
open OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel
open OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium
open OperatorDerivativeRewrite.Foundation.SU2StationaryMinorization

namespace OperatorDerivativeRewrite.Foundation.SU2ResidualEntropy

def reset (r : ℝ) : ℝ := Real.exp (-(4 * |r|)) / 2

theorem reset_pos (r : ℝ) : 0 < reset r := by
  unfold reset
  positivity

theorem reset_lt_one (r : ℝ) : reset r < 1 := by
  have he : Real.exp (-(4 * |r|)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg r])
  unfold reset
  linarith

theorem equilibriumDensity_nonneg (r : ℝ) (D : SU2) :
    0 ≤ equilibriumDensity r D := by
  unfold equilibriumDensity
  exact div_nonneg
    (MeasurableExponentialKernel.partition_positive law (interaction r) D
      (interaction_exp_integrable r D)).le
    (globalPartition_pos r).le

theorem equilibriumDensity_integrable (r : ℝ) :
    Integrable (equilibriumDensity r) law := by
  apply Integrable.mono' (integrable_const (Real.exp (2 * |r|)))
    (equilibriumDensity_measurable r).aestronglyMeasurable
  filter_upwards with D
  rw [Real.norm_eq_abs, abs_of_nonneg (equilibriumDensity_nonneg r D)]
  exact equilibriumDensity_upper r D

theorem equilibriumDensity_mass (r : ℝ) :
    (∫ D, equilibriumDensity r D ∂law) = 1 := by
  have hp := (equilibriumLaw_probability r).measure_univ
  rw [equilibriumLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at hp
  rw [← ofReal_integral_eq_lintegral_ofReal (equilibriumDensity_integrable r)
    (Eventually.of_forall (equilibriumDensity_nonneg r))] at hp
  have := congrArg ENNReal.toReal hp
  have hn : 0 ≤ ∫ D, equilibriumDensity r D ∂law :=
    integral_nonneg (equilibriumDensity_nonneg r)
  simpa [ENNReal.toReal_ofReal hn] using this

def residualDensity (r : ℝ) (C D : SU2) : ℝ :=
  (MeasurableExponentialKernel.density law (interaction r) C D -
    reset r * equilibriumDensity r D) / (1 - reset r)

theorem residualDensity_measurable (r : ℝ) :
    Measurable (Function.uncurry (residualDensity r)) := by
  change Measurable (fun p : SU2 × SU2 =>
    (MeasurableExponentialKernel.density law (interaction r) p.1 p.2 -
      reset r * equilibriumDensity r p.2) / (1 - reset r))
  exact ((MeasurableExponentialKernel.density_measurable law (interaction r)
    (interaction_measurable r)).sub
    (measurable_const.mul ((equilibriumDensity_measurable r).comp measurable_snd))).div_const _

theorem residualDensity_nonneg (r : ℝ) (C D : SU2) :
    0 ≤ residualDensity r C D := by
  apply div_nonneg _ (sub_pos.mpr (reset_lt_one r)).le
  apply sub_nonneg.mpr
  have hε : reset r ≤ Real.exp (-(4 * |r|)) := by
    unfold reset
    exact half_le_self (Real.exp_pos _).le
  calc
    reset r * equilibriumDensity r D ≤
        Real.exp (-(4 * |r|)) * equilibriumDensity r D :=
      mul_le_mul_of_nonneg_right hε (equilibriumDensity_nonneg r D)
    _ ≤ _ := stationary_density_minorization r C D

theorem residualDensity_integrable (r : ℝ) (C : SU2) :
    Integrable (residualDensity r C) law := by
  unfold residualDensity
  exact (((interaction_exp_integrable r C).div_const _).sub
    ((equilibriumDensity_integrable r).const_mul _)).div_const _

theorem residualDensity_mass (r : ℝ) (C : SU2) :
    (∫ D, residualDensity r C D ∂law) = 1 := by
  have hk : Integrable
      (MeasurableExponentialKernel.density law (interaction r) C) law :=
    (interaction_exp_integrable r C).div_const _
  unfold residualDensity
  rw [integral_div, integral_sub hk
    ((equilibriumDensity_integrable r).const_mul _), integral_const_mul,
    MeasurableExponentialKernel.density_integral law (interaction r) C
      (interaction_exp_integrable r C), equilibriumDensity_mass r]
  simpa using (div_self (ne_of_gt (sub_pos.mpr (reset_lt_one r))))

def residualKernel (r : ℝ) : Kernel SU2 SU2 :=
  (Kernel.const SU2 law).withDensity
    (fun C D => ENNReal.ofReal (residualDensity r C D))

theorem residualKernel_apply (r : ℝ) (C : SU2) :
    residualKernel r C =
      law.withDensity (fun D => ENNReal.ofReal (residualDensity r C D)) := by
  rw [residualKernel, Kernel.withDensity_apply _
    (residualDensity_measurable r).ennreal_ofReal]
  rfl

theorem residualKernel_markov (r : ℝ) : IsMarkovKernel (residualKernel r) := by
  constructor
  intro C
  constructor
  rw [residualKernel_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (residualDensity_integrable r C)
      (Eventually.of_forall (residualDensity_nonneg r C)),
    residualDensity_mass]
  norm_num

theorem residual_density_split (r : ℝ) (C D : SU2) :
    ENNReal.ofReal (reset r) * ENNReal.ofReal (equilibriumDensity r D) +
      ENNReal.ofReal (1 - reset r) * ENNReal.ofReal (residualDensity r C D) =
      ENNReal.ofReal (MeasurableExponentialKernel.density law (interaction r) C D) := by
  have hε0 : 0 ≤ reset r := (reset_pos r).le
  have hε1 : 0 ≤ 1 - reset r := (sub_pos.mpr (reset_lt_one r)).le
  rw [← ENNReal.ofReal_mul hε0, ← ENNReal.ofReal_mul hε1,
    ← ENNReal.ofReal_add (mul_nonneg hε0 (equilibriumDensity_nonneg r D))
      (mul_nonneg hε1 (residualDensity_nonneg r C D))]
  congr 1
  unfold residualDensity
  field_simp [ne_of_gt (sub_pos.mpr (reset_lt_one r))]
  ring

theorem residualKernel_split (r : ℝ) (C : SU2) :
    ENNReal.ofReal (reset r) • equilibriumLaw r +
      ENNReal.ofReal (1 - reset r) • residualKernel r C = loopKernel r C := by
  rw [equilibriumLaw, residualKernel_apply, loopKernel,
    MeasurableExponentialKernel.kernel_apply law _ (interaction_measurable r)]
  rw [← withDensity_smul' (ENNReal.ofReal (reset r))
    (fun D : SU2 => ENNReal.ofReal (equilibriumDensity r D)) ENNReal.ofReal_ne_top,
    ← withDensity_smul' (ENNReal.ofReal (1 - reset r))
    (fun D : SU2 => ENNReal.ofReal (residualDensity r C D)) ENNReal.ofReal_ne_top]
  erw [← withDensity_add_left
    ((equilibriumDensity_measurable r).ennreal_ofReal.const_smul (ENNReal.ofReal (reset r)))]
  apply withDensity_congr_ae
  filter_upwards with D
  exact residual_density_split r C D

theorem forward_split (r : ℝ) (ρ : Measure SU2) [IsProbabilityMeasure ρ] :
    ENNReal.ofReal (reset r) • equilibriumLaw r +
      ENNReal.ofReal (1 - reset r) • (residualKernel r ∘ₘ ρ) =
        loopKernel r ∘ₘ ρ := by
  ext B hB
  have hi := lintegral_congr (μ := ρ)
    (fun C => congrArg (fun ν : Measure SU2 => ν B) (residualKernel_split r C))
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at hi
  rw [lintegral_add_left measurable_const, lintegral_const,
    lintegral_const_mul _ ((residualKernel r).measurable_coe hB)] at hi
  simpa only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one, Measure.bind_apply hB (residualKernel r).aemeasurable,
    Measure.bind_apply hB (loopKernel r).aemeasurable] using hi

theorem residualKernel_invariant (r : ℝ) :
    residualKernel r ∘ₘ equilibriumLaw r = equilibriumLaw r := by
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  have hs := forward_split r (equilibriumLaw r)
  rw [equilibriumLaw_stationary] at hs
  have hε0 : 0 ≤ reset r := (reset_pos r).le
  have hε1 : 0 ≤ 1 - reset r := (sub_pos.mpr (reset_lt_one r)).le
  have hc : ENNReal.ofReal (reset r) + ENNReal.ofReal (1 - reset r) = 1 := by
    rw [← ENNReal.ofReal_add hε0 hε1]
    norm_num
  have he : ENNReal.ofReal (reset r) • equilibriumLaw r +
      ENNReal.ofReal (1 - reset r) • equilibriumLaw r = equilibriumLaw r := by
    rw [← add_smul, hc, one_smul]
  letI : IsFiniteMeasure (ENNReal.ofReal (reset r) • equilibriumLaw r) := ⟨by simp⟩
  have heq := (Measure.add_right_inj
    (ENNReal.ofReal (reset r) • equilibriumLaw r) _ _).mp (hs.trans he.symm)
  have hi := congrArg (fun ν : Measure SU2 =>
    (ENNReal.ofReal (1 - reset r))⁻¹ • ν) heq
  simpa only [smul_smul, ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (reset_lt_one r))))
    ENNReal.ofReal_ne_top, one_smul] using hi

theorem entropy_contraction (r : ℝ) (ρ : Measure SU2) [IsProbabilityMeasure ρ] :
    klDiv (loopKernel r ∘ₘ ρ) (equilibriumLaw r) ≤
      ENNReal.ofReal (1 - reset r) * klDiv ρ (equilibriumLaw r) := by
  letI : IsMarkovKernel (residualKernel r) := residualKernel_markov r
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  have hd := klDiv_comp_right_le ρ (equilibriumLaw r) (residualKernel r)
  rw [residualKernel_invariant] at hd
  let a : ℝ≥0 := ⟨reset r, (reset_pos r).le⟩
  let b : ℝ≥0 := ⟨1 - reset r, (sub_pos.mpr (reset_lt_one r)).le⟩
  have hab : a + b = 1 := by ext; change reset r + (1 - reset r) = 1; ring
  have hm := OperatorDerivativeRewrite.Foundation.CauchyPoissonMixtureEntropy.mixture_kl_bound_all
    ((residualKernel r) ∘ₘ ρ) (equilibriumLaw r) a b hab
  have ha : (a : ℝ≥0∞) = ENNReal.ofReal (reset r) := by
    exact (ENNReal.ofReal_eq_coe_nnreal (reset_pos r).le).symm
  have hb : (b : ℝ≥0∞) = ENNReal.ofReal (1 - reset r) := by
    exact (ENNReal.ofReal_eq_coe_nnreal (sub_pos.mpr (reset_lt_one r)).le).symm
  change klDiv ((a : ℝ≥0∞) • equilibriumLaw r +
    (b : ℝ≥0∞) • ((residualKernel r) ∘ₘ ρ)) (equilibriumLaw r) ≤ _ at hm
  rw [ha, hb, forward_split r ρ] at hm
  exact hm.trans (by gcongr)

def iterateLaw (r : ℝ) (ρ : Measure SU2) : ℕ → Measure SU2
  | 0 => ρ
  | n + 1 => loopKernel r ∘ₘ iterateLaw r ρ n

theorem iterateLaw_probability (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] (n : ℕ) :
    IsProbabilityMeasure (iterateLaw r ρ n) := by
  induction n with
  | zero => simpa [iterateLaw] using (inferInstance : IsProbabilityMeasure ρ)
  | succ n ih =>
      letI : IsProbabilityMeasure (iterateLaw r ρ n) := ih
      letI : IsMarkovKernel (loopKernel r) := loopKernel_markov r
      change IsProbabilityMeasure (loopKernel r ∘ₘ iterateLaw r ρ n)
      infer_instance

theorem entropy_geometric (r : ℝ) (ρ : Measure SU2) [IsProbabilityMeasure ρ]
    (n : ℕ) :
    klDiv (iterateLaw r ρ n) (equilibriumLaw r) ≤
      (ENNReal.ofReal (1 - reset r)) ^ n * klDiv ρ (equilibriumLaw r) := by
  induction n with
  | zero => simp [iterateLaw]
  | succ n ih =>
      letI : IsProbabilityMeasure (iterateLaw r ρ n) :=
        iterateLaw_probability r ρ n
      have hs := entropy_contraction r (iterateLaw r ρ n)
      change klDiv (loopKernel r ∘ₘ iterateLaw r ρ n) (equilibriumLaw r) ≤ _
      calc
        _ ≤ ENNReal.ofReal (1 - reset r) *
            klDiv (iterateLaw r ρ n) (equilibriumLaw r) := hs
        _ ≤ ENNReal.ofReal (1 - reset r) *
            ((ENNReal.ofReal (1 - reset r)) ^ n *
              klDiv ρ (equilibriumLaw r)) := by gcongr
        _ = _ := by rw [pow_succ]; ring

end OperatorDerivativeRewrite.Foundation.SU2ResidualEntropy
