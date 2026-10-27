import Foundation.WaveTorusCoreBridge
import Foundation.FourierGammaCriterion
/-! A bounded, even, nonnegative, zero-normalized Fourier rate with an actual
Haar-L² contraction semigroup but negative pointwise algebraic Γ₁ on a finite
two-mode cylinder. This disproves conditional negative definiteness and
covariance positivity for arbitrary nonnegative multiplier rates. It does not
by itself construct or exclude a stochastic path realization in Lean. -/
open Filter
open scoped Topology NNReal
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open FiniteStableGamma.Core FourierGammaCriterion
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.BoundedRateGammaObstruction

def waveOne : Wave := fun _ => 1
def waveTwo : Wave := fun _ => 2
def rate (k : Wave) : ℝ := if k = waveTwo ∨ k = -waveTwo then 1 else 0
def waves : Fin 2 → Wave := ![waveOne,waveTwo]
def weights : Fin 2 → ℝ := ![1,-1/2]
def witness : Fourier :=
  ∑ i : Fin 2, AddMonoidAlgebra.single (waves i) (weights i : ℂ)

theorem rate_nonnegative (k : Wave) : 0 ≤ rate k := by
  simp only [rate]
  split_ifs <;> norm_num

theorem rate_le_one (k : Wave) : rate k ≤ 1 := by
  simp only [rate]
  split_ifs <;> norm_num

theorem rate_even (k : Wave) : rate (-k) = rate k := by
  have he : waveTwo = -k ↔ k = -waveTwo := by
    constructor
    · intro h
      have hh := congrArg Neg.neg h
      simpa using hh.symm
    · intro h
      have hh := congrArg Neg.neg h
      simpa using hh.symm
  simp [rate,neg_eq_iff_eq_neg,eq_comm,he,or_comm]

def nnRate (k : Wave) : ℝ≥0 := ⟨rate k,rate_nonnegative k⟩

private theorem waveOne_ne_two : waveOne ≠ waveTwo := by
  intro h
  have hh := congrFun h (0 : Fin 3)
  norm_num [waveOne,waveTwo] at hh

private theorem waveOne_ne_neg_two : waveOne ≠ -waveTwo := by
  intro h
  have hh := congrFun h (0 : Fin 3)
  norm_num [waveOne,waveTwo,Pi.neg_apply] at hh

private theorem waveTwo_ne_zero : waveTwo ≠ 0 := by
  intro h
  have hh := congrFun h (0 : Fin 3)
  norm_num [waveTwo] at hh

theorem rate_one : rate waveOne = 0 := by
  simp [rate,waveOne_ne_two,waveOne_ne_neg_two]

theorem rate_two : rate waveTwo = 1 := by simp [rate]

theorem rate_zero : rate 0 = 0 := by
  simp [rate,waveTwo_ne_zero,Ne.symm waveTwo_ne_zero]

theorem rate_neg_one : rate (-waveOne) = 0 := by
  have h : -waveOne ≠ waveTwo := by
    intro he
    have hh := congrFun he (0 : Fin 3)
    norm_num [waveOne,waveTwo,Pi.neg_apply] at hh
  have h' : -waveOne ≠ -waveTwo := by
    intro he
    apply waveOne_ne_two
    simpa using congrArg Neg.neg he
  simp [rate,h,h']

private theorem two_sub_one : waveTwo-waveOne = waveOne := by
  funext j
  simp [waveOne,waveTwo,Pi.sub_apply]

private theorem one_sub_two : waveOne-waveTwo = -waveOne := by
  funext j
  simp [waveOne,waveTwo,Pi.sub_apply,Pi.neg_apply]

theorem gamma_negative :
    (synthesis (0 : Space) (gammaIter rate 1 witness witness)).re = -1/4 := by
  unfold witness
  rw [real_gamma_energy]
  norm_num [Fin.sum_univ_succ,waves,weights,kernel,rate_one,rate_two,
    rate_zero,rate_neg_one,two_sub_one,one_sub_two]

theorem not_gamma_positive :
    ¬ ∀ f : Fourier, 0 ≤ (synthesis (0 : Space) (gammaIter rate 1 f f)).re := by
  intro h
  have hh := h witness
  rw [gamma_negative] at hh
  norm_num at hh

theorem not_negative_symbol :
    ¬ FourierCovarianceCriterion.NegativeSymbol rate := by
  intro h
  exact not_gamma_positive
    ((FourierGammaCriterion.gamma_positive_iff_negative rate rate_zero rate_even).mpr h)

theorem not_covariance_symbol :
    ¬ FourierCovarianceCriterion.CovarianceSymbol rate := by
  intro h
  exact not_negative_symbol
    ((FourierCovarianceCriterion.symbol_iff rate rate_zero rate_even).mp h)

theorem physical_witness_slope :
    Tendsto (PhysicalTorusWaveSemigroup.slope nnRate
      (WaveTorusCoreBridge.lift witness)) (𝓝[>] 0)
      (𝓝 (WaveTorusCoreBridge.lift (generator rate witness))) := by
  apply (PhysicalTorusWaveSemigroup.generator_iff nnRate _ _).mpr
  intro k
  rw [WaveTorusCoreBridge.lift_coeff,WaveTorusCoreBridge.lift_coeff,
    WaveTorusCoreBridge.generator_coeff]
  rfl

theorem physical_contraction (t : ℝ≥0) :
    ‖PhysicalTorusWaveSemigroup.evolution nnRate t
      (WaveTorusCoreBridge.lift witness)‖ ≤
      ‖WaveTorusCoreBridge.lift witness‖ :=
  PhysicalTorusWaveSemigroup.contraction nnRate t _

theorem physical_stationary_zero (t : ℝ≥0) :
    PhysicalTorusWaveSemigroup.evolution nnRate t
      (PhysicalTorusWaveSemigroup.basis 0) =
        PhysicalTorusWaveSemigroup.basis 0 := by
  exact PhysicalTorusWaveSemigroup.stationary_mode nnRate 0
    (Subtype.ext rate_zero) t

end OperatorDerivativeRewrite.Foundation.BoundedRateGammaObstruction
