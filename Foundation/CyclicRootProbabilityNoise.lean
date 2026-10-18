import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Actual finite probability innovations with arbitrary cyclic holomorphic moment gaps. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.CyclicRootProbabilityNoise
variable (N : ℕ) [NeZero N]

instance cyclicMeasurable : MeasurableSpace (ZMod N) := ⊤
instance cyclicSingletons : MeasurableSingletonClass (ZMod N) := ⟨fun _ => trivial⟩

def probability : Measure (ZMod N) := (PMF.uniformOfFintype (ZMod N)).toMeasure

instance probability_isProbability : IsProbabilityMeasure (probability N) := by
  unfold probability
  infer_instance

def noise (c : ℂ) (k : ZMod N) : ℂ := c * ZMod.stdAddChar k

theorem integral_formula (f : ZMod N → ℂ) :
    (∫ k, f k ∂probability N) = (∑ k, f k)/(N : ℂ) := by
  rw [probability,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ZMod.card,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,Complex.real_smul,← Finset.mul_sum,Complex.ofReal_inv,
    Complex.ofReal_natCast]
  ring

theorem character_sum (j : ZMod N) :
    (∑ k : ZMod N, ZMod.stdAddChar (j*k)) = if j = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h,ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

theorem noise_power (c : ℂ) (k : ZMod N) (r : ℕ) :
    (noise N c k)^r = c^r * ZMod.stdAddChar ((r : ZMod N)*k) := by
  rw [noise,mul_pow,← AddChar.map_nsmul_eq_pow,nsmul_eq_mul]

theorem holomorphic_moment (c : ℂ) (r : ℕ) :
    (∫ k, (noise N c k)^r ∂probability N) = if (r : ZMod N) = 0 then c^r else 0 := by
  rw [integral_formula]
  simp_rw [noise_power]
  rw [← Finset.mul_sum,character_sum]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  split_ifs <;> simp_all

theorem lower_moment (c : ℂ) (r : ℕ) (hr : 0 < r) (hN : r < N) :
    (∫ k, (noise N c k)^r ∂probability N) = 0 := by
  rw [holomorphic_moment,if_neg]
  intro h
  exact (Nat.not_le_of_gt hN) (Nat.le_of_dvd hr ((ZMod.natCast_eq_zero_iff r N).mp h))

theorem nth_power (c : ℂ) (k : ZMod N) : (noise N c k)^N = c^N := by
  rw [noise_power]
  simp

theorem nth_moment (c : ℂ) : (∫ k, (noise N c k)^N ∂probability N) = c^N := by
  simp_rw [nth_power]
  simp

theorem noise_norm (c : ℂ) (k : ZMod N) : ‖noise N c k‖ = ‖c‖ := by
  rw [noise,norm_mul,ZMod.stdAddChar_apply,Circle.norm_coe,mul_one]

theorem absolute_second (c : ℂ) : (∫ k, ‖noise N c k‖^2 ∂probability N) = ‖c‖^2 := by
  simp_rw [noise_norm]
  simp

end OperatorDerivativeRewrite.Foundation.CyclicRootProbabilityNoise
