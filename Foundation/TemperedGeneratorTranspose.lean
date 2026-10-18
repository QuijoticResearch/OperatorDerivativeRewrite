import Mathlib.Analysis.Distribution.TemperedDistribution

/-! Density generators transpose with parity; no odd-order measure is assumed. -/
noncomputable section
open scoped SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.TemperedGeneratorTranspose

def distributionJet (n : ℕ) (u : 𝓢'(ℝ, ℂ)) : 𝓢'(ℝ, ℂ) :=
  (TemperedDistribution.derivCLM ℂ)^[n] u

def testJet (n : ℕ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (SchwartzMap.derivCLM ℂ ℂ)^[n] f

theorem jet_pairing (n : ℕ) (u : 𝓢'(ℝ, ℂ)) (f : 𝓢(ℝ, ℂ)) :
    distributionJet n u f = (-1:ℂ)^n * u (testJet n f) := by
  induction n generalizing f with
  | zero => simp [distributionJet, testJet]
  | succ n ih =>
    change ((TemperedDistribution.derivCLM ℂ)^[n+1] u) f = _
    rw [Function.iterate_succ_apply', TemperedDistribution.derivCLM_apply_apply, map_neg]
    change -(distributionJet n u (SchwartzMap.derivCLM ℂ ℂ f)) = _
    rw [ih]
    have he : testJet n (SchwartzMap.derivCLM ℂ ℂ f) = testJet (n+1) f := by
      exact (Function.iterate_succ_apply _ _ _).symm
    rw [he, pow_succ]
    ring

theorem generator_pairing (c : ℂ) (p : ℕ) (u : 𝓢'(ℝ, ℂ)) (f : 𝓢(ℝ, ℂ)) :
    (c • distributionJet p u) f = ((-1:ℂ)^p*c) * u (testJet p f) := by
  simp only [smul_apply, smul_eq_mul, jet_pairing]
  ring

theorem even_generator_pairing (c : ℂ) (p : ℕ) (hp : Even p)
    (u : 𝓢'(ℝ, ℂ)) (f : 𝓢(ℝ, ℂ)) :
    (c • distributionJet p u) f = c * u (testJet p f) := by
  rw [generator_pairing, hp.neg_one_pow, one_mul]

theorem odd_generator_pairing (c : ℂ) (p : ℕ) (hp : Odd p)
    (u : 𝓢'(ℝ, ℂ)) (f : 𝓢(ℝ, ℂ)) :
    (c • distributionJet p u) f = -(c * u (testJet p f)) := by
  rw [generator_pairing, hp.neg_one_pow]
  ring

theorem odd_same_sign_impossible (c : ℂ) (hc : c ≠ 0) (p : ℕ) (hp : Odd p)
    (u : 𝓢'(ℝ, ℂ)) (f : 𝓢(ℝ, ℂ)) (hf : u (testJet p f) ≠ 0) :
    (c • distributionJet p u) f ≠ c * u (testJet p f) := by
  rw [odd_generator_pairing c p hp]
  intro h
  have he : (2:ℂ)*(c * u (testJet p f)) = 0 := by linear_combination -h
  exact mul_ne_zero (by norm_num) (mul_ne_zero hc hf) he

end OperatorDerivativeRewrite.Foundation.TemperedGeneratorTranspose
