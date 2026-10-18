import Foundation.SignedSchwartzPolynomialL2
import Foundation.SchwartzGaussianCutoff
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! Actual polynomial jets in the minimal Schwartz graph completion, constructed by a
single Gaussian cutoff sequence and dominated convergence in the positive majorant.
This is a marginal domain theorem; no chronological or path-space completion is asserted. -/
noncomputable section
open MeasureTheory Polynomial Filter
open scoped SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzPolynomialJets
open SignedSchwartzL2Rigging SignedSchwartzClosedDerivative SignedSchwartzPolynomialL2
open SchwartzPolynomialPairing SchwartzGaussianCutoff HigherHeatSpatialGenerator

def polyJet (P : Polynomial ℝ) (r : ℕ) (x : ℝ) : ℂ :=
  ((((Polynomial.derivative^[r]) P).eval x : ℝ) : ℂ)

theorem polyJet_eq (P : Polynomial ℝ) (r : ℕ) :
    iteratedDeriv r (fun x : ℝ => ((P.eval x : ℝ) : ℂ)) = polyJet P r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    change deriv (fun y : ℝ => ((((Polynomial.derivative^[r]) P).eval y : ℝ) : ℂ)) x = _
    simpa only [polyJet, Function.iterate_succ_apply'] using
      (((Polynomial.derivative^[r]) P).hasDerivAt x).ofReal_comp.deriv

def approx (P : Polynomial ℝ) (n : ℕ) : 𝓢(ℝ, ℂ) := weightedPolynomial P (cutoff n)

theorem approx_jet (P : Polynomial ℝ) (r n : ℕ) (x : ℝ) :
    iteratedDeriv r (approx P n : ℝ → ℂ) x =
      ∑ k ∈ Finset.range (r + 1), (r.choose k : ℂ) *
        iteratedDeriv k (cutoff n : ℝ → ℂ) x * polyJet P (r - k) x := by
  have he : (approx P n : ℝ → ℂ) =
      (fun y : ℝ => cutoff n y * ((P.eval y : ℝ) : ℂ)) := by
    funext y
    rw [approx, weighted_apply, mul_comm]
  rw [he]
  have hp : ContDiff ℝ r (fun y : ℝ => ((P.eval y : ℝ) : ℂ)) := by
    apply Complex.ofRealCLM.contDiff.comp
    simpa using P.contDiff_aeval (𝕜 := ℝ) r
  rw [iteratedDeriv_fun_mul ((cutoff n).smooth r).contDiffAt hp.contDiffAt]
  simp only [polyJet_eq]

theorem approx_jet_tendsto (P : Polynomial ℝ) (r : ℕ) (x : ℝ) :
    Tendsto (fun n => iteratedDeriv r (approx P n : ℝ → ℂ) x) atTop
      (𝓝 (polyJet P r x)) := by
  have ht := tendsto_finsetSum (Finset.range (r + 1)) (fun k _ =>
    ((tendsto_const_nhds (x := (r.choose k : ℂ))).mul
      (cutoff_jet_tendsto k x)).mul (tendsto_const_nhds (x := polyJet P (r - k) x)))
  simpa only [approx_jet, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, ite_true, Nat.choose_zero_right,
    Nat.cast_one, one_mul, Nat.sub_zero] using ht

theorem polynomial_abs_bound (P : Polynomial ℝ) (x : ℝ) :
    |P.eval x| ≤ (1+P^2).eval x := by
  simp only [eval_add, eval_one, eval_pow]
  have hs := sq_nonneg (|P.eval x|-1)
  nlinarith [sq_abs (P.eval x)]

def bound (P : Polynomial ℝ) (r : ℕ) : Polynomial ℝ :=
  (1+((Polynomial.derivative^[r]) P)^2) +
    ∑ k ∈ Finset.range (r + 1),
      C ((r.choose k : ℝ)*jetBound k) * (1+((Polynomial.derivative^[r - k]) P)^2)

theorem bound_nonneg (P : Polynomial ℝ) (r : ℕ) (x : ℝ) : 0 ≤ (bound P r).eval x := by
  simp only [bound, eval_add, eval_one, eval_pow, eval_finsetSum, eval_mul, eval_C]
  apply add_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (jetBound_nonneg k)) (by positivity)

theorem polyJet_bound (P : Polynomial ℝ) (r : ℕ) (x : ℝ) :
    ‖polyJet P r x‖ ≤ (bound P r).eval x := by
  have hb := polynomial_abs_bound ((Polynomial.derivative^[r]) P) x
  simp only [polyJet, Complex.norm_real, Real.norm_eq_abs]
  apply hb.trans
  simp only [bound, eval_add, eval_one, eval_pow, eval_finsetSum, eval_mul, eval_C]
  have hs : 0 ≤ ∑ k ∈ Finset.range (r + 1),
      ((r.choose k : ℝ)*jetBound k) * (1+(((Polynomial.derivative^[r - k]) P).eval x)^2) := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (jetBound_nonneg k)) (by positivity)
  linarith

theorem approx_jet_bound (P : Polynomial ℝ) (r n : ℕ) (x : ℝ) :
    ‖iteratedDeriv r (approx P n : ℝ → ℂ) x‖ ≤ (bound P r).eval x := by
  rw [approx_jet]
  apply (norm_sum_le _ _).trans
  have hs : (∑ k ∈ Finset.range (r + 1),
      ‖(r.choose k : ℂ)*iteratedDeriv k (cutoff n : ℝ → ℂ) x*polyJet P (r - k) x‖) ≤
      ∑ k ∈ Finset.range (r + 1),
      ((r.choose k : ℝ)*jetBound k) * (1+(((Polynomial.derivative^[r - k]) P).eval x)^2) := by
    apply Finset.sum_le_sum
    intro k hk
    simp only [norm_mul, Complex.norm_natCast, polyJet, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (cutoff_jet_bound k n x) (Nat.cast_nonneg _))
      (by simpa only [eval_add, eval_one, eval_pow] using
        polynomial_abs_bound ((Polynomial.derivative^[r - k]) P) x)
      (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (jetBound_nonneg k))
  apply hs.trans
  simp only [bound, eval_add, eval_one, eval_pow, eval_finsetSum, eval_mul, eval_C]
  linarith [sq_nonneg (((Polynomial.derivative^[r]) P).eval x)]

theorem coreInput_ae (K : 𝓢(ℝ, ℝ)) (f : 𝓢(ℝ, ℂ)) :
    coreInput K f =ᵐ[measure K] f := f.coeFn_toLp 2 (measure K)

theorem approx_l2_tendsto (K : 𝓢(ℝ, ℝ)) (P : Polynomial ℝ) (r : ℕ) :
    Tendsto (fun n => coreInput K (jet r (approx P n))) atTop
      (𝓝 (polynomialL2 K ((Polynomial.derivative^[r]) P))) := by
  let b := (real_memLp K (bound P r)).toLp (fun x => (bound P r).eval x)
  have hb : b =ᵐ[measure K] (fun x => (bound P r).eval x) := MemLp.coeFn_toLp _
  have hf (n : ℕ) : coreInput K (jet r (approx P n)) =ᵐ[measure K]
      (fun x => iteratedDeriv r (approx P n : ℝ → ℂ) x) := by
    simpa only [jet_coe] using coreInput_ae K (jet r (approx P n))
  have hg := polynomialL2_ae K ((Polynomial.derivative^[r]) P)
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [hf n, hb] with x hx hy
    rw [hx, hy, Real.norm_eq_abs, abs_of_nonneg (bound_nonneg P r x)]
    exact approx_jet_bound P r n x
  · filter_upwards [hg, hb] with x hx hy
    rw [hx, hy, Real.norm_eq_abs, abs_of_nonneg (bound_nonneg P r x)]
    exact polyJet_bound P r x
  · have hall : ∀ᵐ x ∂measure K, ∀ n, coreInput K (jet r (approx P n)) x =
        iteratedDeriv r (approx P n : ℝ → ℂ) x := ae_all_iff.mpr hf
    filter_upwards [hall, hg] with x hx hy
    simp only [hx, hy]
    exact approx_jet_tendsto P r x

theorem deriv_iterate_eq_jet (r : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (SchwartzMap.derivCLM ℂ ℂ)^[r] f = jet r f := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', ih]; rfl

def polynomialJets (K : 𝓢(ℝ, ℝ)) (r : ℕ) (P : Polynomial ℝ) :
    SignedSchwartzJetDomain.Jets K r :=
  fun i => polynomialL2 K ((Polynomial.derivative^[i.val]) P)

theorem jets_tendsto (K : 𝓢(ℝ, ℝ)) (r : ℕ) (P : Polynomial ℝ) :
    Tendsto (fun n => SignedSchwartzJetDomain.jets K r (approx P n)) atTop
      (𝓝 (polynomialJets K r P)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  simpa only [SignedSchwartzJetDomain.jets_apply, deriv_iterate_eq_jet, polynomialJets]
    using approx_l2_tendsto K P i.val

theorem polynomialJets_mem (K : 𝓢(ℝ, ℝ)) (r : ℕ) (P : Polynomial ℝ) :
    polynomialJets K r P ∈ SignedSchwartzJetDomain.coreClosure K r := by
  apply (SignedSchwartzJetDomain.coreClosure_closed K r).mem_of_tendsto
    (jets_tendsto K r P)
  exact Eventually.of_forall (fun n =>
    (SignedSchwartzJetDomain.jets K r).range.le_topologicalClosure ⟨approx P n, rfl⟩)

def polynomialDomain (K : 𝓢(ℝ, ℝ)) (r : ℕ) (P : Polynomial ℝ) :
    SignedSchwartzJetDomain.Domain K r := ⟨polynomialJets K r P, polynomialJets_mem K r P⟩

theorem polynomialDomain_component (K : 𝓢(ℝ, ℝ)) (r : ℕ) (P : Polynomial ℝ)
    (i : Fin (r + 1)) :
    SignedSchwartzJetDomain.component K r i (polynomialDomain K r P) =
      polynomialL2 K ((Polynomial.derivative^[i.val]) P) := rfl

theorem polynomialDomain_value (K : 𝓢(ℝ, ℝ)) (r : ℕ) (P : Polynomial ℝ) :
    SignedSchwartzJetDomain.value K r (polynomialDomain K r P) = polynomialL2 K P := rfl

theorem polynomialDomain_unique (K : 𝓢(ℝ, ℝ)) (r : ℕ) (P : Polynomial ℝ)
    (u : SignedSchwartzJetDomain.Domain K r)
    (hu : SignedSchwartzJetDomain.value K r u = polynomialL2 K P) :
    u = polynomialDomain K r P :=
  SignedSchwartzJetDomain.value_injective K r hu

theorem polynomialDomain_tendsto (K : 𝓢(ℝ, ℝ)) (r : ℕ) (P : Polynomial ℝ) :
    Tendsto (fun n => SignedSchwartzJetDomain.core K r (approx P n)) atTop
      (𝓝 (polynomialDomain K r P)) :=
  tendsto_subtype_rng.mpr (jets_tendsto K r P)

theorem polynomial_mem_closed_graph (K : 𝓢(ℝ, ℝ)) (P : Polynomial ℝ) :
    (polynomialL2 K P, polynomialL2 K P.derivative) ∈ (closedDerivative K).graph := by
  have h := SignedSchwartzJetDomain.coreClosure_compatible K 1 (polynomialJets_mem K 1 P)
  exact (SignedSchwartzJetDomain.mem_compatible K 1 (polynomialJets K 1 P)).mp h 0

end OperatorDerivativeRewrite.Foundation.SignedSchwartzPolynomialJets
