import Foundation.SymmetricPolynomialTaylor
import Mathlib.Topology.ContinuousMap.Compact

/-! Compact-uniform limits of the ACTUAL symmetric imaginary polynomial shifts.
Finite coefficient vectors evaluate continuously in the existing compact-open
function space; factorial-jet convergence and a common degree bound suffice.
This transfers the verified scaled Taylor/Euler limit to the whole complex plane.
No infinite-degree Xi vector is put into the bounded factorial domain. -/
noncomputable section
open Polynomial Filter Set Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.SymmetricPolynomialHeatLimit

def finiteEvaluation (L : ℕ) (a : Fin L → ℝ) : C(ℂ,ℂ) :=
  ⟨fun z => ∑ j : Fin L,(a j:ℂ)*z^(j:ℕ),by fun_prop⟩

theorem finiteEvaluation_continuous (L : ℕ) : Continuous (finiteEvaluation L) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (Fin L → ℝ) × ℂ => ∑ j : Fin L,(p.1 j:ℂ)*p.2^(j:ℕ))
  apply continuous_finsetSum
  intro j hj
  exact (Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_fst)).mul
    (continuous_snd.pow (j:ℕ))

theorem finiteEvaluation_limit (L : ℕ) (a : ℕ → Fin L → ℝ) (b : Fin L → ℝ)
    (ha : ∀ j : Fin L,Tendsto (fun n => a n j) atTop (𝓝 (b j))) :
    TendstoLocallyUniformly (fun n z => finiteEvaluation L (a n) z)
      (finiteEvaluation L b) atTop := by
  have hv : Tendsto a atTop (𝓝 b) := tendsto_pi_nhds.mpr ha
  have hc := ((finiteEvaluation_continuous L).tendsto b).comp hv
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hc) K hK

theorem finiteEvaluation_polynomial (L : ℕ) (P : ℝ[X]) (hP : P.natDegree<L) (z : ℂ) :
    finiteEvaluation L (fun j => P.coeff (j:ℕ)) z=(P.map (algebraMap ℝ ℂ)).eval z := by
  have he := (P.map (algebraMap ℝ ℂ)).eval_eq_sum_range' (n:=L)
    (Polynomial.natDegree_map_le.trans_lt hP) z
  rw [he]
  change (∑ j : Fin L,(P.coeff (j:ℕ):ℂ)*z^(j:ℕ))=_
  simp only [coeff_map,Complex.coe_algebraMap]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (P.coeff j:ℂ)*z^j) L

theorem finite_degree_coefficient_limit (L : ℕ) (P : ℕ → ℝ[X]) (Q : ℝ[X])
    (hP : ∀ n,(P n).natDegree<L) (hQ : Q.natDegree<L)
    (hc : ∀ j : ℕ,j<L → Tendsto (fun n => (P n).coeff j) atTop (𝓝 (Q.coeff j))) :
    TendstoLocallyUniformly (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z)
      (fun z => (Q.map (algebraMap ℝ ℂ)).eval z) atTop := by
  have he := finiteEvaluation_limit L (fun n j => (P n).coeff j) (fun j => Q.coeff j)
    (fun j => hc j j.isLt)
  have hn : (fun n z => finiteEvaluation L (fun j => (P n).coeff j) z)=
      (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) := by
    funext n z
    exact finiteEvaluation_polynomial L (P n) (hP n) z
  have hq : (finiteEvaluation L (fun j => Q.coeff j):ℂ → ℂ)=
      (fun z => (Q.map (algebraMap ℝ ℂ)).eval z) := by
    funext z
    exact finiteEvaluation_polynomial L Q hQ z
  rw [hn,hq] at he
  exact he

open FactorialAnalyticDomain in
theorem finite_degree_jet_limit (L : ℕ) (P : ℕ → ℝ[X]) (Q : ℝ[X])
    (hP : ∀ n,(P n).natDegree<L) (hQ : Q.natDegree<L)
    (hjet : Tendsto (fun n => polynomial (P n)) atTop (𝓝 (polynomial Q))) :
    TendstoLocallyUniformly (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z)
      (fun z => (Q.map (algebraMap ℝ ℂ)).eval z) atTop := by
  apply finite_degree_coefficient_limit L P Q hP hQ
  intro j hj
  have he := ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 j).continuous.tendsto _).comp hjet
  have hd := he.div_const (j.factorial:ℝ)
  change Tendsto (fun n => ((j.factorial:ℝ)*(P n).coeff j)/(j.factorial:ℝ)) atTop
    (𝓝 (((j.factorial:ℝ)*Q.coeff j)/(j.factorial:ℝ))) at hd
  simpa only [mul_div_cancel_left₀ _ (by positivity : (j.factorial:ℝ)≠0)] using hd

open FactorialAnalyticDomain in
theorem jet_limit_degree (D : ℕ) (P : ℕ → ℝ[X]) (Q : ℝ[X])
    (hP : ∀ n,(P n).natDegree≤D)
    (hjet : Tendsto (fun n => polynomial (P n)) atTop (𝓝 (polynomial Q))) :
    Q.natDegree≤D := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have he := ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 k).continuous.tendsto _).comp hjet
  have hz : Tendsto (fun n => polynomial (P n) k) atTop (𝓝 (0:ℝ)) := by
    have heq : (fun n => polynomial (P n) k)=(fun _ : ℕ => (0:ℝ)) := by
      funext n
      rw [polynomial_apply,Polynomial.coeff_eq_zero_of_natDegree_lt ((hP n).trans_lt hk),mul_zero]
    rw [heq]
    exact tendsto_const_nhds
  have hh : polynomial Q k=0 := tendsto_nhds_unique he hz
  rw [polynomial_apply] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by positivity)

theorem scaledShift_locally_uniform (s : ℝ) (hs : 0≤s) (P : ℝ[X]) :
    TendstoLocallyUniformly
      (fun n z => (SymmetricPolynomialStrip.scaledShift s n (P.map (algebraMap ℝ ℂ))).eval z)
      (fun z => ((PureOrderPolynomialTransport.transport 2 (-s) P).map (algebraMap ℝ ℂ)).eval z)
      atTop := by
  have hj := SymmetricPolynomialTaylor.scaledEvenTaylor_jet_limit s hs P
  have hd (n : ℕ) : (SymmetricPolynomialTaylor.scaledEvenTaylor s n P).natDegree≤P.natDegree :=
    SymmetricPolynomialTaylor.scaledEvenTaylor_degree s n P
  have hQ := jet_limit_degree P.natDegree _ _ hd hj
  have he := finite_degree_jet_limit (P.natDegree+1)
    (SymmetricPolynomialTaylor.scaledEvenTaylor s · P)
    (PureOrderPolynomialTransport.transport 2 (-s) P)
    (fun n => (hd n).trans_lt (Nat.lt_succ_self _))
    (hQ.trans_lt (Nat.lt_succ_self _)) hj
  simpa only [SymmetricPolynomialTaylor.scaledEvenTaylor_map] using he

end OperatorDerivativeRewrite.Foundation.SymmetricPolynomialHeatLimit
