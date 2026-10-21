import Foundation.PolynomialDerivativeEuler
import Foundation.SymmetricPolynomialStrip

/-! Exact finite Taylor realization of symmetric imaginary polynomial shifts.
Real Hasse-derivative sums preserve degree, complexify to the actual symmetric
shift, and iterate with one cutoff. Their scaled factorial jets converge to the
existing heat transport. Complex local-uniform convergence is proved separately;
no actual Xi vector in the bounded factorial domain is asserted. -/
noncomputable section
open Polynomial Complex Finset Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.SymmetricPolynomialTaylor

theorem sum_even_odd (f : ℕ → ℂ) (N : ℕ) :
    (∑ r∈range (2*N),f r)=∑ j∈range N,(f (2*j)+f (2*j+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=2*N+1+1 by omega,sum_range_succ,sum_range_succ,ih,sum_range_succ]
    ring

theorem finite_hasse_eval (P : ℂ[X]) (L : ℕ) (hL : P.natDegree<L) (z w : ℂ) :
    P.eval (z+w)=∑ r∈range L,(hasseDeriv r P).eval z*w^r := by
  have he := (taylor z P).eval_eq_sum_range' (n:=L)
    (by simpa only [natDegree_taylor] using hL) w
  simpa only [taylor_eval,taylor_coeff,add_comm w z] using he

theorem imaginary_even (h : ℝ) (j : ℕ) :
    (I*(h:ℂ))^(2*j)=(((-1:ℝ)^j*h^(2*j):ℝ):ℂ) := by
  simp only [mul_pow,pow_mul,I_sq,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one]

theorem opposite_even (w : ℂ) (j : ℕ) : (-w)^(2*j)=w^(2*j) := by
  exact (even_two_mul j).neg_pow w

theorem opposite_odd (w : ℂ) (j : ℕ) : (-w)^(2*j+1)= -w^(2*j+1) := by
  rw [pow_succ,pow_succ,opposite_even]
  ring

theorem symmetricShift_hasse_eval (P : ℂ[X]) (N : ℕ) (hN : P.natDegree<2*(N+1))
    (h : ℝ) (z : ℂ) :
    (SymmetricPolynomialStrip.symmetricShift h P).eval z=
      ∑ j∈range (N+1),(((-1:ℝ)^j*h^(2*j):ℝ):ℂ)*(hasseDeriv (2*j) P).eval z := by
  rw [SymmetricPolynomialStrip.symmetricShift_eval,
    show z-I*h=z+(-I*h) by ring,
    finite_hasse_eval P (2*(N+1)) hN z (I*h),
    finite_hasse_eval P (2*(N+1)) hN z (-I*h)]
  have he : ((∑ r∈range (2*(N+1)),(hasseDeriv r P).eval z*(I*h)^r)+
      (∑ r∈range (2*(N+1)),(hasseDeriv r P).eval z*(-I*h)^r))/2=
      ∑ r∈range (2*(N+1)),(hasseDeriv r P).eval z*((I*h)^r+(-(I*h))^r)/2 := by
    rw [← Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he,sum_even_odd]
  apply Finset.sum_congr rfl
  intro j hj
  rw [opposite_even,opposite_odd,imaginary_even]
  ring

def evenTaylor (h : ℝ) (N : ℕ) (P : ℝ[X]) : ℝ[X] :=
  ∑ j∈range (N+1),((-1:ℝ)^j*h^(2*j)) • hasseDeriv (2*j) P

theorem evenTaylor_degree (h : ℝ) (N : ℕ) (P : ℝ[X]) :
    (evenTaylor h N P).natDegree≤P.natDegree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((Polynomial.natDegree_hasseDeriv_le _ _).trans (Nat.sub_le _ _))

theorem evenTaylor_map (h : ℝ) (N : ℕ) (P : ℝ[X]) (hN : P.natDegree<2*(N+1)) :
    (evenTaylor h N P).map (algebraMap ℝ ℂ)=
      SymmetricPolynomialStrip.symmetricShift h (P.map (algebraMap ℝ ℂ)) := by
  apply Polynomial.funext
  intro z
  rw [symmetricShift_hasse_eval _ N ((Polynomial.natDegree_map_le).trans_lt hN)]
  simp only [evenTaylor,Polynomial.map_sum,eval_finsetSum,Polynomial.map_smul,
    eval_smul,smul_eq_mul,hasseDeriv_map,Complex.coe_algebraMap]

open FactorialAnalyticDomain in
theorem polynomial_hasse (P : ℝ[X]) (r : ℕ) :
    polynomial (hasseDeriv r P)=(1/(r.factorial:ℝ)) • ((shift^r) (polynomial P)) := by
  rw [one_div]
  apply (eq_inv_smul_iff₀ (by positivity : (r.factorial:ℝ)≠0)).mpr
  have he := congrFun (Polynomial.factorial_smul_hasseDeriv (R:=ℝ) (k:=r)) P
  change r.factorial • hasseDeriv r P=derivative^[r] P at he
  rw [← Nat.cast_smul_eq_nsmul ℝ] at he
  have hj := congrArg (fun Q : ℝ[X] => polynomialMap Q) he
  rw [map_smul] at hj
  exact hj.trans (polynomial_iterate_derivative r P)

open FactorialAnalyticDomain in
theorem evenTaylor_jet (h : ℝ) (N : ℕ) (P : ℝ[X]) :
    polynomial (evenTaylor h N P)=∑ j∈range (N+1),
      (((-1:ℝ)^j*h^(2*j))/((2*j).factorial:ℝ)) • ((shift^(2*j)) (polynomial P)) := by
  change polynomialMap (evenTaylor h N P)=_
  rw [evenTaylor,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  change ((-1:ℝ)^j*h^(2*j)) • polynomial (hasseDeriv (2*j) P)=_
  rw [polynomial_hasse,smul_smul]
  simp only [one_div,div_eq_mul_inv,one_mul]

theorem clock_coefficient (h s : ℝ) (n j : ℕ)
    (hc : h^2=2*s/((n+1:ℕ):ℝ)) :
    ((-1:ℝ)^(j+1)*h^(2*(j+1)))/((2*(j+1)).factorial:ℝ)=
      (1/((n+1:ℕ):ℝ))*
        (((-1:ℝ)^(j+1)*(2*s)^(j+1)/((2*j+2).factorial:ℝ)) *
          (1/((n+1:ℕ):ℝ))^j) := by
  rw [pow_mul,hc,div_pow,show 2*(j+1)=2*j+2 by omega]
  simp only [div_eq_mul_inv,one_div,inv_pow,pow_succ]
  ring

open FactorialAnalyticDomain in
theorem evenTaylor_euler_step (h s : ℝ) (N n : ℕ) (P : ℝ[X])
    (hc : h^2=2*s/((n+1:ℕ):ℝ)) :
    polynomial (evenTaylor h (N+1) P)=
      (1+(1/((n+1:ℕ):ℝ)) • PolynomialDerivativeEuler.correction N s n) (polynomial P) := by
  rw [evenTaylor_jet,sum_range_succ']
  simp only [Nat.mul_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,div_one,
    one_smul,one_apply_eq_self,_root_.add_apply,_root_.smul_apply]
  change (∑ j∈range (N+1),
      (((-1:ℝ)^(j+1)*h^(2*(j+1)))/((2*(j+1)).factorial:ℝ)) •
        ((shift^(2*(j+1))) (polynomial P)))+polynomial P=
      polynomial P+(1/((n+1:ℕ):ℝ)) • (PolynomialDerivativeEuler.correction N s n (polynomial P))
  rw [add_comm]
  congr 1
  rw [PolynomialDerivativeEuler.correction,_root_.sum_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [_root_.smul_apply,smul_smul,clock_coefficient h s n j hc]
  congr 2

def iterateEvenTaylor (h : ℝ) (N r : ℕ) (P : ℝ[X]) : ℝ[X] := (evenTaylor h N)^[r] P

theorem iterateEvenTaylor_succ (h : ℝ) (N r : ℕ) (P : ℝ[X]) :
    iterateEvenTaylor h N (r+1) P=evenTaylor h N (iterateEvenTaylor h N r P) := by
  simp only [iterateEvenTaylor,Function.iterate_succ_apply']

theorem iterateEvenTaylor_degree (h : ℝ) (N r : ℕ) (P : ℝ[X]) :
    (iterateEvenTaylor h N r P).natDegree≤P.natDegree := by
  induction r with
  | zero => exact le_refl _
  | succ r ih =>
    rw [iterateEvenTaylor_succ]
    exact (evenTaylor_degree h N _).trans ih

open FactorialAnalyticDomain in
theorem iterateEvenTaylor_jet (h s : ℝ) (N n r : ℕ) (P : ℝ[X])
    (hc : h^2=2*s/((n+1:ℕ):ℝ)) :
    polynomial (iterateEvenTaylor h (N+1) r P)=
      ((1+(1/((n+1:ℕ):ℝ)) • PolynomialDerivativeEuler.correction N s n)^r) (polynomial P) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [iterateEvenTaylor_succ]
    rw [evenTaylor_euler_step h s N n _ hc]
    change (1+(1/((n+1:ℕ):ℝ)) • PolynomialDerivativeEuler.correction N s n)
      (polynomial (iterateEvenTaylor h (N+1) r P))=_
    rw [ih,pow_succ']
    rfl

theorem iterateEvenTaylor_map (h : ℝ) (N r : ℕ) (P : ℝ[X])
    (hN : P.natDegree<2*(N+1)) :
    (iterateEvenTaylor h N r P).map (algebraMap ℝ ℂ)=
      SymmetricPolynomialStrip.iteratedShift h r (P.map (algebraMap ℝ ℂ)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [iterateEvenTaylor_succ]
    rw [evenTaylor_map h N _ ((iterateEvenTaylor_degree h N r P).trans_lt hN)]
    change SymmetricPolynomialStrip.symmetricShift h
      ((iterateEvenTaylor h N r P).map (algebraMap ℝ ℂ))=_
    rw [ih]
    simp only [SymmetricPolynomialStrip.iteratedShift,Function.iterate_succ_apply']

def scaledEvenTaylor (s : ℝ) (n : ℕ) (P : ℝ[X]) : ℝ[X] :=
  iterateEvenTaylor (Real.sqrt (2*s/((n+1:ℕ):ℝ))) (P.natDegree+1) (n+1) P

theorem scaledEvenTaylor_degree (s : ℝ) (n : ℕ) (P : ℝ[X]) :
    (scaledEvenTaylor s n P).natDegree≤P.natDegree :=
  iterateEvenTaylor_degree _ _ _ P

theorem scaledEvenTaylor_map (s : ℝ) (n : ℕ) (P : ℝ[X]) :
    (scaledEvenTaylor s n P).map (algebraMap ℝ ℂ)=
      SymmetricPolynomialStrip.scaledShift s n (P.map (algebraMap ℝ ℂ)) :=
  iterateEvenTaylor_map _ (P.natDegree+1) (n+1) P (by omega)

open FactorialAnalyticDomain in
theorem scaledEvenTaylor_jet_limit (s : ℝ) (hs : 0≤s) (P : ℝ[X]) :
    Tendsto (fun n => polynomial (scaledEvenTaylor s n P)) atTop
      (𝓝 (polynomial (PureOrderPolynomialTransport.transport 2 (-s) P))) := by
  have he (n : ℕ) : polynomial (scaledEvenTaylor s n P)=
      ((1+(1/((n+1:ℕ):ℝ)) • PolynomialDerivativeEuler.correction P.natDegree s n)^(n+1))
        (polynomial P) := by
    apply iterateEvenTaylor_jet
    exact Real.sq_sqrt (div_nonneg (by linarith) (by positivity))
  simp_rw [he]
  exact PolynomialDerivativeEuler.correction_euler_polynomial_limit P.natDegree s P

end OperatorDerivativeRewrite.Foundation.SymmetricPolynomialTaylor
