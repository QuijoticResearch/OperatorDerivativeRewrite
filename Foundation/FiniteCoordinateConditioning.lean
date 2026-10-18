import Foundation.SingleCoordinateConditioning

/-! Actual finite signed conditioning and its uniform position-coordinate bound. -/
noncomputable section
open scoped NNReal BigOperators

namespace OperatorDerivativeRewrite.Foundation.FiniteCoordinateConditioning
open SingleCoordinateConditioning MultivariateDirectionalKernel
open PureOrderPolynomialConditioning
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem eraseValue_direction (j : ι) (v x : ι → ℝ) (hv : v j = 0) (z : ℝ) :
    eraseValue j (fun i => x i + z*v i) = fun i => eraseValue j x i + z*v i := by
  funext i
  by_cases hi : i=j <;> simp [eraseValue, hi, hv]

omit [Fintype ι] in
theorem line_zeroCoordinate (j : ι) (v x : ι → ℝ) (hv : v j = 0) (P : MvPolynomial ι ℝ) :
    line v x (zeroCoordinate j P) = line v (eraseValue j x) P := by
  apply Polynomial.funext
  intro z
  rw [eval_line, eval_zeroCoordinate, eval_line, eraseValue_direction j v x hv z]

omit [Fintype ι] in
theorem heat_zeroCoordinate (p : ℕ) (hp : 0 < p) (a : ℝ) (j : ι) (v : ι → ℝ)
    (hv : v j = 0) (P : MvPolynomial ι ℝ) :
    transport p hp a v (zeroCoordinate j P) = zeroCoordinate j (transport p hp a v P) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_zeroCoordinate]
  change MvPolynomial.eval x
    (MultivariateFactorialHeat.polynomialEvolution p a v (zeroCoordinate j P)) =
    MvPolynomial.eval (eraseValue j x) (MultivariateFactorialHeat.polynomialEvolution p a v P)
  rw [← expectation_polynomialEvolution p hp, ← expectation_polynomialEvolution p hp,
    line_zeroCoordinate j v x hv]

def zeroChain : List ι → MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial ι ℝ
  | [] => AlgHom.id ℝ _
  | j::js => (zeroCoordinate j).comp (zeroChain js)

def heatChain (p : ℕ) (hp : 0 < p) (a : ι → ℝ) :
    List ι → MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ
  | [] => LinearMap.id
  | j::js => (transport p hp (a j) (Pi.single j 1)).comp (heatChain p hp a js)

def conditioningChain (p : ℕ) (a : ι → ℝ) :
    List ι → MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ
  | [] => LinearMap.id
  | j::js => (conditioning p a (Finset.univ.erase j)).comp (conditioningChain p a js)

omit [Fintype ι] in
theorem heat_zeroChain (p : ℕ) (hp : 0 < p) (a : ℝ) (j : ι) (js : List ι)
    (hj : j ∉ js) (P : MvPolynomial ι ℝ) :
    transport p hp a (Pi.single j 1) (zeroChain js P) =
      zeroChain js (transport p hp a (Pi.single j 1) P) := by
  induction js with
  | nil => rfl
  | cons k ks ih =>
    have hjk : j ≠ k := fun h => hj (by simp [h])
    have hjks : j ∉ ks := fun h => hj (List.mem_cons_of_mem k h)
    change transport p hp a (Pi.single j 1) (zeroCoordinate k (zeroChain ks P)) = _
    rw [heat_zeroCoordinate p hp a k (Pi.single j 1) (by simp [hjk])]
    rw [ih hjks]
    rfl

theorem conditioningChain_eq (p : ℕ) (a : ι → ℝ) (js : List ι) (P : MvPolynomial ι ℝ) :
    conditioningChain p a js P = conditioning p a (Finset.univ \ js.toFinset) P := by
  induction js with
  | nil => simp only [conditioningChain, LinearMap.id_apply, List.toFinset_nil,
      Finset.sdiff_empty, conditioning_univ]
  | cons j js ih =>
    change conditioning p a (Finset.univ.erase j) (conditioningChain p a js P) = _
    rw [ih, conditioning_tower]
    apply congrArg (fun S : Finset ι => conditioning p a S P)
    ext i
    simp

theorem conditioningChain_factor (p : ℕ) (hp : 0 < p) (a : ι → ℝ) (js : List ι)
    (hjs : js.Nodup) (P : MvPolynomial ι ℝ) :
    conditioningChain p a js P = zeroChain js (heatChain p hp a js P) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    have hj := (List.nodup_cons.mp hjs).1
    have htail := (List.nodup_cons.mp hjs).2
    change conditioning p a (Finset.univ.erase j) (conditioningChain p a js P) = _
    rw [← heat_then_zero p hp, ih htail, heat_zeroChain p hp (a j) j js hj]
    rfl

theorem conditioning_factor (p : ℕ) (hp : 0 < p) (a : ι → ℝ) (js : List ι)
    (hjs : js.Nodup) (P : MvPolynomial ι ℝ) :
    conditioning p a (Finset.univ \ js.toFinset) P = zeroChain js (heatChain p hp a js P) := by
  rw [← conditioningChain_eq, conditioningChain_factor p hp a js hjs]

omit [Fintype ι] in
theorem eval_zeroChain (js : List ι) (x : ι → ℝ) (P : MvPolynomial ι ℝ) :
    MvPolynomial.eval x (zeroChain js P) =
      MvPolynomial.eval (fun i => if i ∈ js then 0 else x i) P := by
  induction js generalizing x with
  | nil => simp only [zeroChain, AlgHom.id_apply, List.not_mem_nil, ite_false]
  | cons j js ih =>
    change MvPolynomial.eval x (zeroCoordinate j (zeroChain js P)) = _
    rw [eval_zeroCoordinate, ih]
    apply congrArg (fun y : ι → ℝ => MvPolynomial.eval y P)
    funext i
    by_cases hi : i=j <;> by_cases hjs : i ∈ js <;> simp [eraseValue, hi, hjs]

end OperatorDerivativeRewrite.Foundation.FiniteCoordinateConditioning
