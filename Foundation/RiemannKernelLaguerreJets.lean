import Foundation.RiemannQuarticTaylorJets
import Foundation.RiemannQuarticSaddleTimes
noncomputable section
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.RiemannKernelLaguerreJets
open RiemannQuarticTaylorJets

/-- Differential Laguerre transform, with ordinary derivatives. -/
def laguerre (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x * deriv f x - f x * deriv (deriv f) x

/-- Iteration acts on FUNCTIONS before evaluation, not on point values. -/
def hierarchy (f : ℝ → ℝ) : ℕ → (ℝ → ℝ)
  | 0 => f
  | k+1 => laguerre (hierarchy f k)

/-- Exact normalized-derivative recurrence corresponding to the transform. -/
def laguerreJet (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (n+1), (((i+1:ℕ):ℝ)*a (i+1))*(((n-i+1:ℕ):ℝ)*a (n-i+1))) -
  (∑ i ∈ Finset.range (n+1), a i*(((n-i+1:ℕ):ℝ)*((n-i+2:ℕ):ℝ)*a (n-i+2)))

def jetHierarchy (a : ℕ → ℝ) : ℕ → (ℕ → ℝ)
  | 0 => a
  | k+1 => laguerreJet (jetHierarchy a k)

private theorem coefficient_mul_at (f g : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    coefficient (fun u => f u*g u) n x=
      ∑ i ∈ Finset.range (n+1),coefficient f i x*coefficient g (n-i) x := by
  simp only [coefficient]
  rw [iteratedDeriv_fun_mul (hf.of_le (by simp)) (hg.of_le (by simp)),Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i≤n := by have := Finset.mem_range.mp hi;omega
  have hfac : (n.choose i:ℝ)*(i.factorial:ℝ)*((n-i).factorial:ℝ)=(n.factorial:ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hn : (n.factorial:ℝ)≠0 := by positivity
  have hi0 : (i.factorial:ℝ)≠0 := by positivity
  have hni : ((n-i).factorial:ℝ)≠0 := by positivity
  rw [div_mul_div_comm]
  apply (div_eq_div_iff hn (mul_ne_zero hi0 hni)).mpr
  rw [← hfac]
  ring

private theorem coefficient_sub_at (f g : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    coefficient (fun u => f u-g u) n x=coefficient f n x-coefficient g n x := by
  unfold coefficient
  rw [iteratedDeriv_fun_sub (hf.of_le (by simp)) (hg.of_le (by simp))]
  ring

theorem laguerre_contDiffAt (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (laguerre f) x := by
  have hd := hf.derivWithin (by simp : (∞:ℕ∞ω)+1≤∞)
  have hdd := hd.derivWithin (by simp : (∞:ℕ∞ω)+1≤∞)
  exact (hd.mul hd).sub (hf.mul hdd)

theorem coefficient_laguerre (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    coefficient (laguerre f) n x=laguerreJet (fun i => coefficient f i x) n := by
  have hd := hf.derivWithin (by simp : (∞:ℕ∞ω)+1≤∞)
  have hdd := hd.derivWithin (by simp : (∞:ℕ∞ω)+1≤∞)
  change coefficient (fun u => deriv f u*deriv f u-f u*deriv (deriv f) u) n x=_
  rw [coefficient_sub_at _ _ x (hd.mul hd) (hf.mul hdd) n,
    coefficient_mul_at _ _ x hd hd n,coefficient_mul_at _ _ x hf hdd n]
  simp_rw [coefficient_deriv]
  unfold laguerreJet
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_assoc] <;> ring

theorem hierarchy_contDiffAt (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ ∞ f x) (k : ℕ) :
    ContDiffAt ℝ ∞ (hierarchy f k) x := by
  induction k with
  | zero => exact hf
  | succ k ih => exact laguerre_contDiffAt _ x ih

theorem coefficient_hierarchy (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ ∞ f x) (k n : ℕ) :
    coefficient (hierarchy f k) n x=jetHierarchy (fun i => coefficient f i x) k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [hierarchy,coefficient_laguerre _ x (hierarchy_contDiffAt f x hf k) n]
    simp only [ih,jetHierarchy]

theorem laguerreJet_congr (a b : ℕ → ℝ) (n : ℕ) (h : ∀ i≤n+2,a i=b i) :
    laguerreJet a n=laguerreJet b n := by
  unfold laguerreJet
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
  · have hi' := Finset.mem_range.mp hi
    rw [h (i+1) (by omega),h (n-i+1) (by omega)]
  · rw [h i (by have := Finset.mem_range.mp hi;omega),h (n-i+2) (by omega)]

/-- At level k and output order n, exactly the input jet through n+2k suffices. -/
theorem jetHierarchy_congr (a b : ℕ → ℝ) (k n : ℕ) (h : ∀ i≤n+2*k,a i=b i) :
    jetHierarchy a k n=jetHierarchy b k n := by
  induction k generalizing n with
  | zero => exact h n (by omega)
  | succ k ih =>
    apply laguerreJet_congr
    intro i hi
    apply ih
    intro j hj
    exact h j (by omega)

/-- The ACTUAL theta kernel in the positive square-root coordinate. -/
def kernelCurve (t : ℝ) : ℝ := RiemannQuarticKernel.kernel (Real.sqrt t)

theorem kernelCurve_contDiffAt (t : ℝ) (ht : 0<t) : ContDiffAt ℝ ∞ kernelCurve t := by
  exact ((RiemannQuarticSaddleTimes.kernel_analyticAt (Real.sqrt t)).contDiffAt).comp t
    (Real.contDiffAt_sqrt ht.ne')

/-- Exact finite-jet reduction for the actual fifth transform. This is an
identity, not a numerical sign certificate. -/
theorem actual_fifth_exact (t : ℝ) (ht : 0<t) :
    hierarchy kernelCurve 5 t=jetHierarchy (fun i => coefficient kernelCurve i t) 5 0 := by
  simpa only [coefficient_zero] using coefficient_hierarchy kernelCurve t (kernelCurve_contDiffAt t ht) 5 0

/-- No derivative beyond order10 is needed by this particular sign question. -/
theorem actual_fifth_of_ten_jet (t : ℝ) (ht : 0<t) (a : ℕ → ℝ)
    (ha : ∀ i≤10,coefficient kernelCurve i t=a i) :
    hierarchy kernelCurve 5 t=jetHierarchy a 5 0 := by
  rw [actual_fifth_exact t ht]
  exact jetHierarchy_congr _ a 5 0 ha


/-- A fixed rescaling multiplies the next transform by its square. -/
theorem laguerreJet_scale (a : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    laguerreJet (fun i => c*a i) n=c^2*laguerreJet a n := by
  unfold laguerreJet
  rw [mul_sub,Finset.mul_sum,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

theorem jetHierarchy_scale (a : ℕ → ℝ) (c : ℝ) (k n : ℕ) :
    jetHierarchy (fun i => c*a i) k n=c^(2^k)*jetHierarchy a k n := by
  induction k generalizing n with
  | zero => simp [jetHierarchy]
  | succ k ih =>
    have he : jetHierarchy (fun i => c*a i) k=(fun i => c^(2^k)*jetHierarchy a k i) := funext ih
    rw [jetHierarchy,he,laguerreJet_scale,← pow_mul,Nat.pow_succ]
    rfl

/-- Per-stage normalization by a NONZERO fixed constant preserves the sign.
Normalizing by a varying function would be a different differential operation. -/
theorem laguerreJet_scale_neg_iff (a : ℕ → ℝ) (c : ℝ) (hc : c≠0) (n : ℕ) :
    laguerreJet (fun i => c*a i) n<0 ↔ laguerreJet a n<0 := by
  rw [laguerreJet_scale]
  have hp := sq_pos_of_ne_zero hc
  constructor
  · intro h
    by_contra hx
    exact (not_lt_of_ge (mul_nonneg hp.le (le_of_not_gt hx))) h
  · exact mul_neg_of_pos_of_neg hp

end OperatorDerivativeRewrite.Foundation.RiemannKernelLaguerreJets
