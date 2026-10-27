import Foundation.AnchoredCovariance
import Mathlib.Analysis.InnerProductSpace.GramMatrix
open scoped BigOperators
/-! Finite-sample covariance criterion without a required sampled zero.
Adjoining an anchor proves the symbol equivalence. Actual Hilbert increment
representations and the verified fractional covariance supply positive cases.
This is classical covariance structure, not a process or curvature theorem. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourierCovarianceCriterion
open AnchoredCovariance FiniteFourierDifferentialTrace FiniteStableGamma.Core
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def withZero (k : ι → Wave) : Option ι → Wave := fun i => Option.elim i 0 k
theorem negative_restrict (d : Option ι → Option ι → ℝ) (hd : CondNegative d) :
    CondNegative (fun i j => d (some i) (some j)) := by
  intro c hc
  have h := hd (fun i => Option.elim i 0 c) (by simpa [Fintype.sum_option] using hc)
  simpa [energy,Fintype.sum_option] using h
theorem kernel_psd_of_augmented (ψ : Wave → ℝ) (h0 : ψ 0=0) (he : ∀ k,ψ (-k)=ψ k)
    (k : ι → Wave) (h : CondNegative (fun i j => ψ (withZero k j-withZero k i))) :
    Matrix.PosSemidef (fun i j => kernel ψ (k i) (k j)) := by
  have hp := (fourier_covariance_iff ψ h0 he (withZero k) none rfl).mpr h
  exact hp.submatrix some
def NegativeSymbol (ψ : Wave → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (k : ι → Wave), CondNegative (fun i j => ψ (k j-k i))
def CovarianceSymbol (ψ : Wave → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (k : ι → Wave), Matrix.PosSemidef (fun i j => kernel ψ (k i) (k j))
theorem symbol_iff (ψ : Wave → ℝ) (h0 : ψ 0=0) (he : ∀ k,ψ (-k)=ψ k) :
    CovarianceSymbol ψ ↔ NegativeSymbol ψ := by
  constructor
  · intro h ι _ _ k
    have hp := (fourier_covariance_iff ψ h0 he (withZero k) none rfl).mp (h _ (withZero k))
    exact negative_restrict _ hp
  · intro h ι _ _ k
    exact kernel_psd_of_augmented ψ h0 he k (h _ (withZero k))
theorem stable_covariance (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) : CovarianceSymbol (stableSymbol γ) := by
  intro ι _ _ k
  have h := FractionalCovarianceMatrices.covarianceMatrix_posSemidef (γ/2) (by linarith) (by linarith) (fun i => (k i 0:ℝ))
  have he : (fun i j => kernel (stableSymbol γ) (k i) (k j)) =
      FractionalCovarianceMatrices.covarianceMatrix (γ/2) (fun i => (k i 0:ℝ)) := by
    funext i j
    exact stable_kernel_covariance γ (k i) (k j)
  rw [he]
  exact h
theorem stable_negative (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) : NegativeSymbol (stableSymbol γ) := by
  apply (symbol_iff (stableSymbol γ) ?_ ?_).mp (stable_covariance γ hγ hγ2)
  · simp [stableSymbol,Real.zero_rpow (ne_of_gt hγ)]
  · intro k
    simp [stableSymbol]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem hilbert_kernel (ψ : Wave → ℝ) (v : Wave → H)
    (hn : ∀ k,ψ k=‖v k‖^2) (hd : ∀ k l,ψ (l-k)=‖v l-v k‖^2) (k l : Wave) :
    kernel ψ k l = inner ℝ (v k) (v l) := by
  rw [kernel,hn k,hn l,hd k l,norm_sub_sq_real,real_inner_comm (v l) (v k)]
  ring
theorem hilbert_covariance (ψ : Wave → ℝ) (v : Wave → H)
    (hn : ∀ k,ψ k=‖v k‖^2) (hd : ∀ k l,ψ (l-k)=‖v l-v k‖^2) :
    CovarianceSymbol ψ := by
  intro ι _ _ k
  have he : (fun i j => kernel ψ (k i) (k j)) = Matrix.gram ℝ (fun i => v (k i)) := by
    funext i j
    exact hilbert_kernel ψ v hn hd (k i) (k j)
  rw [he]
  exact Matrix.posSemidef_gram ℝ _
theorem hilbert_negative (ψ : Wave → ℝ) (v : Wave → H)
    (hn : ∀ k,ψ k=‖v k‖^2) (hd : ∀ k l,ψ (l-k)=‖v l-v k‖^2) :
    NegativeSymbol ψ := by
  have h0 : ψ 0=0 := by simpa using hd 0 0
  have he (k : Wave) : ψ (-k)=ψ k := by
    have h1 := hd k 0
    have h2 := hd 0 k
    simp only [zero_sub,sub_zero] at h1 h2
    rw [h1,h2,norm_sub_rev]
  exact (symbol_iff ψ h0 he).mp (hilbert_covariance ψ v hn hd)

end OperatorDerivativeRewrite.Foundation.FourierCovarianceCriterion
