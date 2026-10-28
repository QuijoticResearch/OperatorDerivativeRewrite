import Foundation.SU2SevenLinkSpatialSeparation
import Foundation.SU2StrongCouplingCovariance

/-! The actual right-path center sector of the spatial seven-link transfer.
This centers the variational trial against every even bounded vacuum candidate;
existence of a positive eigenfunction is not assumed as an axiom. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkParity
open QuaternionSU2Representation SU2WilsonConvolution SU2SevenLinkTransfer SU2SevenLinkVariational
open SU2SevenLinkOddTrial SU2StrongCouplingCovariance

/-- Multiply just the first private right-path link by the nontrivial SU(2) center. -/
def center : State := (1,1,1,1,SU2StapleExtremes.minusOne,1,1)

def flip (s : State) : State := center*s

theorem flip_measurable : Measurable flip := (continuous_const_mul center).measurable

theorem first_flip (s : State) : first (flip s)=first s := by
  simp [flip,center,first,leftPath]

theorem rightPath_flip (s : State) : rightPath (flip s)=SU2StapleExtremes.minusOne*rightPath s := by
  simp [flip,center,rightPath,mul_assoc]

private theorem trace_middle_center (L R : SU2) :
    halfTrace (L*(SU2StapleExtremes.minusOne*R)) = -halfTrace (L*R) := by
  rw [halfTrace_mul_comm L _,mul_assoc,halfTrace_center_neg,halfTrace_mul_comm R L]

theorem second_flip (s : State) : second (flip s)= -second s := by
  unfold second
  rw [rightPath_flip]
  have hu : (flip s).1=s.1 := by simp [flip,center]
  rw [hu]
  exact trace_middle_center _ _

theorem meanChannel_flip (s : State) : meanChannel (flip s)= -meanChannel s := by
  change halfTrace (leftPath (flip s)*rightPath (flip s))/4= -meanChannel s
  rw [rightPath_flip]
  have hl : leftPath (flip s)=leftPath s := by simp [flip,center,leftPath]
  rw [hl,trace_middle_center]
  change -halfTrace (leftPath s*rightPath s)/4= -(halfTrace (leftPath s*rightPath s)/4)
  ring

theorem residual_flip (s : State) : residual (flip s)= -residual s := by
  change first (flip s)*second (flip s)-meanChannel (flip s)= -(first s*second s-meanChannel s)
  rw [first_flip,second_flip,meanChannel_flip]
  ring

theorem oddPolynomial_flip (t A B : ℝ) (s : State) :
    oddPolynomial t A B (flip s)= -oddPolynomial t A B s := by
  simp only [oddPolynomial_pointwise,second_flip,meanChannel_flip,residual_flip]
  ring

theorem unweight_flip (t : ℝ) (f : State → ℝ) (hf : ∀ s, f (flip s)= -f s) (s : State) :
    unweight t f (flip s)= -unweight t f s := by
  unfold unweight
  rw [first_flip,hf]
  ring

theorem trial_flip (t A B : ℝ) (s : State) :
    unweight t (oddPolynomial t A B) (flip s)= -unweight t (oddPolynomial t A B) s :=
  unweight_flip t _ (oddPolynomial_flip t A B) s

/-- Actual spatial transfer preserves this center sector; convolution commutes
with the literal left translation and the half weights are unchanged. -/
theorem spatialStep_flip (β t : ℝ) (f : State → ℝ) (s : State) :
    spatialStep β t f (flip s)=spatialStep β t (fun r => f (flip r)) s := by
  unfold spatialStep SU2SevenLinkTransfer.step
  rw [first_flip]
  apply congrArg (fun z : ℝ => Real.exp (t*first s/2)*z)
  apply integral_congr_ae
  filter_upwards with v
  have he : flip s*v=flip (s*v) := mul_assoc center s v
  rw [he,first_flip]

theorem spatialStep_odd (β t : ℝ) (f : State → ℝ) (hf : ∀ s, f (flip s)= -f s) (s : State) :
    spatialStep β t f (flip s)= -spatialStep β t f s := by
  rw [spatialStep_flip]
  unfold spatialStep SU2SevenLinkTransfer.step
  simp_rw [hf,mul_neg,integral_neg]
  ring

/-- Product Haar is invariant under this actual one-link transformation.
Right invariance is already verified; center multiplication also equals right
multiplication on that coordinate. -/
private theorem minusOne_central (C : SU2) :
    SU2StapleExtremes.minusOne*C=C*SU2StapleExtremes.minusOne := by
  apply Subtype.ext
  change QuaternionSU2Representation.repr (-1)*(C : SU2TraceHessianModel.M2)=(C : SU2TraceHessianModel.M2)*QuaternionSU2Representation.repr (-1)
  have hr : QuaternionSU2Representation.repr (-1)= -(1 : SU2TraceHessianModel.M2) := by
    simpa using repr_real (-1)
  rw [hr]
  simp

private theorem center_central (s : State) : center*s=s*center := by
  have h := minusOne_central s.2.2.2.2.1
  simpa [center,Prod.ext_iff] using h

theorem integral_flip (f : State → ℝ) : (∫ s, f (flip s) ∂haar)=∫ s, f s ∂haar := by
  have he (s : State) : flip s=s*center := center_central s
  simp_rw [he]
  exact integral_mul_right_eq_self f center

/-- Exact centering against EVERY even weight, not just the polynomial vacuum.
This algebraic Bochner identity does not assert L1 membership. The actual
ground-transform application separately proves boundedness and its L2 domain. -/
theorem odd_even_orthogonal (f g : State → ℝ)
    (hf : ∀ s, f (flip s)= -f s) (hg : ∀ s, g (flip s)=g s) :
    (∫ s, f s*g s ∂haar)=0 := by
  have h := integral_flip (fun s => f s*g s)
  simp_rw [hf,hg,neg_mul,integral_neg] at h
  linarith

theorem trial_orthogonal (t A B : ℝ) (ψ : State → ℝ) (hψ : ∀ s, ψ (flip s)=ψ s) :
    (∫ s, unweight t (oddPolynomial t A B) s*ψ s ∂haar)=0 :=
  odd_even_orthogonal _ ψ (trial_flip t A B) hψ

theorem flip_flip (s : State) : flip (flip s)=s := by
  have hz : SU2StapleExtremes.minusOne*SU2StapleExtremes.minusOne=(1 : SU2) := by
    apply Subtype.ext
    change QuaternionSU2Representation.repr (-1)*QuaternionSU2Representation.repr (-1)=1
    have hr : QuaternionSU2Representation.repr (-1)= -(1 : SU2TraceHessianModel.M2) := by
      simpa using repr_real (-1)
    rw [hr]
    simp
  have hc : center*center=(1 : State) := by simpa [center,Prod.ext_iff] using hz
  unfold flip
  rw [← mul_assoc,hc,one_mul]

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkParity
