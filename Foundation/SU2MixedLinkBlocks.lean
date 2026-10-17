import Foundation.SU2OrderedLinkHessian

/-! Mixed partials preserve the factor order; link-block transposition preserves symmetry. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2MixedLinkBlocks
set_option backward.isDefEq.respectTransparency false
open SU2TraceHessianModel SU2ProductCurveHessian SU2OrderedLinkHessian
open ChristoffelSkewCancellation

def twoAction (U B C : M2) (s t : ℝ) : ℝ :=
  wilson (U*NormedSpace.exp (s • B)*NormedSpace.exp (t • C))
def firstSlope (U B C : M2) (s t : ℝ) : ℝ :=
  -traceReal ((U*(B*NormedSpace.exp (s • B)))*NormedSpace.exp (t • C))/2
def secondSlope (U B C : M2) (s t : ℝ) : ℝ :=
  -traceReal ((U*NormedSpace.exp (s • B))*(C*NormedSpace.exp (t • C)))/2

theorem first_hasDerivAt (U B C : M2) (s t : ℝ) :
    HasDerivAt (fun a => twoAction U B C a t) (firstSlope U B C s t) s := by
  have hm := ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) B s).const_mul U).mul_const
    (NormedSpace.exp (t • C))
  have ht := realTraceCLM.hasFDerivAt.comp_hasDerivAt s hm
  change HasDerivAt (fun a : ℝ => traceReal (U*NormedSpace.exp (a • B)*
    NormedSpace.exp (t • C)))
    (traceReal ((U*(B*NormedSpace.exp (s • B)))*NormedSpace.exp (t • C))) s at ht
  have hh := (hasDerivAt_const s (1:ℝ)).sub (ht.div_const 2)
  convert hh using 1 <;> first | rfl | (dsimp [firstSlope]; ring)

theorem second_hasDerivAt (U B C : M2) (s t : ℝ) :
    HasDerivAt (twoAction U B C s) (secondSlope U B C s t) t :=
  curve_hasDerivAt (U*NormedSpace.exp (s • B)) C t

theorem mixed_first_then_second (U B C : M2) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => twoAction U B C s t) 0) 0=
      -traceReal (U*B*C)/2 := by
  have he : (fun t : ℝ => deriv (fun s : ℝ => twoAction U B C s t) 0)=
      firstSlope U B C 0 := funext (fun t => (first_hasDerivAt U B C 0 t).deriv)
  rw [he]
  have hm := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) C 0).const_mul (U*B)
  have ht := realTraceCLM.hasFDerivAt.comp_hasDerivAt 0 hm
  have hh := ht.neg.div_const 2
  have hf : firstSlope U B C 0=(fun t : ℝ => -realTraceCLM ((U*B)*NormedSpace.exp (t • C))/2) := by
    funext t
    simp [firstSlope, realTraceCLM_apply]
  rw [hf]
  simpa [realTraceCLM_apply] using hh.deriv

theorem mixed_second_then_first (U B C : M2) :
    deriv (fun s : ℝ => deriv (twoAction U B C s) 0) 0=
      -traceReal (U*B*C)/2 := by
  have he : (fun s : ℝ => deriv (twoAction U B C s) 0)=
      (fun s : ℝ => secondSlope U B C s 0) :=
    funext (fun s => (second_hasDerivAt U B C s 0).deriv)
  rw [he]
  have hm := ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) B 0).const_mul U).mul_const C
  have ht := realTraceCLM.hasFDerivAt.comp_hasDerivAt 0 hm
  have hh := ht.neg.div_const 2
  have hf : (fun s : ℝ => secondSlope U B C s 0)=
      (fun s : ℝ => -realTraceCLM ((U*NormedSpace.exp (s • B))*C)/2) := by
    funext s
    simp [secondSlope, realTraceCLM_apply]
  rw [hf]
  simpa [realTraceCLM_apply] using hh.deriv

theorem mixed_partials_equal (U B C : M2) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => twoAction U B C s t) 0) 0=
      deriv (fun s : ℝ => deriv (twoAction U B C s) 0) 0 := by
  rw [mixed_first_then_second, mixed_second_then_first]

theorem ordered_difference_gradient (U B C : M2) :
    deriv (deriv (action U B C)) 0-deriv (deriv (curve U (B+C))) 0=
      deriv (curve U (B*C-C*B)) 0 := by
  rw [ordered_difference]
  simpa [SU2ProductCurveHessian.slope] using (curve_hasDerivAt U (B*C-C*B) 0).deriv.symm

variable {I : Type*} [Fintype I]

def linkBlock (M : Matrix I I ℝ) : Matrix (I ⊕ I) (I ⊕ I) ℝ
  | .inl a, .inr b => M a b
  | .inr b, .inl a => M a b
  | _, _ => 0
def linkVector (x y : I → ℝ) : I ⊕ I → ℝ := Sum.elim x y

omit [Fintype I] in
theorem linkBlock_symmetric (M : Matrix I I ℝ) (i j : I ⊕ I) :
    linkBlock M j i=linkBlock M i j := by cases i <;> cases j <;> rfl

theorem contraction_transpose (M : Matrix I I ℝ) (x y : I → ℝ) :
    contraction M.transpose y x=contraction M x y := by
  unfold contraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Matrix.transpose_apply]
  ring

theorem linkBlock_contraction (M : Matrix I I ℝ) (x y : I → ℝ) :
    contraction (linkBlock M) (linkVector x y) (linkVector x y)=2*contraction M x y := by
  have he : contraction (linkBlock M) (linkVector x y) (linkVector x y)=
      contraction M x y+contraction M.transpose y x := by
    simp [contraction, Fintype.sum_sum_type, linkBlock, linkVector]
  rw [he, contraction_transpose]
  ring

theorem linkBlock_same_color_zero (M : Matrix I I ℝ)
    (hM : ∀ a b, M b a= -M a b) (x : I → ℝ) :
    contraction (linkBlock M) (linkVector x x) (linkVector x x)=0 := by
  rw [linkBlock_contraction, contraction_diagonal_zero M hM x, mul_zero]

def mixedBlock (U : M2) (a b : Fin 3) : ℝ := -traceReal (U*tangent a*tangent b)/2
def colorCorrection (U : M2) (a b : Fin 3) : ℝ :=
  -traceReal (U*(tangent a*tangent b-tangent b*tangent a))/4

theorem mixedBlock_actual (U : M2) (a b : Fin 3) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => twoAction U (tangent a) (tangent b) s t) 0) 0=
      mixedBlock U a b := mixed_first_then_second U (tangent a) (tangent b)

theorem colorCorrection_antisym_part (U : M2) (a b : Fin 3) :
    colorCorrection U a b=(mixedBlock U a b-mixedBlock U b a)/2 := by
  simp only [colorCorrection, mixedBlock, mul_sub, Matrix.mul_assoc, traceReal,
    Matrix.trace_sub, Complex.sub_re]
  ring

theorem colorCorrection_skew (U : M2) (a b : Fin 3) :
    colorCorrection U b a= -colorCorrection U a b := by
  rw [colorCorrection_antisym_part, colorCorrection_antisym_part]
  ring

theorem colorBlock_contraction (θ : ℝ) :
    contraction (linkBlock (colorCorrection (rotation θ)))
      (linkVector (Pi.single (0:Fin 3) 1) (Pi.single (1:Fin 3) 1))
      (linkVector (Pi.single (0:Fin 3) 1) (Pi.single (1:Fin 3) 1))=Real.sin θ/2 := by
  rw [linkBlock_contraction]
  norm_num [contraction, Fin.sum_univ_three, Pi.single_apply]
  have hh := normalized_commutator θ
  unfold colorCorrection
  linarith

theorem colorBlock_matches_actual (θ : ℝ) :
    contraction (linkBlock (colorCorrection (rotation θ)))
      (linkVector (Pi.single (0:Fin 3) 1) (Pi.single (1:Fin 3) 1))
      (linkVector (Pi.single (0:Fin 3) 1) (Pi.single (1:Fin 3) 1))=correction θ := by
  rw [colorBlock_contraction, correction_eq]

theorem colorBlock_nonzero (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    contraction (linkBlock (colorCorrection (rotation θ)))
      (linkVector (Pi.single (0:Fin 3) 1) (Pi.single (1:Fin 3) 1))
      (linkVector (Pi.single (0:Fin 3) 1) (Pi.single (1:Fin 3) 1)) ≠ 0 := by
  rw [colorBlock_contraction]
  exact div_ne_zero hθ (by norm_num)

theorem colorBlock_not_full_skew (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    ¬ ∀ i j, linkBlock (colorCorrection (rotation θ)) j i=
      -linkBlock (colorCorrection (rotation θ)) i j := by
  intro hh
  have hz := contraction_diagonal_zero (linkBlock (colorCorrection (rotation θ))) hh
    (linkVector (Pi.single (0:Fin 3) 1) (Pi.single (1:Fin 3) 1))
  exact colorBlock_nonzero θ hθ hz

end OperatorDerivativeRewrite.Foundation.SU2MixedLinkBlocks
