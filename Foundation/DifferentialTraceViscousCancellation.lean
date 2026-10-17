import Foundation.CommutingDerivationHelicity

/-! Miller-type viscous orthogonality from commuting derivations and an
invariant trace. Concrete Fourier/periodic realizations remain separate. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.DifferentialTraceViscousCancellation
open CommutingDerivationHelicity
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

variable {𝕜 A : Type*} [Field 𝕜] [CharZero 𝕜] [CommRing A] [Algebra 𝕜 A]

def lap (D : Fin 3 → Derivation 𝕜 A A) (f : A) : A := ∑ k, D k (D k f)
def vectorLap (D : Fin 3 → Derivation 𝕜 A A) (u : Fin 3 → A) : Fin 3 → A := fun i => lap D (u i)
def twiceStrain (D : Fin 3 → Derivation 𝕜 A A) (u : Fin 3 → A) (i j : Fin 3) : A :=
  D j (u i)+D i (u j)
def strain (D : Fin 3 → Derivation 𝕜 A A) (u : Fin 3 → A) (i j : Fin 3) : A :=
  (1/2 : 𝕜) • twiceStrain D u i j

theorem lap_add (D : Fin 3 → Derivation 𝕜 A A) (f g : A) :
    lap D (f+g)=lap D f+lap D g := by
  simp only [lap,map_add,Finset.sum_add_distrib]

theorem lap_smul (D : Fin 3 → Derivation 𝕜 A A) (c : 𝕜) (f : A) :
    lap D (c • f)=c • lap D f := by
  simp only [lap,Derivation.map_smul,Finset.smul_sum]

theorem lap_derivative (D : Fin 3 → Derivation 𝕜 A A)
    (hcomm : ∀ i j f, D i (D j f)=D j (D i f)) (i : Fin 3) (f : A) :
    lap D (D i f)=D i (lap D f) := by
  simp only [lap,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [hcomm k i f,hcomm k i (D k f)]

theorem lap_twiceStrain (D : Fin 3 → Derivation 𝕜 A A)
    (hcomm : ∀ i j f, D i (D j f)=D j (D i f)) (u : Fin 3 → A) (i j : Fin 3) :
    lap D (twiceStrain D u i j)=twiceStrain D (vectorLap D u) i j := by
  rw [twiceStrain,lap_add,lap_derivative D hcomm,lap_derivative D hcomm]
  rfl

theorem curl_curl (D : Fin 3 → Derivation 𝕜 A A)
    (hcomm : ∀ i j f, D i (D j f)=D j (D i f)) (u : Fin 3 → A) :
    curl D (curl D u)=gradient D (divergence D u)-vectorLap D u := by
  ext i
  fin_cases i <;>
    norm_num [curl,axis,jacobian,gradient,divergence,vectorLap,lap,Fin.sum_univ_succ,map_add,map_sub] <;>
    simp only [hcomm 1 0,hcomm 2 0,hcomm 2 1] <;> abel

theorem lap_eq_neg_curl_curl (D : Fin 3 → Derivation 𝕜 A A)
    (hcomm : ∀ i j f, D i (D j f)=D j (D i f)) (u : Fin 3 → A)
    (hu : divergence D u=0) : vectorLap D u=-(curl D (curl D u)) := by
  have h := curl_curl D hcomm u
  rw [hu] at h
  have hg : gradient D (0 : A)=0 := by
    ext i
    exact map_zero (D i)
  rw [hg,zero_sub] at h
  simpa using congrArg Neg.neg h.symm

def linearContraction (D : Fin 3 → Derivation 𝕜 A A) (w v : Fin 3 → A) : A :=
  ∑ j, dotProduct (gradient D (v j)) (fun i => w i*w j)

theorem symmetric_contraction (D : Fin 3 → Derivation 𝕜 A A) (w v : Fin 3 → A) :
    (∑ i, ∑ j, w i*twiceStrain D v i j*w j)=2*linearContraction D w v := by
  norm_num [twiceStrain,linearContraction,gradient,dotProduct,Fin.sum_univ_succ] <;> ring

theorem divergence_product_component (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A) (j : Fin 3) :
    divergence D (fun i => w i*w j)=divergence D w*w j+advection D w w j := by
  norm_num [divergence,advection,jacobian,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,Derivation.leibniz,smul_eq_mul] <;> ring

theorem trace_linearContraction (D : Fin 3 → Derivation 𝕜 A A) (T : A →ₗ[𝕜] 𝕜)
    (hT : ∀ i f, T (D i f)=0) (w v : Fin 3 → A) (hw : divergence D w=0) :
    T (linearContraction D w v)=-T (dotProduct (advection D w w) v) := by
  unfold linearContraction
  rw [map_sum]
  have hj (j : Fin 3) : T (dotProduct (gradient D (v j)) (fun i => w i*w j))=
      -T (v j*advection D w w j) := by
    rw [gradient_pairing D T hT,divergence_product_component,hw,zero_mul,zero_add]
  simp_rw [hj]
  simp only [dotProduct,map_sum,Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem twice_miller_zero (D : Fin 3 → Derivation 𝕜 A A) (T : A →ₗ[𝕜] 𝕜)
    (hcomm : ∀ i j f, D i (D j f)=D j (D i f))
    (hT : ∀ i f, T (D i f)=0) (u : Fin 3 → A) (hu : divergence D u=0) :
    T (∑ i, ∑ j, curl D u i*lap D (twiceStrain D u i j)*curl D u j)=0 := by
  simp_rw [lap_twiceStrain D hcomm]
  rw [symmetric_contraction,two_mul,map_add]
  have h : T (linearContraction D (curl D u) (vectorLap D u))=0 := by
    rw [trace_linearContraction D T hT _ _ (divergence_curl D hcomm u),
      lap_eq_neg_curl_curl D hcomm u hu,dotProduct_neg,map_neg,neg_neg]
    exact helicity_zero D T hcomm hT (curl D u)
  rw [h,zero_add]

theorem miller_zero (D : Fin 3 → Derivation 𝕜 A A) (T : A →ₗ[𝕜] 𝕜)
    (hcomm : ∀ i j f, D i (D j f)=D j (D i f))
    (hT : ∀ i f, T (D i f)=0) (u : Fin 3 → A) (hu : divergence D u=0) :
    T (∑ i, ∑ j, curl D u i*lap D (strain D u i j)*curl D u j)=0 := by
  have he : (∑ i, ∑ j, curl D u i*lap D (strain D u i j)*curl D u j)=
      (1/2 : 𝕜) • (∑ i, ∑ j, curl D u i*lap D (twiceStrain D u i j)*curl D u j) := by
    simp only [strain]
    simp only [lap_smul]
    norm_num [Algebra.smul_def,Fin.sum_univ_succ] <;> ring
  rw [he,map_smul,twice_miller_zero D T hcomm hT u hu,smul_zero]

def crossContraction (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A)
    (M : Matrix (Fin 3) (Fin 3) A) : A := ∑ k, ∑ i, ∑ j, D k (w i)*D k (M i j)*w j
def lapContraction (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A)
    (M : Matrix (Fin 3) (Fin 3) A) : A := ∑ i, ∑ j, w i*lap D (M i j)*w j
def flux (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A)
    (M : Matrix (Fin 3) (Fin 3) A) : Fin 3 → A := fun k => ∑ i, ∑ j, w i*D k (M i j)*w j

theorem divergence_flux (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A)
    (M : Matrix (Fin 3) (Fin 3) A) (hM : ∀ i j, M i j=M j i) :
    divergence D (flux D w M)=2*crossContraction D w M+lapContraction D w M := by
  norm_num [divergence,flux,crossContraction,lapContraction,lap,Fin.sum_univ_succ,
    Derivation.leibniz,smul_eq_mul]
  simp only [hM 1 0,hM 2 0,hM 2 1]
  ring

theorem strain_symmetric (D : Fin 3 → Derivation 𝕜 A A) (u : Fin 3 → A) (i j : Fin 3) :
    strain D u i j=strain D u j i := by
  simp only [strain,twiceStrain]
  rw [add_comm]

theorem cross_zero (D : Fin 3 → Derivation 𝕜 A A) (T : A →ₗ[𝕜] 𝕜)
    (hcomm : ∀ i j f, D i (D j f)=D j (D i f))
    (hT : ∀ i f, T (D i f)=0) (u : Fin 3 → A) (hu : divergence D u=0) :
    T (crossContraction D (curl D u) (strain D u))=0 := by
  have hf : T (divergence D (flux D (curl D u) (strain D u)))=0 := by
    simp only [divergence,map_sum]
    exact Finset.sum_eq_zero (fun k _ => hT k _)
  rw [divergence_flux D _ _ (strain_symmetric D u),map_add] at hf
  have hm : T (lapContraction D (curl D u) (strain D u))=0 := miller_zero D T hcomm hT u hu
  rw [hm,add_zero,two_mul,map_add] at hf
  have hz : (2 : 𝕜)*T (crossContraction D (curl D u) (strain D u))=0 := by
    rw [two_mul]
    exact hf
  exact (mul_eq_zero.mp hz).resolve_left two_ne_zero

end OperatorDerivativeRewrite.Foundation.DifferentialTraceViscousCancellation
