import Foundation.RealBeltramiMeans

/-! The remaining strain/derivative viscous trace, from a transport flux. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.BeltramiViscousTrace
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
  FiniteFourierReality RealFiniteFourierAnalysis RealPeriodicViscousCancellation
  ABCFourierProfile BeltramiAdvection RealBeltramiEuler ABCNavierStokesFlow ABCTraceMeans
  RealBeltramiMeans
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

variable {𝕜 A : Type*} [Field 𝕜] [CharZero 𝕜] [CommRing A] [Algebra 𝕜 A]

def viscousContraction (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A)
    (M : Matrix (Fin 3) (Fin 3) A) : A := ∑ k, ∑ i, ∑ j, M i j*D k (w i)*D k (w j)

def transportFlux (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A)
    (M : Matrix (Fin 3) (Fin 3) A) : Fin 3 → A := fun k =>
  ∑ i, ∑ j, w i*M i j*D k (w j)

theorem divergence_transport (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A)
    (M : Matrix (Fin 3) (Fin 3) A) (hM : ∀ i j, M i j=M j i) :
    divergence D (transportFlux D w M)=
      crossContraction D w M+viscousContraction D w M+
        ∑ i, ∑ j, w i*M i j*lap D (w j) := by
  norm_num [divergence,transportFlux,crossContraction,viscousContraction,lap,
    Fin.sum_univ_succ,Derivation.leibniz,smul_eq_mul]
  simp only [hM 1 0,hM 2 0,hM 2 1]
  ring

theorem beltrami_viscous_zero (D : Fin 3 → Derivation 𝕜 A A) (T : A →ₗ[𝕜] 𝕜)
    (hcomm : ∀ i j f, D i (D j f)=D j (D i f)) (hT : ∀ i f, T (D i f)=0)
    (u : Fin 3 → A) (hu : curl D u=u) (hd : divergence D u=0)
    (hl : ∀ i, lap D (u i)= -u i) :
    T (viscousContraction D u (strain D u))=0 := by
  have hf : T (divergence D (transportFlux D u (strain D u)))=0 := by
    simp only [divergence,map_sum]
    exact Finset.sum_eq_zero (fun k _ => hT k _)
  have hc : T (crossContraction D u (strain D u))=0 := by
    have h := cross_zero D T hcomm hT u hd
    simpa only [hu] using h
  have he : (∑ i, ∑ j, u i*strain D u i j*lap D (u j))=
      -dotProduct (Matrix.mulVec (strain D u) u) u := by
    simp only [hl]
    norm_num [dotProduct,Matrix.mulVec,Fin.sum_univ_succ]
    ring
  rw [divergence_transport D u _ (strain_symmetric D u),map_add,map_add,he,map_neg,
    hc,beltrami_stretching_trace D T hT u hu hd] at hf
  simpa using hf

def realViscous (F : RealField) (x : Space) : ℝ :=
  ∑ k, ∑ i, ∑ j, realStrain F x i j*
    realPartial k (fun y => realCurl F y i) x*
    realPartial k (fun y => realCurl F y j) x

theorem realViscous_synthesis (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i))
    (x : Space) : realViscous (realizeReal u) x=
      realSynthesis (viscousContraction derivative (curl derivative u) (strain derivative u)) x := by
  simp only [realViscous,realStrain_realize,realCurl_function,realPartial_synthesis,
    viscousContraction,realSynthesis_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact realSynthesis_product _ _ _ (hermitian_strain u hu i j)
    (hermitian_derivative _ (hermitian_curl u hu i) k)
    (hermitian_derivative _ (hermitian_curl u hu j) k) x

theorem abc_viscous_mean : realBoxAverage (realViscous (realizeReal abc))=0 := by
  have he : realViscous (realizeReal abc)=realSynthesis
      (viscousContraction derivative (curl derivative abc) (strain derivative abc)) :=
    funext (realViscous_synthesis abc abc_hermitian)
  rw [he,realBoxAverage_synthesis,abc_curl,
    beltrami_viscous_zero derivative constantTrace derivative_commute
      constantTrace_derivative abc abc_curl abc_divergence abc_laplacian]
  rfl

end OperatorDerivativeRewrite.Foundation.BeltramiViscousTrace
