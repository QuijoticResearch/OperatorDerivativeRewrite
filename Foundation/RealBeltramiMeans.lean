import Foundation.ABCTraceMeans

/-! Real periodic stretching, amplification and pressure-Hessian means.
All spatial derivatives and averages are the previously realized operators. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RealBeltramiMeans
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
  FiniteFourierReality RealFiniteFourierAnalysis RealPeriodicViscousCancellation
  ABCFourierProfile BeltramiAdvection RealBeltramiEuler ABCNavierStokesFlow ABCTraceMeans
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def realStrainAction (F : RealField) (x : Space) (i : Fin 3) : ℝ :=
  ∑ j, realStrain F x i j*realCurl F x j

def realStretching (F : RealField) (x : Space) : ℝ :=
  dotProduct (realStrainAction F x) (realCurl F x)

def realAmplification (F : RealField) (x : Space) : ℝ :=
  dotProduct (realStrainAction F x) (realStrainAction F x)

def realPressureContraction (F : RealField) (p : Space → ℝ) (x : Space) : ℝ :=
  ∑ j, ∑ i, realPartial i (realPartial j p) x*realCurl F x i*realCurl F x j

def strainAction (u : Fin 3 → Fourier) : Fin 3 → Fourier :=
  Matrix.mulVec (strain derivative u) (curl derivative u)

theorem kinetic_hermitian (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i)) :
    Hermitian (kinetic (𝕜 := ℂ) u) := by
  have he : Hermitian (energy u) := by
    apply hermitian_sum Finset.univ
    intro i _
    simpa only [pow_two] using hermitian_mul (u i) (u i) (hu i) (hu i)
  have h := hermitian_real_smul (1/2 : ℝ) (energy u) he
  simpa [kinetic] using h

theorem strainAction_hermitian (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i))
    (i : Fin 3) : Hermitian (strainAction u i) := by
  apply hermitian_sum Finset.univ
  intro j _
  exact hermitian_mul _ _ (hermitian_strain u hu i j) (hermitian_curl u hu j)

theorem realStrainAction_synthesis (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i))
    (x : Space) (i : Fin 3) :
    realStrainAction (realizeReal u) x i=realSynthesis (strainAction u i) x := by
  simp only [realStrainAction,realStrain_realize,realCurl_realize,strainAction,
    Matrix.mulVec,dotProduct,realSynthesis_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (realSynthesis_mul _ _ (hermitian_strain u hu i j) (hermitian_curl u hu j) x).symm

theorem realStretching_synthesis (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i))
    (x : Space) : realStretching (realizeReal u) x=
      realSynthesis (dotProduct (strainAction u) (curl derivative u)) x := by
  simp only [realStretching,dotProduct,realStrainAction_synthesis u hu,realCurl_realize,
    realSynthesis_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (realSynthesis_mul _ _ (strainAction_hermitian u hu i) (hermitian_curl u hu i) x).symm

theorem realAmplification_synthesis (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i))
    (x : Space) : realAmplification (realizeReal u) x=
      realSynthesis (dotProduct (strainAction u) (strainAction u)) x := by
  simp only [realAmplification,dotProduct,realStrainAction_synthesis u hu,realSynthesis_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (realSynthesis_mul _ _ (strainAction_hermitian u hu i)
    (strainAction_hermitian u hu i) x).symm

theorem realPressure_synthesis (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i))
    (p : Fourier) (hp : Hermitian p) (x : Space) :
    realPressureContraction (realizeReal u) (realSynthesis p) x=
      realSynthesis (linearContraction derivative (curl derivative u) (gradient derivative p)) x := by
  simp only [realPressureContraction,realPartial_synthesis_function,realPartial_synthesis,
    realCurl_realize,linearContraction,gradient,dotProduct,realSynthesis_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have h := realSynthesis_product _ _ _
    (hermitian_derivative _ (hermitian_derivative p hp j) i)
    (hermitian_curl u hu i) (hermitian_curl u hu j) x
  simpa only [mul_assoc] using h

theorem beltrami_stretching_mean (u : Fin 3 → Fourier) (hH : ∀ i, Hermitian (u i))
    (hu : curl derivative u=u) (hd : divergence derivative u=0) :
    realBoxAverage (realStretching (realizeReal u))=0 := by
  have he : realStretching (realizeReal u)=
      realSynthesis (dotProduct (strainAction u) (curl derivative u)) :=
    funext (realStretching_synthesis u hH)
  rw [he,realBoxAverage_synthesis]
  simp only [strainAction,hu]
  rw [beltrami_stretching_trace derivative constantTrace constantTrace_derivative u hu hd]
  rfl

theorem abc_amplification_mean : realBoxAverage (realAmplification (realizeReal abc))=3/2 := by
  have he : realAmplification (realizeReal abc)=
      realSynthesis (dotProduct (strainAction abc) (strainAction abc)) :=
    funext (realAmplification_synthesis abc abc_hermitian)
  rw [he,realBoxAverage_synthesis]
  simp only [strainAction,abc_curl]
  rw [abc_amplification_trace]
  norm_num

theorem abc_pressure_mean : realBoxAverage (realPressureContraction (realizeReal abc)
    (realSynthesis (-kinetic (𝕜 := ℂ) abc)))=3/2 := by
  have hp : Hermitian (-kinetic (𝕜 := ℂ) abc) := by
    simpa using hermitian_sub 0 _ hermitian_zero (kinetic_hermitian abc abc_hermitian)
  have he : realPressureContraction (realizeReal abc) (realSynthesis (-kinetic (𝕜 := ℂ) abc))=
      realSynthesis (linearContraction derivative (curl derivative abc)
        (gradient derivative (-kinetic (𝕜 := ℂ) abc))) :=
    funext (realPressure_synthesis abc abc_hermitian _ hp)
  rw [he,realBoxAverage_synthesis,abc_curl,abc_pressure_trace]
  norm_num

theorem flow_stretching_mean (nu t : ℝ) : realBoxAverage (realStretching (velocity nu t))=0 :=
  beltrami_stretching_mean (state nu t) (state_hermitian nu t) (state_curl nu t)
    (transverse_divergence_zero (state nu t) (state_transverse nu t))

theorem flow_stretching_mean_derivative (nu t : ℝ) :
    deriv (fun s => realBoxAverage (realStretching (velocity nu s))) t=0 := by
  have he : (fun s => realBoxAverage (realStretching (velocity nu s)))=(fun _ : ℝ => 0) :=
    funext (flow_stretching_mean nu)
  rw [he]
  simp

end OperatorDerivativeRewrite.Foundation.RealBeltramiMeans
