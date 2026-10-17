import Foundation.FiniteFourierReality

/-! Real coordinate derivatives and actual real periodic averages of finite
Fourier synthesis, with Hermitian stability of curl, strain and Laplacian. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RealFiniteFourierAnalysis
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
  FiniteFourierReality
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def realSynthesis (f : Fourier) (x : Space) : ℝ := (synthesis x f).re
def realPartial (j : Fin 3) (f : Space → ℝ) (x : Space) : ℝ :=
  deriv (fun r => f (Function.update x j r)) (x j)

theorem realSynthesis_derivative (f : Fourier) (x : Space) (j : Fin 3) :
    HasDerivAt (fun r => realSynthesis f (Function.update x j r))
      (realSynthesis (derivative j f) x) (x j) := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (x j) (synthesis_coordinate_derivative f x j)
  simpa [realSynthesis,Function.comp_def] using h

theorem realPartial_synthesis (f : Fourier) (x : Space) (j : Fin 3) :
    realPartial j (realSynthesis f) x=realSynthesis (derivative j f) x :=
  (realSynthesis_derivative f x j).deriv

theorem realPartial_synthesis_function (j : Fin 3) (f : Fourier) :
    realPartial j (realSynthesis f)=realSynthesis (derivative j f) :=
  funext (fun x => realPartial_synthesis f x j)

def realCircleAverage (j : Fin 3) (F : Space → ℝ) (x : Space) : ℝ :=
  (2*Real.pi)⁻¹*(∫ r in (0 : ℝ)..2*Real.pi, F (Function.update x j r))
def realBoxAverage (F : Space → ℝ) : ℝ :=
  realCircleAverage 2 (realCircleAverage 1 (realCircleAverage 0 F)) 0

theorem normalized_re (z : ℂ) :
    (period⁻¹*z).re=(2*Real.pi)⁻¹*z.re := by
  have hp : period⁻¹=(((2*Real.pi)⁻¹ : ℝ) : ℂ) := by simp [period]
  rw [hp]
  simp [Complex.mul_re]

theorem realCircleAverage_synthesis (j : Fin 3) (f : Fourier) (x : Space) :
    realCircleAverage j (realSynthesis f) x=realSynthesis (cut j f) x := by
  have hi : (∫ r in (0 : ℝ)..2*Real.pi, (synthesis (Function.update x j r) f).re)=
      (∫ r in (0 : ℝ)..2*Real.pi, synthesis (Function.update x j r) f).re := by
    exact Complex.reCLM.intervalIntegral_comp_comm (coordinate_integrable f x j)
  have h := congrArg Complex.re (circleAverage_synthesis j x f)
  change (period⁻¹*(∫ r in (0 : ℝ)..2*Real.pi, synthesis (Function.update x j r) f)).re=_ at h
  rw [normalized_re] at h
  unfold realCircleAverage realSynthesis
  rw [hi]
  exact h

theorem realCircleAverage_synthesis_function (j : Fin 3) (f : Fourier) :
    realCircleAverage j (realSynthesis f)=realSynthesis (cut j f) :=
  funext (fun x => realCircleAverage_synthesis j f x)

theorem realBoxAverage_synthesis (f : Fourier) :
    realBoxAverage (realSynthesis f)=(constantTrace f).re := by
  rw [realBoxAverage,realCircleAverage_synthesis_function,realCircleAverage_synthesis_function,
    realCircleAverage_synthesis_function,cut_all]
  change (synthesis (0 : Space) (AddMonoidAlgebra.single 0 (f.coeff 0))).re=(constantTrace f).re
  rw [synthesis_single,character_zero,mul_one,constantTrace_apply]

theorem hermitian_curl (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i)) (i : Fin 3) :
    Hermitian (curl derivative u i) := by
  fin_cases i
  · exact hermitian_sub _ _ (hermitian_derivative _ (hu 2) 1) (hermitian_derivative _ (hu 1) 2)
  · exact hermitian_sub _ _ (hermitian_derivative _ (hu 0) 2) (hermitian_derivative _ (hu 2) 0)
  · exact hermitian_sub _ _ (hermitian_derivative _ (hu 1) 0) (hermitian_derivative _ (hu 0) 1)

theorem hermitian_strain (u : Fin 3 → Fourier) (hu : ∀ i, Hermitian (u i)) (i j : Fin 3) :
    Hermitian (strain derivative u i j) := by
  have h := hermitian_real_smul (1/2 : ℝ) _
    (hermitian_add _ _ (hermitian_derivative _ (hu i) j) (hermitian_derivative _ (hu j) i))
  simpa [strain,twiceStrain] using h

theorem hermitian_laplacian (f : Fourier) (hf : Hermitian f) : Hermitian (lap derivative f) := by
  apply hermitian_sum Finset.univ
  intro k _
  exact hermitian_derivative _ (hermitian_derivative f hf k) k

theorem realSynthesis_sum {ι : Type*} (s : Finset ι) (f : ι → Fourier) (x : Space) :
    realSynthesis (∑ i ∈ s, f i) x=∑ i ∈ s, realSynthesis (f i) x := by
  simp [realSynthesis,map_sum]

theorem realSynthesis_product (f g h : Fourier) (hf : Hermitian f) (hg : Hermitian g)
    (hh : Hermitian h) (x : Space) :
    realSynthesis f x*realSynthesis g x*realSynthesis h x=realSynthesis (f*g*h) x := by
  simp [realSynthesis,synthesis_mul,Complex.mul_re,Complex.mul_im,
    synthesis_im_zero f hf x,synthesis_im_zero g hg x,synthesis_im_zero h hh x]

end OperatorDerivativeRewrite.Foundation.RealFiniteFourierAnalysis
