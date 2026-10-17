import Foundation.HigherHeatFourierInnovations

/-! Signed covariance of Fourier innovations and its exact product correction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierCovariance
open HigherHeatL2 HigherHeatCylinderFourier HigherHeatBackwardFourier
open HigherHeatFourierInnovations HigherHeatSignedLaws

theorem phase_frequency_add (ξ η z : ℝ) : phase (ξ+η) z=phase ξ z*phase η z := by
  simp only [phase,mul_add,neg_add_rev,AddChar.map_add_eq_mul,Circle.coe_mul]
  ring

def covariance (m : ℕ) (t : ℝ≥0) (ξ η : ℝ) : ℂ :=
  symbol m t (ξ+η)-symbol m t ξ*symbol m t η

theorem product_expand (m : ℕ) (t : ℝ≥0) (ξ η z : ℝ) :
    innovation m t ξ z*innovation m t η z=
      phase (ξ+η) z-symbol m t η*phase ξ z-symbol m t ξ*phase η z+
        symbol m t ξ*symbol m t η := by
  rw [phase_frequency_add]
  unfold innovation
  ring

theorem kernel_product_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (ξ η : ℝ) :
    Integrable (fun z => (innovation m t ξ z*innovation m t η z)*
      (realKernel m hm t ht z:ℂ)) := by
  have h1 := kernel_phase_integrable m hm t ht (ξ+η)
  have h2 := (kernel_phase_integrable m hm t ht ξ).const_mul (symbol m t η)
  have h3 := (kernel_phase_integrable m hm t ht η).const_mul (symbol m t ξ)
  have h4 := ((realKernel m hm t ht).integrable (μ := volume)).ofReal.const_mul
    (symbol m t ξ*symbol m t η)
  apply (((h1.sub h2).sub h3).add h4).congr
  exact Filter.Eventually.of_forall fun z => by
    change phase (ξ+η) z*(realKernel m hm t ht z:ℂ)-
      symbol m t η*(phase ξ z*(realKernel m hm t ht z:ℂ))-
      symbol m t ξ*(phase η z*(realKernel m hm t ht z:ℂ))+
      (symbol m t ξ*symbol m t η)*(realKernel m hm t ht z:ℂ)=
      (innovation m t ξ z*innovation m t η z)*(realKernel m hm t ht z:ℂ)
    rw [product_expand]
    ring

theorem kernel_product (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ η : ℝ) :
    (∫ z : ℝ, (innovation m t ξ z*innovation m t η z)*(realKernel m hm t ht z:ℂ))=
      covariance m t ξ η := by
  let K := realKernel m hm t ht
  have h1 := kernel_phase_integrable m hm t ht (ξ+η)
  have h2 := (kernel_phase_integrable m hm t ht ξ).const_mul (symbol m t η)
  have h3 := (kernel_phase_integrable m hm t ht η).const_mul (symbol m t ξ)
  have h4 := (K.integrable (μ := volume)).ofReal.const_mul (symbol m t ξ*symbol m t η)
  calc
    _ = ∫ z : ℝ, phase (ξ+η) z*(K z:ℂ)-symbol m t η*(phase ξ z*(K z:ℂ))-
        symbol m t ξ*(phase η z*(K z:ℂ))+(symbol m t ξ*symbol m t η)*(K z:ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [product_expand]
        ring
    _ = (∫ z : ℝ, phase (ξ+η) z*(K z:ℂ)-symbol m t η*(phase ξ z*(K z:ℂ))-
        symbol m t ξ*(phase η z*(K z:ℂ)))+
        (∫ z : ℝ, (symbol m t ξ*symbol m t η)*(K z:ℂ)) :=
      integral_add ((h1.sub h2).sub h3) h4
    _ = ((∫ z : ℝ, phase (ξ+η) z*(K z:ℂ)-symbol m t η*(phase ξ z*(K z:ℂ)))-
        (∫ z : ℝ, symbol m t ξ*(phase η z*(K z:ℂ))))+
        (∫ z : ℝ, (symbol m t ξ*symbol m t η)*(K z:ℂ)) := by
      exact congrArg (fun u : ℂ => u+∫ z : ℝ, (symbol m t ξ*symbol m t η)*(K z:ℂ))
        (integral_sub (h1.sub h2) h3)
    _ = (((∫ z : ℝ, phase (ξ+η) z*(K z:ℂ))-
        (∫ z : ℝ, symbol m t η*(phase ξ z*(K z:ℂ))))-
        (∫ z : ℝ, symbol m t ξ*(phase η z*(K z:ℂ))))+
        (∫ z : ℝ, (symbol m t ξ*symbol m t η)*(K z:ℂ)) := by
      exact congrArg (fun u : ℂ => (u-(∫ z : ℝ, symbol m t ξ*(phase η z*(K z:ℂ))))+
        (∫ z : ℝ, (symbol m t ξ*symbol m t η)*(K z:ℂ))) (integral_sub h1 h2)
    _ = _ := by
      dsimp only [K]
      simp only [integral_const_mul,kernel_fourier,integral_complex_ofReal,realKernel_integral,covariance]
      norm_num only [Complex.ofReal_one]
      ring

theorem product_decomposition (m : ℕ) (t : ℝ≥0) (ξ η z : ℝ) :
    innovation m t ξ z*innovation m t η z-covariance m t ξ η=
      innovation m t (ξ+η) z-symbol m t η*innovation m t ξ z-
        symbol m t ξ*innovation m t η z := by
  rw [product_expand]
  unfold innovation covariance
  ring

theorem centered_product_zero (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ η : ℝ) :
    (∫ z : ℝ, (innovation m t ξ z*innovation m t η z-covariance m t ξ η)*
      (realKernel m hm t ht z:ℂ))=0 := by
  have h1 := kernel_product_integrable m hm t ht ξ η
  have h2 := ((realKernel m hm t ht).integrable (μ := volume)).ofReal.const_mul
    (covariance m t ξ η)
  calc
    _ = ∫ z : ℝ, (innovation m t ξ z*innovation m t η z)*(realKernel m hm t ht z:ℂ)-
        covariance m t ξ η*(realKernel m hm t ht z:ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => sub_mul _ _ _
    _ = (∫ z : ℝ, (innovation m t ξ z*innovation m t η z)*(realKernel m hm t ht z:ℂ))-
        (∫ z : ℝ, covariance m t ξ η*(realKernel m hm t ht z:ℂ)) := integral_sub h1 h2
    _ = 0 := by
      rw [kernel_product,integral_const_mul,integral_complex_ofReal,realKernel_integral]
      simp

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierCovariance
