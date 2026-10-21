import Foundation.RiemannQuadraticGlobalStrip
import Foundation.RiemannQuadraticXiTransfer

noncomputable section
open Polynomial Complex Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticStripEvolution
open RiemannEvenFlow PureOrderPolynomialTransport

theorem strip_from_time (t b : ℝ)
    (hstrip : ∀ z : ℂ,flow 1 t z=0 → |z.im|≤b)
    (s : ℝ≥0) (z : ℂ) (hz : flow 1 (t+(s:ℝ)) z=0) :
    z.im^2≤max (b^2-2*(s:ℝ)) 0 := by
  obtain ⟨r,P,hr,hrb,hzeros,h0,heven,hlim,hbudget⟩ :=
    EvenEntireGaussianBudget.exists_real_polynomials_with_gaussian_budget
      (flow 1 t) (RiemannQuadraticDivisor.flow_analytic t)
      (RiemannQuadraticDivisor.flow_origin_ne_zero t) (RiemannEvenEvolution.flow_even 1 t)
      (RiemannEvenEntireGrowth.exists_subquadratic_growth 1 t)
      (RiemannEvenWindowZeros.flow_conj 1 t) b hstrip
  have hPn (n : ℕ) : P n≠0 := by
    intro hzero
    have he := h0 n
    rw [hzero,Polynomial.map_zero,eval_zero] at he
    exact (RiemannQuadraticDivisor.flow_origin_ne_zero t) he.symm
  have hinit (n : ℕ) (a : ℂ) (ha : ((P n).map (algebraMap ℝ ℂ)).eval a=0) : a.im^2≤b^2 := by
    have hb := hstrip a ((hzeros n a).mp ha).2
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a.im) ((abs_nonneg a.im).trans hb)).mpr hb
  let Q : ℕ → ℂ[X] := fun n => (transport 2 (-(s:ℝ)) (P n)).map (algebraMap ℝ ℂ)
  have hpoint (w : ℂ) : Tendsto (fun n => (Q n).eval w) atTop (𝓝 (flow 1 (t+(s:ℝ)) w)) := by
    let : IsGaussian (RiemannQuadraticGaussian.law s) := by
      change IsGaussian (gaussianReal 0 (2*s))
      infer_instance
    obtain ⟨hIP,hIf,hIlim⟩ := EvenEntireGaussianBudget.gaussian_integral_limit
      (RiemannQuadraticGaussian.law s)
      (fun n w => ((P n).map (algebraMap ℝ ℂ)).eval w) (flow 1 t)
      (fun n => ((P n).map (algebraMap ℝ ℂ)).differentiable.continuous)
      (flow_differentiable 1 t).continuous hlim hbudget w I
    simp_rw [ComplexGaussianPolynomialTransport.imaginary_gaussian_transport] at hIlim
    rw [RiemannQuadraticGaussian.imaginary_gaussian_average] at hIlim
    exact hIlim
  let B : ℝ := max (b^2-2*(s:ℝ)) 0
  have hB : 0≤B := le_max_right _ _
  have hQ (n : ℕ) (a : ℂ) (ha : (Q n).eval a=0) : a.im^2≤B :=
    PolynomialStripLimit.quadratic_heat_strip (P n) (hPn n) (s:ℝ) b s.property (hinit n) a ha
  have he := PolynomialStripLimit.strip_zero_limit Q (flow 1 (t+(s:ℝ))) (Real.sqrt B)
    (flow_differentiable 1 (t+(s:ℝ))) ⟨0,RiemannQuadraticDivisor.flow_origin_ne_zero _⟩
    (fun n a ha => Real.abs_le_sqrt (hQ n a ha)) hpoint z hz
  have hsq := (sq_le_sq₀ (abs_nonneg z.im) (Real.sqrt_nonneg B)).mpr he
  simpa only [sq_abs,Real.sq_sqrt hB] using hsq

theorem strip_between_times (t u b : ℝ) (htu : t≤u)
    (hstrip : ∀ z : ℂ,flow 1 t z=0 → |z.im|≤b)
    (z : ℂ) (hz : flow 1 u z=0) : z.im^2≤max (b^2-2*(u-t)) 0 := by
  let s : ℝ≥0 := ⟨u-t,sub_nonneg.mpr htu⟩
  have htime : t+(s:ℝ)=u := by change t + (u-t) = u; ring
  have hz' : flow 1 (t+(s:ℝ)) z=0 := by rw [htime]; exact hz
  exact strip_from_time t b hstrip s z hz'

theorem real_after_strip_wait (t u b : ℝ)
    (hstrip : ∀ z : ℂ,flow 1 t z=0 → |z.im|≤b)
    (htu : t+b^2/2≤u) (z : ℂ) (hz : flow 1 u z=0) : z.im=0 := by
  have htu' : t≤u := by nlinarith [sq_nonneg b]
  have he := strip_between_times t u b htu' hstrip z hz
  rw [max_eq_right (by linarith : b^2-2*(u-t)≤0)] at he
  nlinarith [sq_nonneg z.im]

theorem once_real_always_real (t u : ℝ) (htu : t≤u)
    (hreal : ∀ z : ℂ,flow 1 t z=0 → z.im=0) (z : ℂ) (hz : flow 1 u z=0) : z.im=0 := by
  have he := strip_between_times t u 0 htu (fun w hw => by simp [hreal w hw]) z hz
  rw [max_eq_right (by nlinarith : (0:ℝ)^2-2*(u-t)≤0)] at he
  nlinarith [sq_nonneg z.im]

theorem conditional_seven_eighths_strip
    (hfree : ∀ w : ℂ,(7/8:ℝ)<w.re → riemannZeta w≠0)
    (t : ℝ) (ht : 0≤t) (z : ℂ) (hz : flow 1 t z=0) :
    z.im^2≤max ((9/16:ℝ)-2*t) 0 := by
  have hband (w : ℂ) (hw : flow 1 0 w=0) : |w.im|≤(3/4:ℝ) := by
    apply RiemannQuadraticXiTransfer.zero_im_strip_of_seven_eighths hfree 1 (by norm_num) w
    have he : RiemannRealOrderFlow.flow 1 0 w=flow 1 0 w := by
      simpa only [Nat.cast_one] using RiemannRealOrderFlow.flow_nat 1 0 w
    rw [he]
    exact hw
  have he := strip_between_times 0 t (3/4) ht hband z hz
  convert he using 1
  congr 1 <;> ring

theorem conditional_seven_eighths_real_zeros
    (hfree : ∀ w : ℂ,(7/8:ℝ)<w.re → riemannZeta w≠0)
    (t : ℝ) (ht : 9/32≤t) (z : ℂ) (hz : flow 1 t z=0) : z.im=0 := by
  have he := conditional_seven_eighths_strip hfree t (by linarith) z hz
  rw [max_eq_right (by linarith : (9/16:ℝ)-2*t≤0)] at he
  nlinarith [sq_nonneg z.im]

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticStripEvolution

