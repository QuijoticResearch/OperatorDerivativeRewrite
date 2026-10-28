import Foundation.SU2SevenLinkVariational

/-! The three actual Haar channels used in an inverse-half-weight odd trial.
No normalized spatial eigenbranch is postulated. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkOddTrial
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open SU2SharedPlaquetteProjection SU2SevenLinkTransfer SU2SevenLinkVariational

private theorem bounded_product (f g : State → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hb : ∀ s, |f s| ≤ B) (hc : ∀ s, |g s| ≤ C) :
    Integrable (fun s => f s*g s) haar := by
  apply Integrable.of_bound (hf.mul hg).aestronglyMeasurable (|B| * |C|)
  filter_upwards with s
  change ‖f s*g s‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul ((hb s).trans (le_abs_self B)) ((hc s).trans (le_abs_self C)) (abs_nonneg _) (abs_nonneg _)

private theorem trace_right_mean (U : SU2) : (∫ L, halfTrace (L*U) ∂law)=0 := by
  have he (L : SU2) : halfTrace (L*U)=halfTrace (U*L) := halfTrace_mul_comm L U
  simp_rw [he]
  rw [integral_mul_left_eq_self]
  exact (SU2TiltEnergyResponse.moment_values law).1

theorem haar_second_square : (∫ s, second s^2 ∂haar)=(1/4:ℝ) := by
  have hb (L R U : SU2) : |halfTrace (U⁻¹*R)^2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (halfTrace_bound (U⁻¹*R)) 2
  change (∫ s, halfTrace (s.1⁻¹*rightPath s)^2 ∂haar)=_
  rw [haar_path_integral (fun L R U => halfTrace (U⁻¹*R)^2)
    (second_measurable.pow_const 2) 1 hb]
  simp_rw [trace_square_mean]
  simp

theorem haar_second_meanChannel : (∫ s, second s*meanChannel s ∂haar)=0 := by
  have hb (L R U : SU2) : |halfTrace (U⁻¹*R)*sharedMean L R| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (halfTrace_bound _) (sharedMean_bound L R) (abs_nonneg _) (by norm_num)
  change (∫ s, halfTrace (s.1⁻¹*rightPath s)*sharedMean (leftPath s) (rightPath s) ∂haar)=0
  rw [haar_path_integral (fun L R U => halfTrace (U⁻¹*R)*sharedMean L R)
    (second_measurable.mul meanChannel_measurable) 1 hb]
  have hp (L U : SU2) : (∫ R, halfTrace (U⁻¹*R)*sharedMean L R ∂law)=halfTrace (L*U)/16 := by
    have he (R : SU2) : halfTrace (U⁻¹*R)*sharedMean L R=(halfTrace (U⁻¹*R)*halfTrace (L*R))/4 := by
      unfold sharedMean
      ring
    simp_rw [he]
    rw [integral_div,translated_pair_covariance]
    have hh : halfTrace (U⁻¹*L⁻¹)=halfTrace (L*U) := by rw [← mul_inv_rev,halfTrace_inv]
    rw [hh]
    ring
  simp_rw [hp,integral_div,trace_right_mean]
  simp

theorem haar_first_second_square : (∫ s, first s*second s^2 ∂haar)=0 := by
  have hb (L R U : SU2) : |halfTrace (L*U)*halfTrace (U⁻¹*R)^2| ≤ 1 := by
    rw [abs_mul,abs_pow]
    exact (mul_le_mul (halfTrace_bound _) (pow_le_pow_left₀ (abs_nonneg _) (halfTrace_bound _) 2)
      (sq_nonneg _) (by norm_num)).trans (by norm_num)
  change (∫ s, halfTrace (leftPath s*s.1)*halfTrace (s.1⁻¹*rightPath s)^2 ∂haar)=0
  rw [haar_path_integral (fun L R U => halfTrace (L*U)*halfTrace (U⁻¹*R)^2)
    (first_measurable.mul (second_measurable.pow_const 2)) 1 hb]
  simp_rw [integral_const_mul,trace_square_mean,integral_mul_const,trace_right_mean]
  simp

theorem haar_second_residual : (∫ s, second s*residual s ∂haar)=0 := by
  have h1 := bounded_product first (fun s => second s^2) first_measurable (second_measurable.pow_const 2)
    1 1 first_bound (fun s => by rw [abs_pow]; simpa using pow_le_pow_left₀ (abs_nonneg _) (second_bound s) 2)
  have h2 := bounded_product second meanChannel second_measurable meanChannel_measurable 1 1 second_bound meanChannel_bound
  have he (s : State) : second s*residual s=first s*second s^2-second s*meanChannel s := by
    unfold SU2SevenLinkTransfer.residual sharedResidual sharedProduct first second meanChannel
    ring
  simp_rw [he]
  have hsub := integral_sub h1 h2
  rw [hsub,haar_first_second_square,haar_second_meanChannel]
  norm_num

/-- The three concrete channels, not abstract vectors with assumed moments. -/
def basis (i : Fin 3) (s : State) : ℝ := ![second s,meanChannel s,residual s] i

def mass (i : Fin 3) : ℝ := ![(1/4:ℝ),1/64,3/64] i

theorem basis_measurable (i : Fin 3) : Measurable (basis i) := by
  fin_cases i
  · exact second_measurable
  · exact meanChannel_measurable
  · exact residual_measurable

theorem basis_bound (i : Fin 3) (s : State) : |basis i s| ≤ 2 := by
  fin_cases i
  · exact (second_bound s).trans (by norm_num)
  · exact (meanChannel_bound s).trans (by norm_num)
  · exact residual_bound s

theorem basis_gram (i j : Fin 3) : (∫ s, basis i s*basis j s ∂haar)=if i=j then mass i else 0 := by
  fin_cases i <;> fin_cases j
  · simpa [basis,mass,pow_two] using haar_second_square
  · simpa [basis,mass] using haar_second_meanChannel
  · simpa [basis,mass] using haar_second_residual
  · simpa [basis,mass,mul_comm] using haar_second_meanChannel
  · simpa [basis,mass,pow_two] using haar_mean_second_moment
  · simpa [basis,mass] using haar_channels_orthogonal
  · simpa [basis,mass,mul_comm] using haar_second_residual
  · simpa [basis,mass,mul_comm] using haar_channels_orthogonal
  · simpa [basis,mass,pow_two] using haar_residual_second_moment

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkOddTrial

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkOddTrial
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open SU2SevenLinkTransfer SU2SevenLinkVariational

def linear3 (v : Fin 3 → ℝ) (s : State) : ℝ := ∑ i, v i*basis i s

theorem linear3_measurable (v : Fin 3 → ℝ) : Measurable (linear3 v) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.mul (basis_measurable i))

theorem linear3_bound (v : Fin 3 → ℝ) (s : State) : |linear3 v s| ≤ 2*∑ i, |v i| := by
  unfold linear3
  calc
    _ ≤ ∑ i, |v i*basis i s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| * 2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (basis_bound i s) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem linear3_gram (v w : Fin 3 → ℝ) :
    (∫ s, linear3 v s*linear3 w s ∂haar)=∑ i, v i*w i*mass i := by
  have hi (i j : Fin 3) : Integrable (fun s => (v i*w j)*(basis i s*basis j s)) haar :=
    (bounded_product (basis i) (basis j) (basis_measurable i) (basis_measurable j)
      2 2 (basis_bound i) (basis_bound j)).const_mul _
  have he (s : State) : linear3 v s*linear3 w s=∑ i, ∑ j, (v i*w j)*(basis i s*basis j s) := by
    unfold linear3
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  have hinner (i : Fin 3) : (∫ s, ∑ j, (v i*w j)*(basis i s*basis j s) ∂haar)=v i*w i*mass i := by
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    simp_rw [integral_const_mul,basis_gram]
    simp
  simp_rw [hinner]

def rate (β : ℝ) (i : Fin 3) : ℝ := ![coefficient β^4,coefficient β^6,coefficient β^6*quadraticCoefficient β] i

theorem basis_eigen (β : ℝ) (i : Fin 3) (s : State) :
    SU2SevenLinkTransfer.step β (basis i) s=rate β i*basis i s := by
  fin_cases i
  · exact step_second β s
  · exact step_meanChannel β s
  · exact step_residual β s

theorem linear3_evolution (β : ℝ) (v : Fin 3 → ℝ) (s : State) :
    SU2SevenLinkTransfer.step β (linear3 v) s=linear3 (fun i => rate β i*v i) s := by
  have hi (i : Fin 3) : Integrable (fun z => v i*basis i (s*z)) (noise β) :=
    (step_integrable β (basis i) (basis_measurable i) 2 (basis_bound i) s).const_mul _
  unfold SU2SevenLinkTransfer.step linear3
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_const_mul]
  change (∑ i, v i*SU2SevenLinkTransfer.step β (basis i) s)=_
  simp_rw [basis_eigen]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem linear3_kinetic_form (β : ℝ) (v : Fin 3 → ℝ) :
    pairing β (linear3 v) (linear3 v)=∑ i, rate β i*(v i)^2*mass i := by
  unfold pairing
  simp_rw [linear3_evolution]
  rw [linear3_gram]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Polynomial before applying the inverse spatial half weight. -/
def oddPolynomial (t A B : ℝ) : State → ℝ := linear3 ![1,t*A,t*B]

/-- Exact numerator on the actual spatial transfer; no exponential remainder
and no formal eigenbranch expansion occurs in this identity. -/
theorem unweighted_odd_numerator (β t A B : ℝ) :
    spatialPairing β t (unweight t (oddPolynomial t A B)) (unweight t (oddPolynomial t A B))=
      coefficient β^4/4+t^2*(coefficient β^6*A^2+3*coefficient β^6*quadraticCoefficient β*B^2)/64 := by
  rw [spatialPairing_unweight,oddPolynomial,linear3_kinetic_form]
  simp [Fin.sum_univ_three,rate,mass]
  ring

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkOddTrial

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkOddTrial
open SU2SevenLinkTransfer SU2SevenLinkVariational

theorem oddPolynomial_measurable (t A B : ℝ) : Measurable (oddPolynomial t A B) := linear3_measurable _

theorem oddPolynomial_square (t A B : ℝ) :
    (∫ s, (oddPolynomial t A B s)^2 ∂haar)=1/4+t^2*(A^2+3*B^2)/64 := by
  have h := linear3_gram ![1,t*A,t*B] ![1,t*A,t*B]
  change (∫ s, oddPolynomial t A B s*oddPolynomial t A B s ∂haar)=_ at h
  rw [← show (fun s => (oddPolynomial t A B s)^2)=(fun s => oddPolynomial t A B s*oddPolynomial t A B s) by funext s; ring] at h
  simp [Fin.sum_univ_three,mass] at h
  convert h using 1 <;> ring

/-- Actual Haar denominator after exact inverse-half-weight conjugation. -/
def denominator (t A B : ℝ) : ℝ := ∫ s, Real.exp (-t*first s)*(oddPolynomial t A B s)^2 ∂haar

private theorem polynomial_square_integrable (t A B : ℝ) :
    Integrable (fun s => (oddPolynomial t A B s)^2) haar := by
  apply Integrable.of_bound ((oddPolynomial_measurable t A B).pow_const 2).aestronglyMeasurable
    ((2*∑ i : Fin 3, |(![1,t*A,t*B] : Fin 3 → ℝ) i|)^2)
  filter_upwards with s
  rw [Real.norm_eq_abs,abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (linear3_bound ![1,t*A,t*B] s) 2

theorem denominator_integrable (t A B : ℝ) :
    Integrable (fun s => Real.exp (-t*first s)*(oddPolynomial t A B s)^2) haar := by
  have he := BoundedExponentialTiltResponse.exponential_integrable haar first first_measurable first_bound (-t)
  have h := he.bdd_mul ((oddPolynomial_measurable t A B).pow_const 2).aestronglyMeasurable
    (c := (2*∑ i : Fin 3, |(![1,t*A,t*B] : Fin 3 → ℝ) i|)^2) (by
      filter_upwards with s
      rw [Real.norm_eq_abs,abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (linear3_bound ![1,t*A,t*B] s) 2)
  simpa only [mul_comm] using h

/-- The denominator is quantitatively positive for ALL real trial parameters,
not only near zero. No vanishing-denominator convention is used. -/
theorem denominator_lower_bound (t A B : ℝ) : Real.exp (-|t|)/4 ≤ denominator t A B := by
  have hp (s : State) : Real.exp (-|t|)*(oddPolynomial t A B s)^2 ≤
      Real.exp (-t*first s)*(oddPolynomial t A B s)^2 := by
    have hab : |-t*first s| ≤ |t| := by
      rw [abs_mul,abs_neg]
      simpa using mul_le_mul_of_nonneg_left (first_bound s) (abs_nonneg t)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ((neg_le_neg hab).trans (neg_abs_le _))) (sq_nonneg _)
  have h := integral_mono ((polynomial_square_integrable t A B).const_mul (Real.exp (-|t|)))
    (denominator_integrable t A B) hp
  rw [integral_const_mul,oddPolynomial_square] at h
  change _ ≤ denominator t A B at h
  have hnon : 0 ≤ t^2*(A^2+3*B^2)/64 := by positivity
  have hex := (Real.exp_pos (-|t|)).le
  nlinarith [mul_nonneg hex hnon]

theorem denominator_positive (t A B : ℝ) : 0 < denominator t A B :=
  lt_of_lt_of_le (div_pos (Real.exp_pos _) (by norm_num)) (denominator_lower_bound t A B)

theorem unweighted_trial_norm (t A B : ℝ) :
    (∫ s, (unweight t (oddPolynomial t A B) s)^2 ∂haar)=denominator t A B :=
  unweight_square_integral t _

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkOddTrial

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkOddTrial
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open SU2SharedPlaquetteProjection SU2SevenLinkTransfer

theorem oddPolynomial_pointwise (t A B : ℝ) (s : State) :
    oddPolynomial t A B s=second s+t*(A*meanChannel s+B*SU2SevenLinkTransfer.residual s) := by
  simp [oddPolynomial,linear3,Fin.sum_univ_three,basis]
  ring

/-- Exact conditional right-path integration in the denominator. -/
def radialPolynomial (t A B x : ℝ) : ℝ :=
  1/4+t*(A+3*B)*x/8+t^2*((A-B)^2+8*B*(A+B)*x^2)/64

private theorem reduced_square (t A B : ℝ) (L U : SU2) :
    (∫ R, (halfTrace (U⁻¹*R)+t*(A*sharedMean L R+B*sharedResidual L R U))^2 ∂law)=
      radialPolynomial t A B (halfTrace (L*U)) := by
  let y := fun R => halfTrace (U⁻¹*R)
  let m := fun R => sharedMean L R
  let α := 1+t*B*halfTrace (L*U)
  let γ := t*(A-B)
  have hy : Measurable y := halfTrace_measurable.comp (measurable_const_mul U⁻¹)
  have hm : Measurable m := (halfTrace_measurable.comp (measurable_const_mul L)).div_const 4
  have hiy2 := BoundedExponentialTiltResponse.bounded_power_integrable law y hy (fun R => halfTrace_bound _) 2
  have him2 : Integrable (fun R => m R^2) law := by
    have h := BoundedExponentialTiltResponse.bounded_power_integrable law
      (fun R => halfTrace (L*R)) (halfTrace_measurable.comp (measurable_const_mul L)) (fun R => halfTrace_bound _) 2
    simpa only [m,sharedMean,div_pow] using h.div_const ((4:ℝ)^2)
  have hiym : Integrable (fun R => y R*m R) law := by
    apply Integrable.of_bound (hy.mul hm).aestronglyMeasurable 1
    filter_upwards with R
    change ‖y R*m R‖ ≤ 1
    rw [Real.norm_eq_abs,abs_mul]
    simpa using mul_le_mul (halfTrace_bound (U⁻¹*R)) (sharedMean_bound L R) (abs_nonneg _) (by norm_num)
  have hyy : (∫ R, y R^2 ∂law)=(1/4:ℝ) := trace_square_mean U⁻¹
  have hmm : (∫ R, m R^2 ∂law)=(1/64:ℝ) := by
    dsimp [m,sharedMean]
    simp only [div_pow,integral_div,trace_square_mean]
    norm_num
  have hym : (∫ R, y R*m R ∂law)=halfTrace (L*U)/16 := by
    have he (R : SU2) : y R*m R=(halfTrace (U⁻¹*R)*halfTrace (L*R))/4 := by dsimp [y,m,sharedMean]; ring
    simp_rw [he]
    rw [integral_div,translated_pair_covariance]
    have hh : halfTrace (U⁻¹*L⁻¹)=halfTrace (L*U) := by rw [← mul_inv_rev,halfTrace_inv]
    rw [hh]
    ring
  have he (R : SU2) :
      (halfTrace (U⁻¹*R)+t*(A*sharedMean L R+B*sharedResidual L R U))^2=
        (α^2*y R^2+2*α*γ*(y R*m R))+γ^2*m R^2 := by
    dsimp [α,γ,y,m,sharedResidual,sharedProduct]
    ring
  simp_rw [he]
  have h1 := integral_add (hiy2.const_mul (α^2)) (hiym.const_mul (2*α*γ))
  have h2 := integral_add ((hiy2.const_mul (α^2)).add (hiym.const_mul (2*α*γ))) (him2.const_mul (γ^2))
  simp only [Pi.add_apply] at h1 h2
  rw [h2,h1,integral_const_mul,integral_const_mul,integral_const_mul,hyy,hym,hmm]
  dsimp [α,γ,radialPolynomial]
  ring

theorem denominator_radial (t A B : ℝ) :
    denominator t A B=∫ V, Real.exp (-t*halfTrace V)*radialPolynomial t A B (halfTrace V) ∂law := by
  let F := fun L R U => Real.exp (-t*halfTrace (L*U))*
    (halfTrace (U⁻¹*R)+t*(A*sharedMean L R+B*sharedResidual L R U))^2
  let C := 2*∑ i : Fin 3, |(![1,t*A,t*B] : Fin 3 → ℝ) i|
  have he (s : State) : Real.exp (-t*first s)*(oddPolynomial t A B s)^2=F (leftPath s) (rightPath s) s.1 := by
    rw [oddPolynomial_pointwise]
    rfl
  have hF : Measurable (fun s : State => F (leftPath s) (rightPath s) s.1) := by
    have h : Measurable (fun s : State => Real.exp (-t*first s)*(oddPolynomial t A B s)^2) :=
      ((measurable_const.mul first_measurable).exp).mul ((oddPolynomial_measurable t A B).pow_const 2)
    convert h using 1
    funext s
    exact (he s).symm
  have hb (L R U : SU2) : |F L R U| ≤ Real.exp |t| * C^2 := by
    let s : State := (U,L,1,1,R,1,1)
    have hs : F L R U=Real.exp (-t*first s)*(oddPolynomial t A B s)^2 := by
      rw [he]
      simp [s,leftPath,rightPath]
    rw [hs,abs_mul,abs_of_pos (Real.exp_pos _),abs_pow]
    have hphase : -t*first s ≤ |t| := calc
      _ ≤ |-t*first s| := le_abs_self _
      _ = |t| * |first s| := by rw [abs_mul,abs_neg]
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (first_bound s) (abs_nonneg t)
      _ = |t| := mul_one _
    exact mul_le_mul (Real.exp_le_exp.mpr hphase)
      (pow_le_pow_left₀ (abs_nonneg _) (linear3_bound ![1,t*A,t*B] s) 2) (sq_nonneg _) (Real.exp_pos _).le
  unfold denominator
  simp_rw [he]
  rw [haar_path_integral F hF (Real.exp |t| * C^2) hb]
  dsimp [F]
  simp_rw [integral_const_mul,reduced_square]
  have hu (U : SU2) :
      (∫ L, Real.exp (-t*halfTrace (L*U))*radialPolynomial t A B (halfTrace (L*U)) ∂law)=
      ∫ V, Real.exp (-t*halfTrace V)*radialPolynomial t A B (halfTrace V) ∂law := by
    have hh (L : SU2) : halfTrace (L*U)=halfTrace (U*L) := halfTrace_mul_comm L U
    simp_rw [hh]
    exact integral_mul_left_eq_self (fun V => Real.exp (-t*halfTrace V)*radialPolynomial t A B (halfTrace V)) U
  simp_rw [hu]
  simp

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkOddTrial

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkOddTrial

theorem radialPolynomial_squares (t A B x : ℝ) :
    radialPolynomial t A B x=(1+t*(A+3*B)*x/4)^2/4+t^2*(A-B)^2*(1-x^2)/64 := by
  unfold radialPolynomial
  ring

theorem radialPolynomial_nonneg (t A B x : ℝ) (hx : |x| ≤ 1) : 0 ≤ radialPolynomial t A B x := by
  rw [radialPolynomial_squares]
  have hs : 0 ≤ 1-x^2 := sub_nonneg.mpr ((sq_le_one_iff_abs_le_one x).mpr hx)
  positivity

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkOddTrial
