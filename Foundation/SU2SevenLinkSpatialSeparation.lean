import Foundation.SU2SevenLinkOddTrial

/-! Actual spatial variational comparison, with a quantitative Haar remainder.
No stationary vacuum, eigenbranch, or four-dimensional bridge is assumed. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkSpatialSeparation
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open SU2WilsonGroundCertificate SU2SevenLinkOddTrial SU2SevenLinkVariational

/-- Second-order coefficient of the ACTUAL inverse-weighted norm. -/
def normSecond (A B : ℝ) : ℝ := (A^2+3*B^2-2*A-6*B+2)/64

def radialRemainder (A B : ℝ) : ℝ := (A-B)^2/64+B*(A+B)/32

def normError (A B : ℝ) : ℝ :=
  errorConstant (-(A+3*B)/2) (B*(A+B)/2)/4+2*|radialRemainder A B|

theorem normError_nonneg (A B : ℝ) : 0 ≤ normError A B := by
  unfold normError errorConstant
  positivity

private theorem radial_decomposition (t A B x : ℝ) :
    radialPolynomial t A B x=
      trial (-(A+3*B)/2) (B*(A+B)/2) (-t) x/4+t^2*radialRemainder A B := by
  unfold radialPolynomial trial radialRemainder
  ring

/-- Cubic error before integration; valid for either sign of the spatial tilt. -/
theorem radial_remainder (t A B x : ℝ) (ht : |t| ≤ 1) (hx : |x| ≤ 1) :
    |Real.exp (-t*x)*radialPolynomial t A B x-
      (lowPart (-(A+3*B)/2) (B*(A+B)/2) (-t) x/4+t^2*radialRemainder A B)| ≤
      |t|^3*normError A B := by
  have hw := weighted_remainder (-(A+3*B)/2) (B*(A+B)/2) (-t) x
    (by simpa using ht) hx
  have htx : |-t*x| ≤ |t| := by
    rw [abs_mul,abs_neg]
    simpa using mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  have he : |Real.exp (-t*x)-1| ≤ 2*|t| :=
    (Real.abs_exp_sub_one_le (htx.trans ht)).trans (by linarith)
  have hc : |t^2*radialRemainder A B*(Real.exp (-t*x)-1)| ≤
      |t|^3*(2*|radialRemainder A B|) := by
    rw [abs_mul,abs_mul,abs_pow]
    calc
      _ ≤ |t|^2 * |radialRemainder A B| * (2*|t|) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg (sq_nonneg _) (abs_nonneg _))
      _ = _ := by ring
  have hid : Real.exp (-t*x)*radialPolynomial t A B x-
      (lowPart (-(A+3*B)/2) (B*(A+B)/2) (-t) x/4+t^2*radialRemainder A B)=
      (Real.exp (-t*x)*trial (-(A+3*B)/2) (B*(A+B)/2) (-t) x-
        lowPart (-(A+3*B)/2) (B*(A+B)/2) (-t) x)/4+
        t^2*radialRemainder A B*(Real.exp (-t*x)-1) := by
    rw [radial_decomposition]
    ring
  rw [hid]
  have hdiv := div_le_div_of_nonneg_right hw (by norm_num : (0:ℝ) ≤ 4)
  simp only [abs_neg] at hdiv
  apply (abs_add_le _ _).trans
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
  exact (add_le_add hdiv hc).trans (le_of_eq (by unfold normError; ring))

private theorem radialLow_integrable (t A B : ℝ) :
    Integrable (fun V : SU2 => lowPart (-(A+3*B)/2) (B*(A+B)/2) (-t) (halfTrace V)/4+
      t^2*radialRemainder A B) law := by
  have h1 := BoundedExponentialTiltResponse.bounded_power_integrable law halfTrace
    halfTrace_measurable halfTrace_bound 1
  have h2 := BoundedExponentialTiltResponse.bounded_power_integrable law halfTrace
    halfTrace_measurable halfTrace_bound 2
  simp only [pow_one] at h1
  unfold lowPart
  exact ((((integrable_const (1:ℝ)).add (h1.const_mul ((1+ -(A+3*B)/2)*(-t)))).add
    (((h2.const_mul (B*(A+B)/2+ -(A+3*B)/2+1/2)).sub
      (integrable_const (B*(A+B)/2/4))).const_mul ((-t)^2))).div_const 4).add
    (integrable_const (t^2*radialRemainder A B))

private theorem radialLow_integral (t A B : ℝ) :
    (∫ V : SU2, lowPart (-(A+3*B)/2) (B*(A+B)/2) (-t) (halfTrace V)/4+
      t^2*radialRemainder A B ∂law)=1/4+t^2*normSecond A B := by
  rw [integral_add (by
    have hi := radialLow_integrable t A B
    convert hi.sub (integrable_const (t^2*radialRemainder A B)) using 1
    funext V
    simp) (integrable_const _)]
  rw [integral_div,lowPart_integral law _ _ _ halfTrace halfTrace_measurable halfTrace_bound,
    (SU2TiltEnergyResponse.moment_values law).1,(SU2TiltEnergyResponse.moment_values law).2.1]
  simp only [integral_const,probReal_univ,one_smul]
  unfold radialRemainder normSecond
  ring

/-- Rigorous second-order norm expansion with explicit cubic error, for the
actual seven-link Haar trial. No formal eigenvector expansion is used. -/
theorem denominator_remainder (t A B : ℝ) (ht : |t| ≤ 1) :
    |denominator t A B-(1/4+t^2*normSecond A B)| ≤ |t|^3*normError A B := by
  let low := fun V : SU2 => lowPart (-(A+3*B)/2) (B*(A+B)/2) (-t) (halfTrace V)/4+
    t^2*radialRemainder A B
  have hl := radialLow_integrable t A B
  have hd : Integrable (fun V : SU2 => Real.exp (-t*halfTrace V)*
      radialPolynomial t A B (halfTrace V)) law := by
    apply Integrable.mono' ((integrable_const (|t|^3*normError A B)).add hl.norm)
      (by
        have hh := halfTrace_measurable
        apply Measurable.aestronglyMeasurable
        unfold radialPolynomial
        fun_prop)
    filter_upwards with V
    have h := radial_remainder t A B (halfTrace V) ht (halfTrace_bound V)
    change ‖_‖ ≤ _
    rw [Real.norm_eq_abs]
    have htri := abs_add_le (Real.exp (-t*halfTrace V)*radialPolynomial t A B (halfTrace V)-low V) (low V)
    dsimp [low] at htri ⊢
    rw [sub_add_cancel] at htri
    exact htri.trans (add_le_add h le_rfl)
  have h := norm_integral_le_of_norm_le_const (μ := law)
    (f := fun V : SU2 => Real.exp (-t*halfTrace V)*radialPolynomial t A B (halfTrace V)-low V)
    (Filter.Eventually.of_forall (fun V => by
      simpa only [Real.norm_eq_abs] using radial_remainder t A B (halfTrace V) ht (halfTrace_bound V)))
  rw [integral_sub hd hl,Real.norm_eq_abs] at h
  simp only [probReal_univ,mul_one] at h
  rw [← denominator_radial,radialLow_integral] at h
  exact h

/-- Optimizers of the leading two retained mixed channels. -/
def oddA (β : ℝ) : ℝ := 1/(1-coefficient β^2)
def oddB (β : ℝ) : ℝ := 1/(1-coefficient β^2*quadraticCoefficient β)

def kineticSecond (β A B : ℝ) : ℝ :=
  (coefficient β^6*A^2+3*coefficient β^6*quadraticCoefficient β*B^2)/64

def leadingGap (β : ℝ) : ℝ := kineticSecond β (oddA β) (oddB β)-
  coefficient β^4*normSecond (oddA β) (oddB β)-coefficient β^4*vacuumSecond (coefficient β^4)/4

private theorem optimized_gap_identity (x d : ℝ) (hx : x ≠ 1) (hxd : x*d ≠ 1)
    (hx2 : x^2 ≠ 1) :
    (x^3*(1/(1-x))^2+3*x^3*d*(1/(1-x*d))^2)/64-
      x^2*normSecond (1/(1-x)) (1/(1-x*d))-x^2*vacuumSecond (x^2)/4 =
      x^2/32*((1+x)/(4*(1-x))+3*(1+x*d)/(4*(1-x*d))-(1+x^2)/(1-x^2)) := by
  unfold normSecond vacuumSecond
  field_simp [sub_ne_zero.mpr (Ne.symm hx),sub_ne_zero.mpr (Ne.symm hxd),
    sub_ne_zero.mpr (Ne.symm hx2)]
  <;> ring

/-- Strictly positive actual leading variational separation whenever the Wilson
first channel is nonzero. Moment positivity is proved for the actual law. -/
theorem leadingGap_positive (β : ℝ) (hc : coefficient β ≠ 0) : 0 < leadingGap β := by
  let x := coefficient β^2
  have hx : 0 < x := sq_pos_of_ne_zero hc
  have hxm : x ≤ secondMoment β := coefficient_square_le_secondMoment β
  have hm := secondMoment_lt_one β
  have hx1 : x < 1 := hxm.trans_lt hm
  have hxd : x*quadraticCoefficient β < 1 := calc
    _ ≤ x*|quadraticCoefficient β| := mul_le_mul_of_nonneg_left (le_abs_self _) hx.le
    _ < x*1 := mul_lt_mul_of_pos_left (quadraticCoefficient_abs_lt_one β) hx
    _ < 1 := by simpa using hx1
  have hx2 : x^2 < 1 := pow_lt_one₀ hx.le hx1 (by decide)
  have hid := optimized_gap_identity x (quadraticCoefficient β) (ne_of_lt hx1)
    (ne_of_lt hxd) (ne_of_lt hx2)
  have he : leadingGap β=x^2/32*SU2SharedPlaquetteProjection.overlapBracket x (secondMoment β) := by
    unfold leadingGap kineticSecond oddA oddB
    rw [show coefficient β^4=x^2 by dsimp [x]; ring,
      show coefficient β^6=x^3 by dsimp [x]; ring]
    exact hid
  rw [he]
  exact mul_pos (div_pos (sq_pos_of_pos hx) (by norm_num))
    (SU2SharedPlaquetteProjection.overlapBracket_positive x (secondMoment β) hx hxm hm)

/-- Explicit cubic constant in the normalized comparison. -/
def comparisonError (d E μ C : ℝ) : ℝ :=
  E+μ*(|d|+E)+2*C*(1/4+|d|+E)

private theorem product_upper (t D d E μ C : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hE : 0 ≤ E) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (hD : D ≤ 1/4+t^2*d+t^3*E) :
    (1+μ*t^2+2*C*t^3)*D ≤
      1/4+(d+μ/4)*t^2+comparisonError d E μ C*t^3 := by
  have ht2 : t^2 ≤ t := by nlinarith
  have ht3 : t^3 ≤ t := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht2)]
  have hb : D ≤ 1/4+|d|+E := calc
    _ ≤ 1/4+t^2*d+t^3*E := hD
    _ ≤ 1/4+t^2*|d|+t^3*E := by nlinarith [mul_le_mul_of_nonneg_left (le_abs_self d) (sq_nonneg t)]
    _ ≤ 1/4+|d|+E := by
      have hd := mul_le_mul_of_nonneg_right (ht2.trans ht1) (abs_nonneg d)
      have he := mul_le_mul_of_nonneg_right (ht3.trans ht1) hE
      nlinarith
  have hs : D-1/4 ≤ t*(|d|+E) := calc
    _ ≤ t^2*d+t^3*E := by linarith
    _ ≤ t^2*|d|+t^3*E := by nlinarith [mul_le_mul_of_nonneg_left (le_abs_self d) (sq_nonneg t)]
    _ ≤ t*|d|+t*E := add_le_add (mul_le_mul_of_nonneg_right ht2 (abs_nonneg _))
      (mul_le_mul_of_nonneg_right ht3 hE)
    _ = _ := by ring
  have hsμ := mul_le_mul_of_nonneg_left hs (mul_nonneg hμ (sq_nonneg t))
  have hbC := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*C*t^3)
  unfold comparisonError
  nlinarith [hsμ,hbC]

/-- Explicit sufficient smallness for a strict ACTUAL spatial Rayleigh test.
This is an integral inequality, not an assertion of stationary spectrum. -/
theorem spatial_separation (β t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (herror : coefficient β^4*
      comparisonError (normSecond (oddA β) (oddB β)) (normError (oddA β) (oddB β))
        (vacuumSecond (coefficient β^4))
        (eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4))*t < leadingGap β) :
    coefficient β^4*(1+vacuumSecond (coefficient β^4)*t^2+
      2*eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4)*t^3)*
      (∫ s, (unweight t (oddPolynomial t (oddA β) (oddB β)) s)^2 ∂SU2SevenLinkTransfer.haar) <
    spatialPairing β t (unweight t (oddPolynomial t (oddA β) (oddB β)))
      (unweight t (oddPolynomial t (oddA β) (oddB β))) := by
  have ha : 0 ≤ coefficient β^4 := by positivity
  have ha1 : coefficient β^4 < 1 := by
    have h := pow_lt_one₀ (abs_nonneg (coefficient β)) (coefficient_abs_lt_one β) (by decide : (4:ℕ) ≠ 0)
    rw [← abs_pow] at h
    exact (le_abs_self _).trans_lt h
  have hμ : 0 ≤ vacuumSecond (coefficient β^4) := by
    unfold vacuumSecond
    positivity
  have hd := denominator_remainder t (oddA β) (oddB β) (by rwa [abs_of_pos ht])
  rw [abs_of_pos ht] at hd
  have hd' := (le_abs_self (denominator t (oddA β) (oddB β)-
    (1/4+t^2*normSecond (oddA β) (oddB β)))).trans hd
  have hu := product_upper t (denominator t (oddA β) (oddB β))
    (normSecond (oddA β) (oddB β)) (normError (oddA β) (oddB β))
    (vacuumSecond (coefficient β^4)) (eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4))
    ht.le ht1 (normError_nonneg _ _) hμ (eigenErrorConstant_nonneg _ _) (by linarith)
  have hu' := mul_le_mul_of_nonneg_left hu ha
  have hstrict := mul_lt_mul_of_pos_right herror (sq_pos_of_pos ht)
  rw [unweighted_trial_norm,unweighted_odd_numerator]
  unfold leadingGap kineticSecond at hstrict
  nlinarith [hu',hstrict]

/-- An open interval of actual spatial separation exists at EVERY finite
parameter with a nonzero first Wilson channel. The vacuum smallness condition
is proved on the same interval. This is not a uniform-in-coupling interval. -/
theorem exists_separation_interval (β : ℝ) (hc : coefficient β ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < δ →
      (|linearCoefficient (coefficient β^4)| * |t|+
        |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| * |t|^2 ≤ 1/2) ∧
      coefficient β^4*(1+vacuumSecond (coefficient β^4)*t^2+
        2*eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4)*t^3)*
        (∫ s, (unweight t (oddPolynomial t (oddA β) (oddB β)) s)^2 ∂SU2SevenLinkTransfer.haar) <
      spatialPairing β t (unweight t (oddPolynomial t (oddA β) (oddB β)))
        (unweight t (oddPolynomial t (oddA β) (oddB β))) := by
  let K := coefficient β^4*
    comparisonError (normSecond (oddA β) (oddB β)) (normError (oddA β) (oddB β))
      (vacuumSecond (coefficient β^4))
      (eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4))
  let S := |linearCoefficient (coefficient β^4)|+
    |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)|
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hK : 0 < |K|+1 := by positivity
  have hS1 : 0 < 2*(S+1) := by positivity
  let δ := min 1 (min (leadingGap β/(|K|+1)) (1/(2*(S+1))))
  have hδ : 0 < δ := lt_min (by norm_num)
    (lt_min (div_pos (leadingGap_positive β hc) hK) (div_pos (by norm_num) hS1))
  refine ⟨δ,hδ,min_le_left _ _,?_⟩
  intro t ht htδ
  have ht1 : t ≤ 1 := htδ.le.trans (min_le_left _ _)
  have htK : t < leadingGap β/(|K|+1) := htδ.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have htS : t < 1/(2*(S+1)) := htδ.trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have he : K*t < leadingGap β := by
    have h := (lt_div_iff₀ hK).mp htK
    have h' := mul_le_mul_of_nonneg_right (le_abs_self K) ht.le
    nlinarith
  have hs : |linearCoefficient (coefficient β^4)| * |t|+
      |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| * |t|^2 ≤ 1/2 := by
    rw [abs_of_pos ht]
    have ht2 : t^2 ≤ t := by nlinarith
    have h := (lt_div_iff₀ hS1).mp htS
    have h' := mul_le_mul_of_nonneg_left ht2
      (abs_nonneg (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)))
    dsimp [S] at h
    nlinarith
  exact ⟨hs,spatial_separation β t ht ht1 he⟩

open SU2SevenLinkTransfer

/-- Quantitative pointwise lower bound: the certified vacuum has a bounded
inverse on the SAME smallness domain, with no assumed ground state. -/
theorem trialVacuum_lower (β t : ℝ)
    (hsmall : |linearCoefficient (coefficient β^4)| * |t|+
      |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| * |t|^2 ≤ 1/2)
    (s : State) : Real.exp (-|t|/2)/2 ≤ trialVacuum β t s := by
  have hab : |t*first s/2| ≤ |t|/2 := by
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left (first_bound s) (abs_nonneg t)) (by norm_num)
  have he : Real.exp (-|t|/2) ≤ halfWeight t s := Real.exp_le_exp.mpr (by
    have h := neg_abs_le (t*first s/2)
    linarith)
  have hp := trial_positive (linearCoefficient (coefficient β^4))
    (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t (first s) (first_bound s) hsmall
  change _ ≤ halfWeight t s*trial _ _ t (first s)
  have hh : 0 ≤ halfWeight t s := (Real.exp_pos _).le
  nlinarith [mul_nonneg hh (by linarith : 0 ≤ trial (linearCoefficient (coefficient β^4))
    (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t (first s)-1/2)]

/-- Actual odd trial belongs to the reweighted bounded form core. In particular,
the upper comparison and lower trial are not being taken on disjoint domains. -/
theorem trial_admissible (β t A B : ℝ)
    (hsmall : |linearCoefficient (coefficient β^4)| * |t|+
      |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| * |t|^2 ≤ 1/2) :
    ∃ r : State → ℝ, Measurable r ∧ (∃ R : ℝ, ∀ s, |r s| ≤ R) ∧
      unweight t (oddPolynomial t A B) = fun s => trialVacuum β t s*r s := by
  let f := unweight t (oddPolynomial t A B)
  let u := trialVacuum β t
  let r := fun s => f s/u s
  have hf : Measurable f := unweight_measurable t _ (oddPolynomial_measurable t A B)
  have hu : Measurable u := trialVacuum_measurable β t
  let M := Real.exp (|t|/2)*(2*∑ i : Fin 3, |(![1,t*A,t*B] : Fin 3 → ℝ) i|)
  let l := Real.exp (-|t|/2)/2
  have hl : 0 < l := div_pos (Real.exp_pos _) (by norm_num)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb (s : State) : |f s| ≤ M := by
    change |halfWeight (-t) s*oddPolynomial t A B s| ≤ M
    rw [abs_mul]
    have he := halfWeight_bound (-t) s
    rw [abs_neg] at he
    exact mul_le_mul he (linear3_bound ![1,t*A,t*B] s) (abs_nonneg _) (Real.exp_pos _).le
  refine ⟨r,hf.div hu,⟨M/l,?_⟩,?_⟩
  · intro s
    have hlu : l ≤ u s := trialVacuum_lower β t hsmall s
    have hup : 0 < u s := hl.trans_le hlu
    dsimp [r]
    rw [abs_div,abs_of_pos hup]
    apply (div_le_div_iff₀ hup hl).mpr
    exact (mul_le_mul_of_nonneg_right (hb s) hl.le).trans
      (mul_le_mul_of_nonneg_left hlu hM)
  · funext s
    have hup : u s ≠ 0 := ne_of_gt (trialVacuum_positive β t hsmall s)
    change f s=u s*(f s/u s)
    field_simp

/-- Actual trial quotient, with the denominator proved strictly positive for all
real parameters. An upper certificate is not silently called an eigenvalue. -/
def trialQuotient (β t A B : ℝ) : ℝ :=
  spatialPairing β t (unweight t (oddPolynomial t A B)) (unweight t (oddPolynomial t A B))/denominator t A B

/-- Conditional stationary-normalization bridge: ANY positive normalization
below the certified upper value inherits the strict quotient comparison.
Existence of a vacuum, its parity, and the stationary transform are NOT assumed
as axioms or claimed to follow from this scalar consequence. -/
theorem normalized_trial_separation (β t ell : ℝ) (hell : 0 < ell) (ht : 0 < t) (ht1 : t ≤ 1)
    (hellq : ell ≤ 1+vacuumSecond (coefficient β^4)*t^2+
      2*eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4)*t^3)
    (herror : coefficient β^4*
      comparisonError (normSecond (oddA β) (oddB β)) (normError (oddA β) (oddB β))
        (vacuumSecond (coefficient β^4))
        (eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4))*t < leadingGap β) :
    coefficient β^4 < trialQuotient β t (oddA β) (oddB β)/ell := by
  have hs := spatial_separation β t ht ht1 herror
  rw [unweighted_trial_norm] at hs
  have hD := denominator_positive t (oddA β) (oddB β)
  have ha : 0 ≤ coefficient β^4 := by positivity
  apply (lt_div_iff₀ hell).mpr
  unfold trialQuotient
  apply (lt_div_iff₀ hD).mpr
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hellq ha) hD.le
  exact hm.trans_lt hs

/-- The same actual trial has the certified upper form bound. -/
theorem trial_quotient_upper (β t A B : ℝ) (ht : |t| ≤ 1)
    (hsmall : |linearCoefficient (coefficient β^4)| * |t|+
      |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| * |t|^2 ≤ 1/2) :
    trialQuotient β t A B ≤ 1+vacuumSecond (coefficient β^4)*t^2+
      2*eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4)*|t|^3 := by
  obtain ⟨r,hr,⟨R,hR⟩,he⟩ := trial_admissible β t A B hsmall
  have h := trialVacuum_form_bound β t ht hsmall r hr R hR
  have hs (s : State) : trialVacuum β t s*r s=unweight t (oddPolynomial t A B) s := (congrFun he s).symm
  simp_rw [hs] at h
  rw [unweighted_trial_norm] at h
  exact (div_le_iff₀ (denominator_positive t A B)).mpr h

/-- Actual bounded-form sandwich on a nonempty spatial interval. It compares
a finite seven-link spatial Rayleigh quotient with a positive upper certificate;
it neither declares the quotient an eigenvalue nor supplies physical distance. -/
theorem exists_quotient_sandwich (β : ℝ) (hc : coefficient β ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < δ →
      let q := 1+vacuumSecond (coefficient β^4)*t^2+
        2*eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4)*t^3
      coefficient β^4*q < trialQuotient β t (oddA β) (oddB β) ∧
        trialQuotient β t (oddA β) (oddB β) ≤ q := by
  obtain ⟨δ,hδ,hδ1,hall⟩ := exists_separation_interval β hc
  refine ⟨δ,hδ,hδ1,?_⟩
  intro t ht htδ
  obtain ⟨hsmall,hsep⟩ := hall t ht htδ
  have ht1 : |t| ≤ 1 := by rw [abs_of_pos ht]; exact htδ.le.trans hδ1
  constructor
  · rw [unweighted_trial_norm] at hsep
    exact (lt_div_iff₀ (denominator_positive t (oddA β) (oddB β))).mpr hsep
  · simpa only [abs_of_pos ht] using trial_quotient_upper β t (oddA β) (oddB β) ht1 hsmall

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkSpatialSeparation
