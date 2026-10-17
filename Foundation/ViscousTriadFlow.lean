import Foundation.TriadGaussianDephasing

/-! Explicit viscous evolution for the actual retained Fourier triad. Its energy
decays, but the unforced deterministic evolution does not preserve the Gaussian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.ViscousTriadFlow
open TriadGaussianFlow SectorTransferSymmetry
set_option backward.isDefEq.respectTransparency false

def damping (ν t : ℝ) : ℝ := Real.exp (-ν*t)

def angle (ν t : ℝ) : ℝ := if ν=0 then t else (1-damping (2*ν) t)/(2*ν)

def stateFlow (ν t : ℝ) (x : State) : State :=
  (damping (2*ν) t*x.1,damping ν t • rotate (angle ν t*x.1) x.2)

def vectorFlow (ν t : ℝ) (x : Vector) : Vector := decode (stateFlow ν t (encode x))

theorem vectorFlow_formula (ν t : ℝ) (x : Vector) : vectorFlow ν t x=
    ![damping ν t*(Real.cos (angle ν t*x 2)*x 0+Real.sin (angle ν t*x 2)*x 1),
      damping ν t*(-Real.sin (angle ν t*x 2)*x 0+Real.cos (angle ν t*x 2)*x 1),
      damping (2*ν) t*x 2] := rfl

theorem stateFlow_zero (ν : ℝ) (x : State) : stateFlow ν 0 x=x := by
  simp [stateFlow,angle,damping,rotate_zero]

theorem vectorFlow_zero (ν : ℝ) (x : Vector) : vectorFlow ν 0 x=x := by
  simp [vectorFlow,stateFlow_zero,decode_encode]

theorem damping_derivative (ν t : ℝ) :
    HasDerivAt (damping ν) (-ν*damping ν t) t := by
  change HasDerivAt (fun s : ℝ => Real.exp (-ν*s)) _ t
  simpa [damping,mul_comm] using ((hasDerivAt_id t).const_mul (-ν)).exp

theorem angle_derivative (ν t : ℝ) (hν : ν ≠ 0) :
    HasDerivAt (angle ν) (damping (2*ν) t) t := by
  have he : angle ν=fun s => (1-damping (2*ν) s)/(2*ν) := by
    funext s
    simp [angle,hν]
  rw [he]
  convert ((hasDerivAt_const t (1 : ℝ)).sub (damping_derivative (2*ν) t)).div_const (2*ν) using 1
  <;> field_simp
  <;> ring

/-- A globally defined trajectory solving the actual viscous Fourier-derived drift. -/
theorem vectorFlow_derivative (ν : ℝ) (hν : ν ≠ 0) (x : Vector) (t : ℝ) :
    HasDerivAt (fun s => vectorFlow ν s x)
      (DictionaryTriadPotential.drift ν (vectorFlow ν t x)) t := by
  have ha := (angle_derivative ν t hν).mul_const (x 2)
  have hc := ha.cos
  have hs := ha.sin
  have hd := damping_derivative ν t
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert hd.mul ((hc.mul_const (x 0)).add (hs.mul_const (x 1))) using 1 <;>
      (try funext s) <;> simp [vectorFlow_formula,DictionaryTriadPotential.drift] <;> ring
  · convert hd.mul ((hs.neg.mul_const (x 0)).add (hc.mul_const (x 1))) using 1 <;>
      (try funext s) <;> simp [vectorFlow_formula,DictionaryTriadPotential.drift] <;> ring
  · convert (damping_derivative (2*ν) t).mul_const (x 2) using 1 <;>
      (try funext s) <;> simp [vectorFlow_formula,DictionaryTriadPotential.drift] <;> ring

theorem damping_square (ν t : ℝ) : (damping ν t)^2=damping (2*ν) t := by
  simp only [damping,pow_two,← Real.exp_add]
  congr 1
  ring

theorem plane_square (ν t : ℝ) (x : Vector) :
    (vectorFlow ν t x 0)^2+(vectorFlow ν t x 1)^2=
      damping (2*ν) t*((x 0)^2+(x 1)^2) := by
  have hs : (Real.cos (angle ν t*x 2))^2+(Real.sin (angle ν t*x 2))^2=1 := by
    linarith [Real.sin_sq_add_cos_sq (angle ν t*x 2)]
  rw [vectorFlow_formula]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  calc
    _ = (damping ν t)^2*((Real.cos (angle ν t*x 2))^2+
      (Real.sin (angle ν t*x 2))^2)*((x 0)^2+(x 1)^2) := by ring
    _ = _ := by rw [hs,damping_square]; ring

def energy (x : Vector) : ℝ := 2*(x 0)^2+2*(x 1)^2+4*(x 2)^2

/-- The actual Fourier kinetic pairing computed for this retained triad. -/
theorem energy_eq_kinetic (x : Vector) : energy x=DictionaryTriadPotential.kineticPair x x := by
  rw [DictionaryTriadPotential.kineticPair_formula]
  unfold energy
  ring

theorem energy_formula (ν t : ℝ) (x : Vector) :
    energy (vectorFlow ν t x)=
      2*damping (2*ν) t*((x 0)^2+(x 1)^2)+4*damping (4*ν) t*(x 2)^2 := by
  have hp := plane_square ν t x
  have hc : vectorFlow ν t x 2=damping (2*ν) t*x 2 := by rw [vectorFlow_formula]; rfl
  unfold energy
  rw [show 2*(vectorFlow ν t x 0)^2+2*(vectorFlow ν t x 1)^2=
    2*((vectorFlow ν t x 0)^2+(vectorFlow ν t x 1)^2) by ring,hp,hc,mul_pow,
    damping_square]
  rw [show 2*(2*ν)=4*ν by ring]
  ring

theorem damping_le_one (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) : damping ν t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith

theorem energy_decay (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) (x : Vector) :
    energy (vectorFlow ν t x) ≤ damping (2*ν) t*energy x := by
  have hd : damping (4*ν) t ≤ damping (2*ν) t := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hν ht]
  rw [energy_formula]
  unfold energy
  nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg (x 2))]

theorem energy_strict (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (x : Vector)
    (hx : 0 < energy x) : energy (vectorFlow ν t x)<energy x := by
  have hd : damping (2*ν) t<1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [mul_pos hν ht]
  have hb := energy_decay ν t hν.le ht.le x
  nlinarith [mul_pos (sub_pos.mpr hd) hx]

theorem third_second (ν t : ℝ) :
    (∫ x : State, ((stateFlow ν t x).1)^2 ∂law)=damping (4*ν) t := by
  have he : (fun x : State => ((stateFlow ν t x).1)^2)=fun x : State =>
      damping (4*ν) t*(x.1)^2 := by
    funext x
    change (damping (2*ν) t*x.1)^2=_
    rw [mul_pow,damping_square]
    rw [show 2*(2*ν)=4*ν by ring]
  rw [he,integral_const_mul,TriadGaussianDephasing.fixed_second_one,mul_one]

theorem not_gaussian_preserving (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    ¬ MeasurePreserving (stateFlow ν t) law law := by
  intro h
  have hm := integral_map (μ := law) h.measurable.aemeasurable
    (f := fun x : State => (x.1)^2) (by fun_prop)
  rw [h.map_eq,TriadGaussianDephasing.fixed_second_one,third_second] at hm
  have hd : damping (4*ν) t < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [mul_pos hν ht]
  linarith

theorem zero_viscosity (t : ℝ) (x : State) : stateFlow 0 t x=TriadGaussianFlow.flow t x := by
  simp [stateFlow,angle,damping,TriadGaussianFlow.flow]

theorem damping_add (ν s t : ℝ) : damping ν (s+t)=damping ν s*damping ν t := by
  simp only [damping,← Real.exp_add]
  congr 1
  ring

theorem angle_add (ν s t : ℝ) :
    angle ν (s+t)=angle ν t+damping (2*ν) t*angle ν s := by
  by_cases hν : ν=0
  · simp [angle,hν,damping]
    ring
  · simp only [angle,if_neg hν,damping_add]
    field_simp
    <;> ring

theorem stateFlow_add (ν s t : ℝ) (x : State) :
    stateFlow ν (s+t) x=stateFlow ν s (stateFlow ν t x) := by
  apply Prod.ext
  · change damping (2*ν) (s+t)*x.1=_
    simp only [stateFlow,damping_add]
    ring
  · change damping ν (s+t) • rotate (angle ν (s+t)*x.1) x.2=
      damping ν s • rotate (angle ν s*(damping (2*ν) t*x.1))
        (damping ν t • rotate (angle ν t*x.1) x.2)
    rw [map_smul,smul_smul,← rotate_add,damping_add,angle_add]
    congr 1
    congr 1
    ring

def secondHermite (x : State) : ℝ := (x.1)^2-1

theorem secondHermite_memLp : MemLp secondHermite 2 law := by
  have h := (GaussianCore.polynomial_memLp ((Polynomial.X : Polynomial ℝ)^2-1) 2
    (by norm_num)).comp_measurePreserving (measurePreserving_fst (μ := γ) (ν := planeGaussian))
  change MemLp (fun x : ℝ × Plane => (x.1)^2-1) 2 (γ.prod planeGaussian)
  simpa [Function.comp_def] using h

theorem secondHermite_centered : (∫ x : State, secondHermite x ∂law)=0 := by
  have hi : Integrable (fun x : State => (x.1)^2) law :=
    integrable_of_integral_eq_one TriadGaussianDephasing.fixed_second_one
  unfold secondHermite
  rw [integral_sub hi (integrable_const (1 : ℝ)),TriadGaussianDephasing.fixed_second_one]
  simp

theorem secondHermite_evolved_mean (ν t : ℝ) :
    (∫ x : State, secondHermite (stateFlow ν t x) ∂law)=damping (4*ν) t-1 := by
  have hi : Integrable (fun x : State => (x.1)^2) law :=
    integrable_of_integral_eq_one TriadGaussianDephasing.fixed_second_one
  have hj : Integrable (fun x : State => ((stateFlow ν t x).1)^2) law := by
    convert hi.const_mul ((damping (2*ν) t)^2) using 1
    funext x
    change (damping (2*ν) t*x.1)^2=_
    ring
  unfold secondHermite
  rw [integral_sub hj (integrable_const (1 : ℝ)),third_second]
  simp

theorem secondHermite_not_centered (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    (∫ x : State, secondHermite (stateFlow ν t x) ∂law)<0 := by
  rw [secondHermite_evolved_mean]
  have hd : damping (4*ν) t<1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [mul_pos hν ht]
  linarith

end OperatorDerivativeRewrite.Foundation.ViscousTriadFlow
