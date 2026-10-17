import Foundation.ParameterizedTriadRepresentative
import Foundation.DictionaryTriadLocalization
import Mathlib.Analysis.Calculus.MeanValue

/-! Actual retained Fourier convolution, Leray projection, kinetic pairing and
a scalar-potential obstruction for the existing three-amplitude periodic triad. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.DictionaryTriadPotential
open SectorTransferSymmetry ParameterizedSectorTriad
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

def rawSymbol (a b c : ℝ) (m : Wave) (i : Fin 3) : ℝ :=
  ∑ p ∈ SectorTriadSign.modes, ∑ q ∈ SectorTriadSign.modes,
    if p+q=m then dotWave q (polarization a b c p)*polarization a b c q i else 0

def rawValues (a b c : ℝ) (j : Fin 6) : Vector :=
  ![![-2*b*c,b*c,0],![a*c,-2*a*c,0],![-a*b,-a*b,0],
    ![2*b*c,-b*c,0],![-a*c,2*a*c,0],![a*b,a*b,0]] j

theorem raw_on_mode (a b c : ℝ) (j : Fin 6) :
    rawSymbol a b c (SectorTriadSign.mode j)=rawValues a b c j := by
  ext i
  simp only [rawSymbol,SectorTriadSign.sum_modes,polarization_mode]
  fin_cases j <;> fin_cases i <;>
    norm_num [Fin.sum_univ_succ,SectorTriadSign.mode,amplitude,rawValues,dotWave,
      funext_iff,Fin.forall_fin_succ,Pi.add_apply] <;> ring

theorem projected_on_mode (a b c : ℝ) (j : Fin 6) :
    DictionaryTriadLocalization.leray (SectorTriadSign.mode j)
      (rawSymbol a b c (SectorTriadSign.mode j))=amplitude (b*c) (-a*c) 0 j := by
  rw [raw_on_mode]
  ext i
  fin_cases j <;> fin_cases i <;>
    norm_num [DictionaryTriadLocalization.leray,rawValues,SectorTriadSign.mode,
      amplitude,dotWave,waveSquare,Fin.sum_univ_succ] <;> ring

def drift (ν : ℝ) (x : Vector) : Vector :=
  ![x 1*x 2-ν*x 0,-x 0*x 2-ν*x 1,-2*ν*x 2]

theorem viscous_projected_on_mode (ν a b c : ℝ) (j : Fin 6) :
    (fun i => DictionaryTriadLocalization.leray (SectorTriadSign.mode j)
      (rawSymbol a b c (SectorTriadSign.mode j)) i-
        ν*waveSquare (SectorTriadSign.mode j)*polarization a b c (SectorTriadSign.mode j) i)=
      amplitude (b*c-ν*a) (-a*c-ν*b) (-2*ν*c) j := by
  rw [projected_on_mode,polarization_mode]
  ext i
  fin_cases j <;> fin_cases i <;>
    norm_num [SectorTriadSign.mode,amplitude,waveSquare,Fin.sum_univ_succ] <;>
      ring_nf <;> simp

/-- Negative advection coefficients with the existing i*polarization convention. -/
def negativeComplexSymbol (a b c : ℝ) (m : Wave) (i : Fin 3) : ℂ :=
  ∑ p ∈ SectorTriadSign.modes, ∑ q ∈ SectorTriadSign.modes,
    if p+q=m then -((∑ j : Fin 3,
      ParameterizedTriadRepresentative.coefficient a b c p j*((q j : ℂ)*Complex.I))*
        ParameterizedTriadRepresentative.coefficient a b c q i) else 0

theorem phase_summand (a b c : ℝ) (p q : Wave) (i : Fin 3) :
    -((∑ j : Fin 3,
      ParameterizedTriadRepresentative.coefficient a b c p j*((q j : ℂ)*Complex.I))*
        ParameterizedTriadRepresentative.coefficient a b c q i)=
      Complex.I*((dotWave q (polarization a b c p)*polarization a b c q i : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [ParameterizedTriadRepresentative.coefficient,Fin.sum_univ_three,dotWave,
      Complex.mul_re,Complex.mul_im] <;> ring

theorem negativeComplexSymbol_phase (a b c : ℝ) (m : Wave) :
    negativeComplexSymbol a b c m=fun i => Complex.I*(rawSymbol a b c m i : ℂ) := by
  ext i
  have ht (p q : Wave) :
      (if p+q=m then -((∑ j : Fin 3,
        ParameterizedTriadRepresentative.coefficient a b c p j*((q j : ℂ)*Complex.I))*
          ParameterizedTriadRepresentative.coefficient a b c q i) else 0)=
        Complex.I*((if p+q=m then dotWave q (polarization a b c p)*
          polarization a b c q i else 0 : ℝ) : ℂ) := by
    split_ifs <;> simp [phase_summand]
  simp only [negativeComplexSymbol,ht,rawSymbol]
  push_cast
  simp only [Finset.mul_sum]

/-- Complexification of the real Fourier Leray projector. -/
def complexLeray (m : Wave) (v : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  (DictionaryTriadLocalization.leray m (fun j => (v j).re) i : ℂ)+
    Complex.I*(DictionaryTriadLocalization.leray m (fun j => (v j).im) i : ℂ)

theorem complexLeray_formula (m : Wave) (v : Fin 3 → ℂ) (i : Fin 3) :
    complexLeray m v i = v i-
      ((∑ j : Fin 3, (m j : ℂ)*v j)/(waveSquare m : ℂ))*(m i : ℂ) := by
  apply Complex.ext <;>
    simp [complexLeray,DictionaryTriadLocalization.leray,dotWave,
      Complex.mul_re,Complex.mul_im]

theorem complexLeray_phase (m : Wave) (v : Vector) :
    complexLeray m (fun i => Complex.I*(v i : ℂ))=
      fun i => Complex.I*(DictionaryTriadLocalization.leray m v i : ℂ) := by
  ext i
  simp [complexLeray,DictionaryTriadLocalization.leray,dotWave,
    Complex.mul_re,Complex.mul_im]

/-- The projected negative complex advection has exactly the claimed amplitudes. -/
theorem projected_complex_on_mode (a b c : ℝ) (j : Fin 6) :
    complexLeray (SectorTriadSign.mode j)
      (negativeComplexSymbol a b c (SectorTriadSign.mode j))=
        ParameterizedTriadRepresentative.coefficient (b*c) (-a*c) 0 (SectorTriadSign.mode j) := by
  rw [negativeComplexSymbol_phase,complexLeray_phase,projected_on_mode]
  ext i
  simp [ParameterizedTriadRepresentative.coefficient,polarization_mode]

/-- The actual finite Fourier kinetic pairing; no frequency weight is inserted. -/
def kineticPair (x y : Vector) : ℝ :=
  ∑ k ∈ SectorTriadSign.modes,
    dotVector (polarization (x 0) (x 1) (x 2) k) (polarization (y 0) (y 1) (y 2) k)

theorem kineticPair_formula (x y : Vector) :
    kineticPair x y=2*x 0*y 0+2*x 1*y 1+4*x 2*y 2 := by
  simp only [kineticPair,SectorTriadSign.sum_modes,polarization_mode]
  norm_num [amplitude,dotVector,Fin.sum_univ_succ] <;> ring

theorem nonlinear_energy_cancellation (x : Vector) : kineticPair x (drift 0 x)=0 := by
  rw [kineticPair_formula]
  simp [drift] <;> ring

theorem viscous_energy_dissipation (ν : ℝ) (x : Vector) :
    kineticPair x (drift ν x) = -ν*energyValue (x 0) (x 1) (x 2) := by
  rw [kineticPair_formula]
  simp [drift,energyValue] <;> ring

/-- Unequal cross derivatives persist after adding diagonal viscous damping. -/
theorem cross_derivatives (ν a b c : ℝ) :
    deriv (fun y => drift ν ![a,y,c] 0) b=c ∧
      deriv (fun y => drift ν ![y,b,c] 1) a=-c := by
  constructor
  · simpa [drift] using (((hasDerivAt_id b).mul_const c).sub_const (ν*a)).deriv
  · simpa [drift] using (((hasDerivAt_id a).neg.mul_const c).sub_const (ν*b)).deriv

/-- Exact endpoint difference, proved by subtracting a primitive. -/
theorem affine_derivative_difference (f : ℝ → ℝ) (s t : ℝ)
    (hf : ∀ x, HasDerivAt f (s+t*x) x) : f 1-f 0=s+t/2 := by
  let g : ℝ → ℝ := fun x => f x-(s*x+(t/2)*x^2)
  have hd (x : ℝ) : HasDerivAt g 0 x := by
    have hp := ((hasDerivAt_id x).const_mul s).add
      ((hasDerivAt_pow 2 x).const_mul (t/2))
    convert (hf x).sub hp using 1 <;> first | rfl | (norm_num; ring)
  have he := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) 1 0
  dsimp [g] at he
  linarith

/-- A rectangle test rules out a potential with these partial derivatives.
Only ordinary one-variable derivatives are assumed; no Hessian regularity is needed. -/
theorem no_weighted_potential (ν c wa wb : ℝ) (hc : c ≠ 0)
    (hwa : 0 < wa) (hwb : 0 < wb) :
    ¬ ∃ Φ : ℝ → ℝ → ℝ,
      (∀ a b, HasDerivAt (fun x => Φ x b) (wa*(b*c-ν*a)) a) ∧
      (∀ a b, HasDerivAt (fun y => Φ a y) (wb*(-a*c-ν*b)) b) := by
  rintro ⟨Φ,ha,hb⟩
  have ea (b : ℝ) : Φ 1 b-Φ 0 b=wa*b*c-wa*ν/2 := by
    have h := affine_derivative_difference (fun x => Φ x b) (wa*b*c) (-wa*ν)
      (fun x => by convert ha x b using 1 <;> ring)
    nlinarith
  have eb (a : ℝ) : Φ a 1-Φ a 0=-wb*a*c-wb*ν/2 := by
    have h := affine_derivative_difference (fun y => Φ a y) (-wb*a*c) (-wb*ν)
      (fun y => by convert hb a y using 1 <;> ring)
    nlinarith
  have he : (wa+wb)*c=0 := by
    have ha0 := ea 0
    have ha1 := ea 1
    have hb0 := eb 0
    have hb1 := eb 1
    nlinarith
  exact (mul_ne_zero (ne_of_gt (add_pos hwa hwb)) hc) he

/-- The finite kinetic metric has weights two in the first two coordinates. -/
theorem no_kinetic_potential (ν : ℝ) :
    ¬ ∃ Φ : Vector → ℝ,
      (∀ a b c, HasDerivAt (fun x => Φ ![x,b,c]) (2*drift ν ![a,b,c] 0) a) ∧
      (∀ a b c, HasDerivAt (fun y => Φ ![a,y,c]) (2*drift ν ![a,b,c] 1) b) := by
  rintro ⟨Φ,ha,hb⟩
  apply no_weighted_potential ν 1 2 2 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨fun a b => Φ ![a,b,1], ?_, ?_⟩
  · intro a b
    simpa [drift] using ha a b 1
  · intro a b
    simpa [drift] using hb a b 1

theorem no_negative_kinetic_potential (ν : ℝ) :
    ¬ ∃ Φ : Vector → ℝ,
      (∀ a b c, HasDerivAt (fun x => Φ ![x,b,c]) (-2*drift ν ![a,b,c] 0) a) ∧
      (∀ a b c, HasDerivAt (fun y => Φ ![a,y,c]) (-2*drift ν ![a,b,c] 1) b) := by
  rintro ⟨Φ,ha,hb⟩
  apply no_kinetic_potential ν
  refine ⟨fun x => -Φ x, ?_, ?_⟩
  · intro a b c
    convert (ha a b c).neg using 1 <;> ring
  · intro a b c
    convert (hb a b c).neg using 1 <;> ring

end OperatorDerivativeRewrite.Foundation.DictionaryTriadPotential
