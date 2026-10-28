import Foundation.YMPositivePower
import Mathlib.MeasureTheory.Constructions.Pi

/-! Constructed positive eigenfunction for finite-product SU2 Wilson kernels
against actual product Haar. Gauge projection and the existing seven-link
normalized-coordinate identification are separate obligations. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.YMFiniteWilsonVacuum
open QuaternionSU2Representation

private instance su2_secondCountable : SecondCountableTopology SU2 := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  exact homeomorph.symm.secondCountableTopology

def haar (n : ℕ) : Measure (Fin n → SU2) := Measure.pi (fun _ => law)

instance haar_probability (n : ℕ) : IsProbabilityMeasure (haar n) := by
  unfold haar
  infer_instance

private theorem kernel_measurable {n : ℕ} (β : ℝ) (h : (Fin n → SU2) → ℝ)
    (hh : Measurable h) : Measurable (Function.uncurry (YMPositiveKernel.weightedKernel h β)) := by
  have hk : Measurable (fun p : (Fin n → SU2) × (Fin n → SU2) =>
      YMPositiveKernel.kinetic β p.1 p.2) := by
    unfold YMPositiveKernel.kinetic
    apply Measurable.exp
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact halfTrace_measurable.comp
      (((measurable_pi_apply i).comp measurable_fst).mul
        (((measurable_pi_apply i).comp measurable_snd).inv))
  exact ((hh.comp measurable_fst).mul hk).mul (hh.comp measurable_snd)

private theorem kernel_bounds {n : ℕ} (β l u : ℝ) (h : (Fin n → SU2) → ℝ)
    (hl : 0 < l) (hh : ∀ x,l ≤ h x ∧ h x ≤ u) (x y : Fin n → SU2) :
    l^2*Real.exp (-((n:ℝ)*|β|)) ≤ YMPositiveKernel.weightedKernel h β x y ∧
      YMPositiveKernel.weightedKernel h β x y ≤ u^2*Real.exp ((n:ℝ)*|β|) := by
  have hu : 0 < u := hl.trans_le ((hh x).1.trans (hh x).2)
  have hk := YMPositiveKernel.kinetic_bounds β x y
  have hkp : 0 ≤ YMPositiveKernel.kinetic β x y := (Real.exp_pos _).le.trans hk.1
  unfold YMPositiveKernel.weightedKernel
  constructor
  · calc
      _ = l*Real.exp (-((n:ℝ)*|β|))*l := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul (hh x).1 hk.1 (Real.exp_pos _).le
        (hl.trans_le (hh x).1).le) (hh y).1 hl.le
        (mul_nonneg (hl.trans_le (hh x).1).le hkp)
  · calc
      _ ≤ u*Real.exp ((n:ℝ)*|β|)*u :=
        mul_le_mul (mul_le_mul (hh x).2 hk.2 hkp hu.le) (hh y).2
          (hl.trans_le (hh y).1).le (mul_nonneg hu.le (Real.exp_pos _).le)
      _ = _ := by ring

/-- Actual product-Haar eigenfunction existence, without a supplied vacuum.
The constants deteriorate with link count and coupling; no uniform gap follows. -/
theorem ground_exists {n : ℕ} (β l u : ℝ) (h : (Fin n → SU2) → ℝ)
    (hl : 0 < l) (hm : Measurable h) (hh : ∀ x,l ≤ h x ∧ h x ≤ u) :
    ∃ lam : ℝ, ∃ ψ : (Fin n → SU2) → ℝ, 0 < lam ∧ Measurable ψ ∧
      (∀ x,(l^2*Real.exp (-((n:ℝ)*|β|)))/(u^2*Real.exp ((n:ℝ)*|β|)) ≤ ψ x ∧
        ψ x ≤ (u^2*Real.exp ((n:ℝ)*|β|))/(l^2*Real.exp (-((n:ℝ)*|β|)))) ∧
      (∀ x,YMPositiveKernel.sandwich (haar n) h (YMPositiveKernel.kinetic β) ψ x=lam*ψ x) := by
  have hp : 0 < l^2*Real.exp (-((n:ℝ)*|β|)) :=
    mul_pos (sq_pos_of_pos hl) (Real.exp_pos _)
  obtain ⟨lam,ψ,hlo,hup,hmeas,hbounds,heigen⟩ :=
    YMPositivePower.positive_eigenfunction_exists (haar n) (YMPositiveKernel.weightedKernel h β)
      (l^2*Real.exp (-((n:ℝ)*|β|))) (u^2*Real.exp ((n:ℝ)*|β|))
      (kernel_measurable β h hm) hp (kernel_bounds β l u h hl hh) (fun _ => 1)
  refine ⟨lam,ψ,hp.trans_le hlo,hmeas,hbounds,?_⟩
  intro x
  rw [← heigen x]
  unfold YMPositivePower.applyKernel YMPositiveKernel.sandwich YMPositiveKernel.weightedKernel
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring


/-- The spatial half-weight for the first of two adjacent plaquettes in
seven indexed link coordinates (shared link0, left path1,2,3). -/
def sevenAmplitude (t : ℝ) (C : Fin 7 → SU2) : ℝ :=
  Real.exp ((t/2)*halfTrace (C 1*C 2*C 3*C 0))

private theorem sevenAmplitude_measurable (t : ℝ) : Measurable (sevenAmplitude t) := by
  unfold sevenAmplitude
  apply Measurable.exp
  apply Measurable.const_mul
  exact halfTrace_measurable.comp (by fun_prop)

private theorem sevenAmplitude_bounds (t : ℝ) (C : Fin 7 → SU2) :
    Real.exp (-|t|/2) ≤ sevenAmplitude t C ∧ sevenAmplitude t C ≤ Real.exp (|t|/2) := by
  have he : |(t/2)*halfTrace (C 1*C 2*C 3*C 0)| ≤ |t|/2 := by
    rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have ht := mul_le_mul_of_nonneg_left (halfTrace_bound (C 1*C 2*C 3*C 0))
      (div_nonneg (abs_nonneg t) (by norm_num : (0:ℝ) ≤ 2))
    simpa only [mul_one] using ht
  exact ⟨Real.exp_le_exp.mpr (by linarith [(abs_le.mp he).1]),
    Real.exp_le_exp.mpr (abs_le.mp he).2⟩

/-- Nonzero spatial tilt and arbitrary Wilson parameter: actual finite SU2
product-Haar positive eigenfunction. The normalized tuple-based seven-link
GroundData bridge is not silently assumed by this indexed/raw theorem. -/
theorem seven_raw_ground_exists (β t : ℝ) :
    ∃ lam : ℝ, ∃ ψ : (Fin 7 → SU2) → ℝ, ∃ l u : ℝ,
      0 < lam ∧ 0 < l ∧ Measurable ψ ∧ (∀ C,l ≤ ψ C ∧ |ψ C| ≤ u) ∧
      (∀ C,YMPositiveKernel.sandwich (haar 7) (sevenAmplitude t)
        (YMPositiveKernel.kinetic β) ψ C=lam*ψ C) := by
  let l := Real.exp (-|t|/2)
  let u := Real.exp (|t|/2)
  obtain ⟨lam,ψ,hp,hm,hb,he⟩ := ground_exists β l u (sevenAmplitude t)
    (Real.exp_pos _) (sevenAmplitude_measurable t) (sevenAmplitude_bounds t)
  have hlo : 0 < l^2*Real.exp (-((7:ℝ)*|β|)) := mul_pos (sq_pos_of_pos (Real.exp_pos _)) (Real.exp_pos _)
  have hup : 0 < u^2*Real.exp ((7:ℝ)*|β|) := mul_pos (sq_pos_of_pos (Real.exp_pos _)) (Real.exp_pos _)
  refine ⟨lam,ψ,(l^2*Real.exp (-((7:ℝ)*|β|)))/(u^2*Real.exp ((7:ℝ)*|β|)),
    (u^2*Real.exp ((7:ℝ)*|β|))/(l^2*Real.exp (-((7:ℝ)*|β|))),hp,div_pos hlo hup,hm,?_,he⟩
  intro C
  exact ⟨(hb C).1,by rw [abs_of_pos ((div_pos hlo hup).trans_le (hb C).1)]; exact (hb C).2⟩

end OperatorDerivativeRewrite.Foundation.YMFiniteWilsonVacuum
