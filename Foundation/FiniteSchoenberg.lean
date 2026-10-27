import Foundation.FiniteBochnerObstruction
/-! Finite Schoenberg equivalence for real Fourier symbols. The Schur
product theorem and exponential series show that the entrywise exponential
of a PSD matrix is PSD. A rank-one factor then converts anchored covariance
PSD to positivity of every finite heat-multiplier matrix. The converse takes
the right derivative at time zero on zero-sum vectors. No spatial Markov
operator or probability measure is constructed here. -/
open OperatorDerivativeRewrite.Foundation
open Filter Set
open scoped MatrixOrder Topology BigOperators

noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteSchoenberg
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open FourierCovarianceCriterion FiniteFourierDifferentialTrace FiniteStableGamma.Core

def entryPower (K : Matrix ι ι ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  fun i j => K i j ^ n

omit [DecidableEq ι] in
theorem entryPower_psd (K : Matrix ι ι ℝ) (hK : K.PosSemidef) (n : ℕ) :
    (entryPower K n).PosSemidef := by
  induction n with
  | zero =>
      have h := Matrix.posSemidef_gram ℝ (fun _ : ι => (1 : ℝ))
      convert h using 1
      ext i j
      simp [entryPower,Matrix.gram]
  | succ n ih =>
      have h := ih.hadamard hK
      convert h using 1
      ext i j
      simp [entryPower,Matrix.hadamard_apply,pow_succ]

def partialExp (K : Matrix ι ι ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  ∑ m ∈ Finset.range n, ((Nat.factorial m : ℝ)⁻¹) • entryPower K m

omit [DecidableEq ι] in
theorem partialExp_psd (K : Matrix ι ι ℝ) (hK : K.PosSemidef) (n : ℕ) :
    (partialExp K n).PosSemidef := by
  induction n with
  | zero => simpa [partialExp] using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef)
  | succ n ih =>
      rw [partialExp,Finset.sum_range_succ]
      exact ih.add ((entryPower_psd K hK n).smul (inv_nonneg.mpr (Nat.cast_nonneg _)))

omit [Fintype ι] [DecidableEq ι] in
theorem partialExp_tendsto (K : Matrix ι ι ℝ) :
    Filter.Tendsto (partialExp K) Filter.atTop
      (𝓝 (fun i j => Real.exp (K i j))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := (NormedSpace.expSeries_div_hasSum_exp (K i j)).tendsto_sum_nat
  rw [← Real.exp_eq_exp_ℝ] at h
  simpa only [partialExp,Matrix.sum_apply,Matrix.smul_apply,
    entryPower,smul_eq_mul,div_eq_mul_inv,mul_comm] using h

omit [DecidableEq ι] in
theorem entrywise_exp_psd (K : Matrix ι ι ℝ) (hK : K.PosSemidef) :
    Matrix.PosSemidef (fun i j => Real.exp (K i j)) := by
  exact Matrix.posSemidef_is_closed.mem_of_tendsto
    (partialExp_tendsto K) (Filter.Eventually.of_forall (partialExp_psd K hK))

theorem heat_multiplier_psd_of_covariance (ψ : Wave → ℝ)
    (hψ : CovarianceSymbol ψ) (t : ℝ) (ht : 0 ≤ t)
    (k : ι → Wave) :
    Matrix.PosSemidef (fun i j => Real.exp (-t*ψ (k j-k i))) := by
  let K : Matrix ι ι ℝ := fun i j => kernel ψ (k i) (k j)
  let u : ι → ℝ := fun i => Real.exp (-t*ψ (k i))
  have hK : K.PosSemidef := hψ ι k
  have hScaled : Matrix.PosSemidef (fun i j => Real.exp (2*t*K i j)) := by
    have hs : ((2*t) • K).PosSemidef := hK.smul (by positivity)
    convert entrywise_exp_psd ((2*t) • K) hs using 1
  have hRank : (Matrix.vecMulVec u u).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star u
  have h := hRank.hadamard hScaled
  have heq : (fun i j => Real.exp (-t*ψ (k j-k i)) : Matrix ι ι ℝ) =
      (Matrix.vecMulVec u u).hadamard (fun i j => Real.exp (2*t*K i j)) := by
    ext i j
    have he : -t*ψ (k i) + -t*ψ (k j) + 2*t*kernel ψ (k i) (k j) =
        -t*ψ (k j-k i) := by
      unfold kernel
      ring
    change Real.exp (-t*ψ (k j-k i)) =
      Real.exp (-t*ψ (k i)) * Real.exp (-t*ψ (k j)) *
        Real.exp (2*t*kernel ψ (k i) (k j))
    rw [← Real.exp_add,← Real.exp_add,he]
  rw [heq]
  exact h

theorem heat_multiplier_psd_of_negative (ψ : Wave → ℝ)
    (h0 : ψ 0 = 0) (he : ∀ k, ψ (-k) = ψ k)
    (hψ : NegativeSymbol ψ) (t : ℝ) (ht : 0 ≤ t)
    (k : ι → Wave) :
    Matrix.PosSemidef (fun i j => Real.exp (-t*ψ (k j-k i))) :=
  heat_multiplier_psd_of_covariance ψ ((symbol_iff ψ h0 he).mpr hψ) t ht k

def HeatPositiveSymbol (ψ : Wave → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (k : ι → Wave)
    (t : ℝ), 0 ≤ t →
      Matrix.PosSemidef (fun i j => Real.exp (-t*ψ (k j-k i)))

def expEnergy (d : ι → ι → ℝ) (w : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * Real.exp (-t*d i j)

omit [DecidableEq ι] in
theorem expEnergy_deriv (d : ι → ι → ℝ) (w : ι → ℝ) :
    HasDerivAt (expEnergy d w) (-AnchoredCovariance.energy d w) 0 := by
  have ht (i j : ι) : HasDerivAt
      (fun t : ℝ => w i * w j * Real.exp (-t*d i j))
      (-(w i*w j*d i j)) 0 := by
    have hl : HasDerivAt (fun t : ℝ => -t*d i j) (-(d i j)) 0 := by
      convert (hasDerivAt_id (0:ℝ)).neg.mul_const (d i j) using 1
      · funext t; simp [id]
      · ring
    convert ((Real.hasDerivAt_exp (-(0:ℝ)*d i j)).comp 0 hl).const_mul (w i*w j) using 1 <;>
      simp
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht i j))
  change HasDerivAt (fun t : ℝ => ∑ i, ∑ j, w i*w j*Real.exp (-t*d i j))
    (-∑ i, ∑ j, w i*w j*d i j) 0
  simpa only [Finset.sum_neg_distrib] using h

omit [DecidableEq ι] in
theorem expEnergy_zero (d : ι → ι → ℝ) (w : ι → ℝ)
    (hw : ∑ i, w i = 0) : expEnergy d w 0 = 0 := by
  calc
    expEnergy d w 0 = (∑ i, w i) * (∑ j, w j) := by
      simp only [expEnergy,zero_mul,neg_zero,Real.exp_zero,mul_one]
      change (∑ i, ∑ j, w i * w j) = _
      exact (Fintype.sum_mul_sum w w).symm
    _ = 0 := by rw [hw]; ring

theorem heat_positive_negative (ψ : Wave → ℝ)
    (hp : HeatPositiveSymbol ψ) : NegativeSymbol ψ := by
  intro ι _ _ k c hc
  let d : ι → ι → ℝ := fun i j => ψ (k j-k i)
  have hz := expEnergy_zero d c hc
  have hlim := (expEnergy_deriv d c).tendsto_slope_zero_right
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),
      0 ≤ t⁻¹ * expEnergy d c t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hP := hp ι k t ht.le
    have hQ : 0 ≤ expEnergy d c t := by
      simpa only [expEnergy,d,dotProduct,Matrix.mulVec,Pi.star_apply,
        star_trivial,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using
        hP.dotProduct_mulVec_nonneg c
    exact mul_nonneg (inv_nonneg.mpr ht.le) hQ
  have hderiv : 0 ≤ -AnchoredCovariance.energy d c := by
    apply ge_of_tendsto hlim
    simpa [hz] using hev
  change AnchoredCovariance.energy d c ≤ 0
  linarith

theorem heat_positive_iff_negative (ψ : Wave → ℝ)
    (h0 : ψ 0 = 0) (he : ∀ k, ψ (-k) = ψ k) :
    HeatPositiveSymbol ψ ↔ NegativeSymbol ψ := by
  constructor
  · exact heat_positive_negative ψ
  · intro h ι _ _ k t ht
    exact heat_multiplier_psd_of_negative ψ h0 he h t ht k

theorem heat_positive_iff_covariance (ψ : Wave → ℝ)
    (h0 : ψ 0 = 0) (he : ∀ k, ψ (-k) = ψ k) :
    HeatPositiveSymbol ψ ↔ CovarianceSymbol ψ := by
  exact (heat_positive_iff_negative ψ h0 he).trans
    (FourierCovarianceCriterion.symbol_iff ψ h0 he).symm

theorem anisotropic_heat_positive_iff_active (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) :
    HeatPositiveSymbol (AnisotropicStableGamma.anisotropicSymbol a γ) ↔
      ∀ j, 0 < a j → γ j ≤ 2 := by
  exact (heat_positive_iff_negative _
    (AnisotropicStableGamma.anisotropic_zero a γ hγ0)
    (AnisotropicStableGamma.anisotropic_even a γ)).trans
      (AnisotropicMixedThreshold.anisotropic_negative_iff_active a γ ha hγ0)

end OperatorDerivativeRewrite.Foundation.FiniteSchoenberg
