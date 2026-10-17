import Foundation.OneSidedGapCertificate

/-! A certified quantitative lower bound on the actual physical local energy. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedPhysicalGap
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedGramSector
  OneSidedGapCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def delta : ℝ := 6893/10000

def Lreal : Matrix Interior (Fin 32) ℝ := fun e k => (Ldata (number e) k : ℝ)

def Dreal : Matrix (Fin 32) (Fin 32) ℝ := Matrix.diagonal (fun k => (Ddata k : ℝ))

def corrected : Matrix Interior Interior ℝ :=
  gram-(6893/10000 : ℝ) • 1+(6893/40000 : ℝ) • Matrix.vecMulVec gauge gauge

theorem corrected_entry (e f : Interior) : corrected e f=
    ∑ k : Fin 32, Lreal e k*(Ddata k : ℝ)*Lreal f k := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (rational_identity (number e) (number f))
  push_cast at h
  simp only [apply_ite,Rat.cast_one,Rat.cast_zero] at h
  simp only [← gram_entry_Cdata,gauge_real,point_number,number_injective.eq_iff] at h
  simpa only [corrected,Lreal,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
    Matrix.one_apply,Matrix.vecMulVec_apply,smul_eq_mul,mul_ite,sub_ite,mul_assoc] using h
theorem corrected_factor : corrected=Lreal*Dreal*Lreal.transpose := by
  ext e f
  rw [corrected_entry]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Dreal,Matrix.diagonal,
    Matrix.of_apply,ite_mul,mul_ite,zero_mul,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]

theorem corrected_nonnegative (f : Field) : 0≤dotProduct f (corrected.mulVec f) := by
  rw [corrected_factor,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  have he (y : Fin 32 → ℝ) : dotProduct f (Lreal.mulVec y)=
      dotProduct y (Lreal.transpose.mulVec f) := by
    simpa only [Matrix.transpose_transpose] using
      Matrix.dotProduct_transpose_mulVec Lreal.transpose f y
  rw [he]
  simp only [Dreal,Matrix.mulVec_diagonal,Pi.mul_apply,dotProduct]
  apply Finset.sum_nonneg
  intro k _
  have hd : 0≤(Ddata k : ℝ) := by exact_mod_cast pivots_nonnegative k
  simpa only [pow_two,mul_assoc] using
    mul_nonneg hd (sq_nonneg (Lreal.transpose.mulVec f k))

theorem outer_quadratic (f : Field) :
    dotProduct f ((Matrix.vecMulVec gauge gauge).mulVec f)=(dotProduct f gauge)^2 := by
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_vecMulVec,smul_dotProduct,smul_eq_mul,
    dotProduct_comm gauge f]
  ring

theorem corrected_quadratic (f : Field) : dotProduct f (corrected.mulVec f)=
    realEnergy (extend f)-delta*dotProduct f f+(delta/4)*(dotProduct f gauge)^2 := by
  rw [corrected,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,
    Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_add,dotProduct_sub,
    dotProduct_smul,dotProduct_smul,gram_energy,outer_quadratic]
  norm_num [delta,smul_eq_mul]

theorem physical_pairing (f : Field) (hf : OrthogonalToGauge (extend f)) : dotProduct f gauge=0 := by
  have hs : (∑ e∈edges, extend f e*originField e)=dotProduct f gauge := by
    have h := Finset.sum_subtype (F := (inferInstance : Fintype Interior)) (p := fun e : EdgeData => e∈edges) edges
      (fun _ => Iff.rfl) (fun e => extend f e*originField e)
    simpa only [dotProduct,OneSidedBlockRank.gauge,extend_on] using h
  change (∑ e∈edges, extend f e*originField e)=0 at hf
  rw [hs] at hf
  exact hf

theorem projected_energy_lower_bound (f : Field) :
    delta*dotProduct f f-(delta/4)*(dotProduct f gauge)^2≤realEnergy (extend f) := by
  have h := corrected_nonnegative f
  rw [corrected_quadratic] at h
  linarith

theorem physical_energy_lower_bound (f : Field) (hf : OrthogonalToGauge (extend f)) :
    (6893/10000 : ℝ)*(∑ e : Interior, (f e)^2)≤realEnergy (extend f) := by
  have h := projected_energy_lower_bound f
  rw [physical_pairing f hf] at h
  simpa only [delta,dotProduct,pow_two,zero_mul,mul_zero,sub_zero] using h

theorem delta_positive : 0<delta := by norm_num [delta]

end OperatorDerivativeRewrite.Foundation.OneSidedPhysicalGap
