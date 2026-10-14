import Foundation.GaussianConditionalFullGraphs
import Foundation.GaussianPotentialPredictionRank
import Foundation.GaussianBrownianPRP

/-! Exact Hodge geometry between causal Ito fields and canonical minimum-norm recovery. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianItoSourceHodge
open InfiniteGaussian GaussianNumberSectors GaussianDivergenceRecovery GaussianSourceHodge
open GaussianQuadraticSourceHodge GaussianInverseNumberPotential GaussianPotentialPredictionRank
open GaussianPredictableFull GaussianPredictableAdjoint GaussianBrownianPRP
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem ito_gradientProjection (u : fullPredictable) :
    gradientProjection (predictableField u)=recovery (itoIntegral u) :=
  (recovery_divergence_gradientProjection _ _ (predictableField_divergence_graph u)).symm

theorem ito_recovery_residual_graph (u : fullPredictable) :
    (predictableField u-recovery (itoIntegral u),0)∈hilbertDivergence.graph := by
  rw [← ito_gradientProjection]
  exact residual_divergence_zero _

theorem ito_recovery_energy (u : fullPredictable) :
    ‖u‖^2=‖recovery (itoIntegral u)‖^2+‖predictableField u-recovery (itoIntegral u)‖^2 := by
  have ho := recovery_orthogonal_kernel (itoIntegral u) _ (ito_recovery_residual_graph u)
  rw [inner_sub_left,real_inner_self_eq_norm_sq] at ho
  have he := norm_sub_sq_real (predictableField u) (recovery (itoIntegral u))
  rw [predictableField.norm_map] at he
  nlinarith

theorem recovery_sector_energy (n : ℕ) (f : sector n) :
    ‖recovery f‖^2=(n : ℝ)⁻¹*‖(f : GaussianL2)‖^2 := by
  have hs : HasSum (fun m : ℕ => (m : ℝ)⁻¹*‖projection m f‖^2)
      ((n : ℝ)⁻¹*‖projection n f‖^2) := by
    apply hasSum_single n
    intro m hmn
    rw [projection_of_sector f,if_neg hmn,norm_zero,zero_pow (by omega),mul_zero]
  have he := (recovery_inverse_energy_hasSum f).unique hs
  simpa only [projection_fix] using he

theorem ito_sector_residual_energy (u : fullPredictable) (n : ℕ)
    (hn : itoIntegral u∈sector n) :
    ‖predictableField u-recovery (itoIntegral u)‖^2=(1-(n : ℝ)⁻¹)*‖u‖^2 := by
  have hr := recovery_sector_energy n ⟨itoIntegral u,hn⟩
  rw [itoIntegral.norm_map] at hr
  have he := ito_recovery_energy u
  linarith

theorem predictable_recovery_potential (f : GaussianL2) :
    predictableProjection (recovery f)=predictableAdjoint (potentialOperator f) := by
  obtain ⟨g,hg,hv⟩ := closedCylindricalDerivative.mem_graph_iff.mp (potential_derivative_graph f)
  have he := predictableAdjoint_eq_projected_derivative g
  change predictableAdjoint (g : GaussianL2)=predictableProjection (closedCylindricalDerivative g) at he
  rw [hg,hv] at he
  exact he.symm

theorem predictable_recovery_sector (n : ℕ) (f : sector n) :
    predictableProjection (recovery f)=(n : ℝ)⁻¹ • predictableAdjoint f := by
  rw [predictable_recovery_potential,potential_sector,map_smul]

theorem alternating_projection_sector (u : fullPredictable) (n : ℕ)
    (hn : itoIntegral u∈sector n) :
    predictableProjection (gradientProjection (predictableField u))=(n : ℝ)⁻¹ • u := by
  rw [ito_gradientProjection]
  have he := predictable_recovery_sector n ⟨itoIntegral u,hn⟩
  simpa only [predictableAdjoint_integral] using he

theorem pure_mode_causal_minimum_gap (u : fullPredictable) (n : ℕ) (hn : 1<n)
    (hmode : itoIntegral u∈sector n) (hu : u≠0) :
    ‖recovery (itoIntegral u)‖<‖predictableField u‖ := by
  have he := recovery_sector_energy n ⟨itoIntegral u,hmode⟩
  rw [itoIntegral.norm_map] at he
  have hpow : 0<‖u‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
  have hinv : (n : ℝ)⁻¹<1 := (inv_lt_one₀ (by exact_mod_cast (show 0<n by omega))).mpr (by exact_mod_cast hn)
  rw [predictableField.norm_map]
  nlinarith [norm_nonneg (recovery (itoIntegral u)),norm_nonneg u]

def terminalWickIntegrand (n : ℕ) (T : ℝ≥0) : fullPredictable :=
  (n+1 : ℝ) • GaussianHermiteRepresentation.hermiteIntegrand n T

theorem terminalWickIntegrand_integral (n : ℕ) (T : ℝ≥0) :
    itoIntegral (terminalWickIntegrand n T)=(GaussianTimeSpaceHermite.brownianCore T (n+1) : GaussianL2) := by
  rw [terminalWickIntegrand,map_smul]
  exact (GaussianHermiteRepresentation.hermite_representation n T).symm

theorem terminalWickIntegrand_energy (n : ℕ) (T : ℝ≥0) :
    ‖terminalWickIntegrand n T‖^2=((n+1).factorial : ℝ)*(T : ℝ)^(n+1) := by
  rw [← itoIntegral.norm_map (terminalWickIntegrand n T),terminalWickIntegrand_integral,
    GaussianTimeSpaceHermite.brownianCore_norm_sq]

theorem terminalWick_residual_energy (n : ℕ) (T : ℝ≥0) :
    ‖predictableField (terminalWickIntegrand n T)-recovery (itoIntegral (terminalWickIntegrand n T))‖^2=
      (1-(n+1 : ℝ)⁻¹)*((n+1).factorial : ℝ)*(T : ℝ)^(n+1) := by
  have hm : itoIntegral (terminalWickIntegrand n T)∈sector (n+1) := by
    rw [terminalWickIntegrand_integral]
    exact IBMCubicFirstChaos.wick_mem_sector _ _
  rw [ito_sector_residual_energy _ (n+1) hm,terminalWickIntegrand_energy,mul_assoc]
  simp only [Nat.cast_add,Nat.cast_one]

theorem quadratic_causal_residual_energy (T : ℝ≥0) :
    ‖predictableField (terminalWickIntegrand 1 T)-recovery (itoIntegral (terminalWickIntegrand 1 T))‖^2=
      (T : ℝ)^2 := by
  rw [terminalWick_residual_energy]
  norm_num

end OperatorDerivativeRewrite.Foundation.GaussianItoSourceHodge
