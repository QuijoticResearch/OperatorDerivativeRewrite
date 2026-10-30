import Foundation.CubeRootSchur

/-! Simultaneous kinetic/spatial coordinates for the actual finite-cube Schur form. -/
noncomputable section
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianModes
open CubeTemporalSchur CubeChartAction CubeRootSchur SU2HemisphereJets
open SU2GaussianConeCoordinates QuaternionSU2Representation

def basis : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-1,1/2,0,1,1/2;
      1,1/2,0,1,-1/2;
      0,1,0,0,1;
      0,0,1,0,-1;
      0,0,1,0,1]

def weights : Fin 5 → ℝ := ![1,1/4,1/2,2/3,1/2]
def orders : Fin 5 → ℝ := ![4,4,4,6,6]

private def actualK : Matrix (Fin 5) (Fin 5) ℚ :=
  !![5/12,-1/12,-1/6,1/24,-1/24;
     -1/12,5/12,-1/6,-5/24,5/24;
     -1/6,-1/6,5/12,5/24,-5/24;
     1/24,-5/24,5/24,5/12,-1/6;
     -1/24,5/24,-5/24,-1/6,5/12]

private def actualH : Matrix (Fin 5) (Fin 5) ℚ :=
  !![2,0,-1,0,0;0,2,-1,-1,1;-1,-1,2,1,-1;0,-1,1,2,-1;0,1,-1,-1,2]

theorem kinetic_congruence : basis.transpose*kinetic*basis=Matrix.diagonal weights := by
  have hk : kinetic=actualK.map (Rat.castHom ℝ) := by rfl
  rw [hk]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis,actualK,weights,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.diagonal_apply,Matrix.map_apply,Fin.sum_univ_succ]

theorem spatial_congruence :
    basis.transpose*spatial*basis=Matrix.diagonal (fun i => weights i*orders i) := by
  have hh : spatial=actualH.map (Rat.castHom ℝ) := by rfl
  rw [hh]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis,actualH,weights,orders,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.diagonal_apply,Matrix.map_apply,Fin.sum_univ_succ]

def synthesis (x : Boundary) : Boundary := fun i => ∑ j,basis i j • x j

def inverseBasis : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-1/2,1/2,0,-1/4,1/4;
      0,0,1,1/2,-1/2;
      0,0,0,1/2,1/2;
      1/2,1/2,-1/2,-1/4,1/4;
      0,0,0,-1/2,1/2]

def analysis (X : Boundary) : Boundary := fun i => ∑ j,inverseBasis i j • X j

theorem synthesis_analysis (X : Boundary) : synthesis (analysis X)=X := by
  funext i a
  fin_cases i <;>
    norm_num [synthesis,analysis,basis,inverseBasis,Fin.sum_univ_succ,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul] <;> ring

theorem analysis_synthesis (x : Boundary) : analysis (synthesis x)=x := by
  funext i a
  fin_cases i <;>
    norm_num [synthesis,analysis,basis,inverseBasis,Fin.sum_univ_succ,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul] <;> ring

private theorem frame_add (x y : Triple) : frame (x+y)=frame x+frame y := by
  ext a
  fin_cases a <;> simp [frame] <;> ring

private theorem frame_sum (x : Fin 5 → Triple) : frame (∑ j,x j)=∑ j,frame (x j) := by
  simp only [Fin.sum_univ_succ,frame_add]
  simp [frame]

theorem synthesis_frame (x : Boundary) (a : Fin 3) :
    (fun i => frame (synthesis x i) a)=basis.mulVec (fun j => frame (x j) a) := by
  funext i
  simp only [synthesis,frame_sum,frame_smul,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Matrix.mulVec,dotProduct]

private theorem rotate_sum (c : SU2) (x : Fin 5 → Triple) :
    SU2RootAdjoint.rotate c (∑ j,x j)=∑ j,SU2RootAdjoint.rotate c (x j) := by
  simp only [Fin.sum_univ_succ,SU2RootAdjoint.rotate_add]
  have hz : SU2RootAdjoint.rotate c 0=0 := by
    have h := SU2RootAdjoint.rotate_smul c 0 (0:Triple)
    simpa only [zero_smul] using h
  simp [hz]

theorem synthesis_rotate (c : SU2) (x : Boundary) (i : Fin 5) :
    SU2RootAdjoint.rotate c (synthesis x i)=
      synthesis (fun j => SU2RootAdjoint.rotate c (x j)) i := by
  simp only [synthesis,rotate_sum,SU2RootAdjoint.rotate_smul]

private theorem quadratic_congruence (A : Matrix (Fin 5) (Fin 5) ℝ)
    (w : Fin 5 → ℝ) (h : basis.transpose*A*basis=Matrix.diagonal w) (x : Fin 5 → ℝ) :
    dotProduct (basis.mulVec x) (A.mulVec (basis.mulVec x))=∑ i,w i*(x i)^2 := by
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_mulVec,
    ← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,h]
  simp [dotProduct,Matrix.mulVec_diagonal,pow_two,mul_assoc,mul_comm,mul_left_comm]

theorem spatial_modes (x : Boundary) :
    spatialCost (synthesis x)=
      (∑ a : Fin 3,∑ i : Fin 5,weights i*orders i*(frame (x i) a)^2)/16 := by
  unfold spatialCost frameField
  simp_rw [synthesis_frame,quadratic_congruence spatial _ spatial_congruence]

theorem kinetic_modes (x y : Boundary) (c : SU2) :
    (∑ a : Fin 3,dotProduct (difference (synthesis x) (synthesis y) c a)
      (kinetic.mulVec (difference (synthesis x) (synthesis y) c a)))=
      ∑ a : Fin 3,∑ i : Fin 5,weights i*
        (frame (x i) a-frame (SU2RootAdjoint.rotate c (y i)) a)^2 := by
  have hd (a : Fin 3) : difference (synthesis x) (synthesis y) c a=
      basis.mulVec (fun i => frame (x i) a-frame (SU2RootAdjoint.rotate c (y i)) a) := by
    unfold difference frameField rotatedField
    simp_rw [synthesis_rotate]
    change (fun j => frame (synthesis x j) a-
      frame (synthesis (fun i => SU2RootAdjoint.rotate c (y i)) j) a)=_
    rw [show (fun j => frame (synthesis x j) a-
        frame (synthesis (fun i => SU2RootAdjoint.rotate c (y i)) j) a)=
        (fun j => frame (synthesis x j) a)-
          (fun j => frame (synthesis (fun i => SU2RootAdjoint.rotate c (y i)) j) a) from rfl,
      synthesis_frame,synthesis_frame,← Matrix.mulVec_sub]
    rfl
  simp_rw [hd,quadratic_congruence kinetic weights kinetic_congruence]

private theorem frame_square (x : Triple) :
    (∑ a : Fin 3,(frame x a)^2)=4*sizeSq x := by
  simp [frame,sizeSq,Fin.sum_univ_three]
  ring

private theorem frame_difference_square (x y : Triple) :
    (∑ a : Fin 3,(frame x a-frame y a)^2)=4*sizeSq (x-y) := by
  simp [frame,sizeSq,Fin.sum_univ_three]
  ring

theorem spatial_triples (x : Boundary) :
    spatialCost (synthesis x)=∑ i : Fin 5,weights i*orders i*sizeSq (x i)/4 := by
  rw [spatial_modes,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,frame_square]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem kinetic_triples (x y : Boundary) (c : SU2) :
    (∑ a : Fin 3,dotProduct (difference (synthesis x) (synthesis y) c a)
      (kinetic.mulVec (difference (synthesis x) (synthesis y) c a)))=
      ∑ i : Fin 5,4*weights i*sizeSq (x i-SU2RootAdjoint.rotate c (y i)) := by
  rw [kinetic_modes,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,frame_difference_square]
  apply Finset.sum_congr rfl
  intro i _
  ring

def channel (i : Fin 5) (x y : Triple) (c : SU2) : ℝ :=
  weights i/4*(orders i*(sizeSq x+sizeSq y)+
    2*sizeSq (x-SU2RootAdjoint.rotate c y))

/-- Exact five-channel identity for the ACTUAL Schur exponent, at every root. -/
theorem effective_channels (x y : Boundary) (c : SU2) :
    effective (synthesis x) (synthesis y) c=∑ i,channel i (x i) (y i) c := by
  unfold effective
  rw [spatial_triples,spatial_triples,kinetic_triples,Finset.sum_div]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold channel
  ring

theorem exponential_channels (x y : Boundary) (c : SU2) :
    Real.exp (-effective (synthesis x) (synthesis y) c)=
      ∏ i,Real.exp (-channel i (x i) (y i) c) := by
  rw [effective_channels,← Finset.sum_neg_distrib,Real.exp_sum]

/-- The channel has the actual rotated Gaussian cross term. -/
theorem channel_gaussian (i : Fin 5) (x y : Triple) (c : SU2) :
    channel i x y c=weights i*(orders i+2)/4*(sizeSq x+sizeSq y)-
      weights i*dotProduct x (SU2RootAdjoint.rotate c y) := by
  have hn := SU2RootAdjoint.rotate_sizeSq c y
  have hd : sizeSq (x-SU2RootAdjoint.rotate c y)=sizeSq x+
      sizeSq (SU2RootAdjoint.rotate c y)-2*dotProduct x (SU2RootAdjoint.rotate c y) := by
    simp [sizeSq,dotProduct,Fin.sum_univ_three]
    ring
  unfold channel
  rw [hd,hn]
  ring

end OperatorDerivativeRewrite.Foundation.CubeGaussianModes
