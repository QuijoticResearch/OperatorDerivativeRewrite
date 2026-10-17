import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-! Polynomial diagonal intertwining preserves coordinate-zero moments even at zero couplings. -/
noncomputable section
open Matrix
namespace OperatorDerivativeRewrite.Foundation.TridiagonalMomentIntertwining

def symmetric (a b c f r s e h : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,r,0,0,0; r,a,s,0,0; 0,s,b,e,0; 0,0,e,c,h; 0,0,0,h,f]

def monic (a b c f u v w z : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,1,0,0,0; u,a,1,0,0; 0,v,b,1,0; 0,0,w,c,1; 0,0,0,z,f]

def weights (r s e h : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.diagonal ![1,r,r*s,r*s*e,r*s*e*h]

theorem intertwine (a b c f r s e h : ℝ) :
    weights r s e h*symmetric a b c f r s e h =
      monic a b c f (r^2) (s^2) (e^2) (h^2)*weights r s e h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weights,symmetric,monic,Matrix.diagonal_mul,Matrix.mul_diagonal] <;> ring

theorem power_intertwine (a b c f r s e h : ℝ) (n : ℕ) :
    weights r s e h*(symmetric a b c f r s e h)^n =
      (monic a b c f (r^2) (s^2) (e^2) (h^2))^n*weights r s e h := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,pow_succ,← mul_assoc,ih,mul_assoc,intertwine,← mul_assoc]

theorem coordinate_moment (a b c f r s e h : ℝ) (n : ℕ) :
    ((symmetric a b c f r s e h)^n) 0 0 =
      ((monic a b c f (r^2) (s^2) (e^2) (h^2))^n) 0 0 := by
  have he := congrArg (fun A : Matrix (Fin 5) (Fin 5) ℝ => A 0 0)
    (power_intertwine a b c f r s e h n)
  simpa [weights,Matrix.diagonal_mul,Matrix.mul_diagonal] using he

end OperatorDerivativeRewrite.Foundation.TridiagonalMomentIntertwining
