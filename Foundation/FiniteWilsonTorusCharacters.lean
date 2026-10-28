import Foundation.FiniteWilsonTorusProbe

/-! Complete finite character certificates for the already realized kinetic
operator. Integer identities are checked in Lean, without numerical eigenvectors
or enlarged verification resource settings. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusCharacters
open FiniteWilsonTorusKernel

private def bitSign (a i : State) (k : ℕ) : ℤ :=
  if a.val.testBit k && i.val.testBit k then -1 else 1

def characterZ (a i : State) : ℤ :=
  bitSign a i 0*bitSign a i 1*bitSign a i 2*bitSign a i 3*bitSign a i 4

def character (a i : State) : ℝ := (characterZ a i:ℝ)

def eigenNumerator : State → ℤ := ![65536,4096,4096,4096,4096,4096,256,4096,16384,4096,4096,1024,4096,16384,1024,4096,16384,4096,4096,16384,4096,1024,1024,4096,4096,4096,4096,4096,4096,4096,4096,4096]

private theorem gram_row_0 : ∀ j : State,
    (∑ a : State,characterZ a 0*characterZ a j)=if (0:State)=j then 32 else 0 := by decide

private theorem gram_row_1 : ∀ j : State,
    (∑ a : State,characterZ a 1*characterZ a j)=if (1:State)=j then 32 else 0 := by decide

private theorem gram_row_2 : ∀ j : State,
    (∑ a : State,characterZ a 2*characterZ a j)=if (2:State)=j then 32 else 0 := by decide

private theorem gram_row_3 : ∀ j : State,
    (∑ a : State,characterZ a 3*characterZ a j)=if (3:State)=j then 32 else 0 := by decide

private theorem gram_row_4 : ∀ j : State,
    (∑ a : State,characterZ a 4*characterZ a j)=if (4:State)=j then 32 else 0 := by decide

private theorem gram_row_5 : ∀ j : State,
    (∑ a : State,characterZ a 5*characterZ a j)=if (5:State)=j then 32 else 0 := by decide

private theorem gram_row_6 : ∀ j : State,
    (∑ a : State,characterZ a 6*characterZ a j)=if (6:State)=j then 32 else 0 := by decide

private theorem gram_row_7 : ∀ j : State,
    (∑ a : State,characterZ a 7*characterZ a j)=if (7:State)=j then 32 else 0 := by decide

private theorem gram_row_8 : ∀ j : State,
    (∑ a : State,characterZ a 8*characterZ a j)=if (8:State)=j then 32 else 0 := by decide

private theorem gram_row_9 : ∀ j : State,
    (∑ a : State,characterZ a 9*characterZ a j)=if (9:State)=j then 32 else 0 := by decide

private theorem gram_row_10 : ∀ j : State,
    (∑ a : State,characterZ a 10*characterZ a j)=if (10:State)=j then 32 else 0 := by decide

private theorem gram_row_11 : ∀ j : State,
    (∑ a : State,characterZ a 11*characterZ a j)=if (11:State)=j then 32 else 0 := by decide

private theorem gram_row_12 : ∀ j : State,
    (∑ a : State,characterZ a 12*characterZ a j)=if (12:State)=j then 32 else 0 := by decide

private theorem gram_row_13 : ∀ j : State,
    (∑ a : State,characterZ a 13*characterZ a j)=if (13:State)=j then 32 else 0 := by decide

private theorem gram_row_14 : ∀ j : State,
    (∑ a : State,characterZ a 14*characterZ a j)=if (14:State)=j then 32 else 0 := by decide

private theorem gram_row_15 : ∀ j : State,
    (∑ a : State,characterZ a 15*characterZ a j)=if (15:State)=j then 32 else 0 := by decide

private theorem gram_row_16 : ∀ j : State,
    (∑ a : State,characterZ a 16*characterZ a j)=if (16:State)=j then 32 else 0 := by decide

private theorem gram_row_17 : ∀ j : State,
    (∑ a : State,characterZ a 17*characterZ a j)=if (17:State)=j then 32 else 0 := by decide

private theorem gram_row_18 : ∀ j : State,
    (∑ a : State,characterZ a 18*characterZ a j)=if (18:State)=j then 32 else 0 := by decide

private theorem gram_row_19 : ∀ j : State,
    (∑ a : State,characterZ a 19*characterZ a j)=if (19:State)=j then 32 else 0 := by decide

private theorem gram_row_20 : ∀ j : State,
    (∑ a : State,characterZ a 20*characterZ a j)=if (20:State)=j then 32 else 0 := by decide

private theorem gram_row_21 : ∀ j : State,
    (∑ a : State,characterZ a 21*characterZ a j)=if (21:State)=j then 32 else 0 := by decide

private theorem gram_row_22 : ∀ j : State,
    (∑ a : State,characterZ a 22*characterZ a j)=if (22:State)=j then 32 else 0 := by decide

private theorem gram_row_23 : ∀ j : State,
    (∑ a : State,characterZ a 23*characterZ a j)=if (23:State)=j then 32 else 0 := by decide

private theorem gram_row_24 : ∀ j : State,
    (∑ a : State,characterZ a 24*characterZ a j)=if (24:State)=j then 32 else 0 := by decide

private theorem gram_row_25 : ∀ j : State,
    (∑ a : State,characterZ a 25*characterZ a j)=if (25:State)=j then 32 else 0 := by decide

private theorem gram_row_26 : ∀ j : State,
    (∑ a : State,characterZ a 26*characterZ a j)=if (26:State)=j then 32 else 0 := by decide

private theorem gram_row_27 : ∀ j : State,
    (∑ a : State,characterZ a 27*characterZ a j)=if (27:State)=j then 32 else 0 := by decide

private theorem gram_row_28 : ∀ j : State,
    (∑ a : State,characterZ a 28*characterZ a j)=if (28:State)=j then 32 else 0 := by decide

private theorem gram_row_29 : ∀ j : State,
    (∑ a : State,characterZ a 29*characterZ a j)=if (29:State)=j then 32 else 0 := by decide

private theorem gram_row_30 : ∀ j : State,
    (∑ a : State,characterZ a 30*characterZ a j)=if (30:State)=j then 32 else 0 := by decide

private theorem gram_row_31 : ∀ j : State,
    (∑ a : State,characterZ a 31*characterZ a j)=if (31:State)=j then 32 else 0 := by decide

theorem integer_gram (i j : State) :
    (∑ a : State,characterZ a i*characterZ a j)=if i=j then 32 else 0 := by
  fin_cases i
  · exact gram_row_0 j
  · exact gram_row_1 j
  · exact gram_row_2 j
  · exact gram_row_3 j
  · exact gram_row_4 j
  · exact gram_row_5 j
  · exact gram_row_6 j
  · exact gram_row_7 j
  · exact gram_row_8 j
  · exact gram_row_9 j
  · exact gram_row_10 j
  · exact gram_row_11 j
  · exact gram_row_12 j
  · exact gram_row_13 j
  · exact gram_row_14 j
  · exact gram_row_15 j
  · exact gram_row_16 j
  · exact gram_row_17 j
  · exact gram_row_18 j
  · exact gram_row_19 j
  · exact gram_row_20 j
  · exact gram_row_21 j
  · exact gram_row_22 j
  · exact gram_row_23 j
  · exact gram_row_24 j
  · exact gram_row_25 j
  · exact gram_row_26 j
  · exact gram_row_27 j
  · exact gram_row_28 j
  · exact gram_row_29 j
  · exact gram_row_30 j
  · exact gram_row_31 j

private theorem kinetic_row_0 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 0*characterZ a j)=32*(count (difference 0 j):ℤ) := by decide

private theorem kinetic_row_1 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 1*characterZ a j)=32*(count (difference 1 j):ℤ) := by decide

private theorem kinetic_row_2 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 2*characterZ a j)=32*(count (difference 2 j):ℤ) := by decide

private theorem kinetic_row_3 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 3*characterZ a j)=32*(count (difference 3 j):ℤ) := by decide

private theorem kinetic_row_4 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 4*characterZ a j)=32*(count (difference 4 j):ℤ) := by decide

private theorem kinetic_row_5 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 5*characterZ a j)=32*(count (difference 5 j):ℤ) := by decide

private theorem kinetic_row_6 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 6*characterZ a j)=32*(count (difference 6 j):ℤ) := by decide

private theorem kinetic_row_7 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 7*characterZ a j)=32*(count (difference 7 j):ℤ) := by decide

private theorem kinetic_row_8 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 8*characterZ a j)=32*(count (difference 8 j):ℤ) := by decide

private theorem kinetic_row_9 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 9*characterZ a j)=32*(count (difference 9 j):ℤ) := by decide

private theorem kinetic_row_10 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 10*characterZ a j)=32*(count (difference 10 j):ℤ) := by decide

private theorem kinetic_row_11 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 11*characterZ a j)=32*(count (difference 11 j):ℤ) := by decide

private theorem kinetic_row_12 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 12*characterZ a j)=32*(count (difference 12 j):ℤ) := by decide

private theorem kinetic_row_13 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 13*characterZ a j)=32*(count (difference 13 j):ℤ) := by decide

private theorem kinetic_row_14 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 14*characterZ a j)=32*(count (difference 14 j):ℤ) := by decide

private theorem kinetic_row_15 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 15*characterZ a j)=32*(count (difference 15 j):ℤ) := by decide

private theorem kinetic_row_16 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 16*characterZ a j)=32*(count (difference 16 j):ℤ) := by decide

private theorem kinetic_row_17 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 17*characterZ a j)=32*(count (difference 17 j):ℤ) := by decide

private theorem kinetic_row_18 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 18*characterZ a j)=32*(count (difference 18 j):ℤ) := by decide

private theorem kinetic_row_19 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 19*characterZ a j)=32*(count (difference 19 j):ℤ) := by decide

private theorem kinetic_row_20 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 20*characterZ a j)=32*(count (difference 20 j):ℤ) := by decide

private theorem kinetic_row_21 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 21*characterZ a j)=32*(count (difference 21 j):ℤ) := by decide

private theorem kinetic_row_22 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 22*characterZ a j)=32*(count (difference 22 j):ℤ) := by decide

private theorem kinetic_row_23 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 23*characterZ a j)=32*(count (difference 23 j):ℤ) := by decide

private theorem kinetic_row_24 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 24*characterZ a j)=32*(count (difference 24 j):ℤ) := by decide

private theorem kinetic_row_25 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 25*characterZ a j)=32*(count (difference 25 j):ℤ) := by decide

private theorem kinetic_row_26 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 26*characterZ a j)=32*(count (difference 26 j):ℤ) := by decide

private theorem kinetic_row_27 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 27*characterZ a j)=32*(count (difference 27 j):ℤ) := by decide

private theorem kinetic_row_28 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 28*characterZ a j)=32*(count (difference 28 j):ℤ) := by decide

private theorem kinetic_row_29 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 29*characterZ a j)=32*(count (difference 29 j):ℤ) := by decide

private theorem kinetic_row_30 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 30*characterZ a j)=32*(count (difference 30 j):ℤ) := by decide

private theorem kinetic_row_31 : ∀ j : State,
    (∑ a : State,eigenNumerator a*characterZ a 31*characterZ a j)=32*(count (difference 31 j):ℤ) := by decide

theorem integer_kinetic (i j : State) :
    (∑ a : State,eigenNumerator a*characterZ a i*characterZ a j)=32*(count (difference i j):ℤ) := by
  fin_cases i
  · exact kinetic_row_0 j
  · exact kinetic_row_1 j
  · exact kinetic_row_2 j
  · exact kinetic_row_3 j
  · exact kinetic_row_4 j
  · exact kinetic_row_5 j
  · exact kinetic_row_6 j
  · exact kinetic_row_7 j
  · exact kinetic_row_8 j
  · exact kinetic_row_9 j
  · exact kinetic_row_10 j
  · exact kinetic_row_11 j
  · exact kinetic_row_12 j
  · exact kinetic_row_13 j
  · exact kinetic_row_14 j
  · exact kinetic_row_15 j
  · exact kinetic_row_16 j
  · exact kinetic_row_17 j
  · exact kinetic_row_18 j
  · exact kinetic_row_19 j
  · exact kinetic_row_20 j
  · exact kinetic_row_21 j
  · exact kinetic_row_22 j
  · exact kinetic_row_23 j
  · exact kinetic_row_24 j
  · exact kinetic_row_25 j
  · exact kinetic_row_26 j
  · exact kinetic_row_27 j
  · exact kinetic_row_28 j
  · exact kinetic_row_29 j
  · exact kinetic_row_30 j
  · exact kinetic_row_31 j

theorem gram (i j : State) :
    (∑ a : State,character a i*character a j)=if i=j then 32 else 0 := by
  simp only [character]
  exact_mod_cast integer_gram i j

theorem kinetic_fourier (i j : State) :
    (∑ a : State,(eigenNumerator a:ℝ)*character a i*character a j)=2097152*kinetic i j := by
  have h : (∑ a : State,(eigenNumerator a:ℝ)*character a i*character a j)=
      32*(count (difference i j):ℝ) := by
    simp only [character]
    exact_mod_cast integer_kinetic i j
  rw [h]
  unfold kinetic
  ring

theorem character_symmetric (a i : State) : character a i=character i a := by
  have hb (k : ℕ) : bitSign a i k=bitSign i a k := by simp [bitSign,Bool.and_comm]
  simp [character,characterZ,hb]

theorem character_zero (i : State) : character 0 i=1 := by
  simp [character,characterZ,bitSign]

theorem nonconstant_numerator_bound (a : State) (ha : a ≠ 0) : (eigenNumerator a:ℝ) ≤ 16384 := by
  fin_cases a <;> norm_num [eigenNumerator] at *

end OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusCharacters
