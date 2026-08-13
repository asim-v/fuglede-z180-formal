import Fuglede.Z180K12Projection36Remainders3_12
import Mathlib.Tactic

/-! Literal bridges for the twelve three-point residue counts. -/

namespace Fuglede

theorem z36_count12_0 (b : Fin 36 → Int) :
    projection36Count12 b 0 = b 0 + b 12 + b 24 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_1 (b : Fin 36 → Int) :
    projection36Count12 b 1 = b 1 + b 13 + b 25 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_2 (b : Fin 36 → Int) :
    projection36Count12 b 2 = b 2 + b 14 + b 26 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_3 (b : Fin 36 → Int) :
    projection36Count12 b 3 = b 3 + b 15 + b 27 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_4 (b : Fin 36 → Int) :
    projection36Count12 b 4 = b 4 + b 16 + b 28 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_5 (b : Fin 36 → Int) :
    projection36Count12 b 5 = b 5 + b 17 + b 29 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_6 (b : Fin 36 → Int) :
    projection36Count12 b 6 = b 6 + b 18 + b 30 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_7 (b : Fin 36 → Int) :
    projection36Count12 b 7 = b 7 + b 19 + b 31 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_8 (b : Fin 36 → Int) :
    projection36Count12 b 8 = b 8 + b 20 + b 32 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_9 (b : Fin 36 → Int) :
    projection36Count12 b 9 = b 9 + b 21 + b 33 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_10 (b : Fin 36 → Int) :
    projection36Count12 b 10 = b 10 + b 22 + b 34 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

theorem z36_count12_11 (b : Fin 36 → Int) :
    projection36Count12 b 11 = b 11 + b 23 + b 35 := by
  unfold projection36Count12
  congr 1 <;> apply congrArg b <;> apply Fin.ext <;> norm_num

#print axioms z36_count12_0
#print axioms z36_count12_11

end Fuglede
