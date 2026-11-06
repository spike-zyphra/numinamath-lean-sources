import Mathlib

/- define s -/
abbrev s' : ℕ → ℕ
  | 0       => 4
  | n + 1   => s' n ^ 2 - 2

/- define Lucas Lehmer test -/
abbrev Lucas_Lehmer_test (p : ℕ) : Prop :=
  s' (p - 2) % (2 ^ p - 1) = 0

/-
Use the Lucas-Lehmer test to determine whether the following Mersenne numbers are prime:
a) $ M_{3} $
-/
theorem number_theory_4926_1 : Lucas_Lehmer_test 3 = True := by native_decide

/-
Use the Lucas-Lehmer test to determine whether the following Mersenne numbers are prime:
b) $ M_{7} $
-/
theorem number_theory_4926_2 : Lucas_Lehmer_test 7 = True := by native_decide

/-
Use the Lucas-Lehmer test to determine whether the following Mersenne numbers are prime:
c) $ M_{11} $
-/
theorem number_theory_4926_3 : Lucas_Lehmer_test 11 = False := by native_decide

/-
Use the Lucas-Lehmer test to determine whether the following Mersenne numbers are prime:
d) $ M_{13} $
-/
theorem number_theory_4926_4 : Lucas_Lehmer_test 13 = True := by native_decide
