import Mathlib

theorem algebra_313060 (A : ℤ) (h : A = 41) :
    [1, 5, 11, 19, 29, A, 55] = [1, 5, 11, 19, 29, 41, 55] := by
  rw [h]
  all_goals
    rfl