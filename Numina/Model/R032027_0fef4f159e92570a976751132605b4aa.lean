import Mathlib

open Nat

theorem number_theory_265694 (a b c d : ℕ) (ha : a < 10) (hb : b < 10)
    (hc : c < 10) (hd : d < 10)
    (h : digits 10 (Nat.factorial 34) = [0, 0, 0, 0, 0, 0, b, a, 5, 3, 4, 6, 9, 0, 6, 8, 1, 6, 7, 4, 8, 0, 4, 1, 4, 0, 6, 9, d, c, 9, 9, 7, 2, 3, 2, 5, 9, 2]) :
    a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 3 := by
  have h1 : digits 10 (Nat.factorial 34) = [0, 0, 0, 0, 0, 0, 0, 2, 5, 3, 4, 6, 9, 0, 6, 8, 1, 6, 7, 4, 8, 0, 4, 1, 4, 0, 6, 9, 3, 0, 9, 9, 7, 2, 3, 2, 5, 9, 2] := by
    native_decide
  rw [h1] at h
  norm_num at h ⊢
  all_goals
    omega