import Mathlib

theorem number_theory_244076 (x y : ℕ) (h : Nat.factorial 26 = 40329100000000000 * 10000000000 + 1000000000 * x + 100000000 * y) :
    x = 4 ∧ y = 0 := by 
  norm_num [Nat.factorial] at h  -- Compute the value of Nat.factorial 26 and simplify h
  have hx : x = 4 := by
    omega
  have hy : y = 0 := by
    omega
  exact ⟨hx, hy⟩
  all_goals
    omega