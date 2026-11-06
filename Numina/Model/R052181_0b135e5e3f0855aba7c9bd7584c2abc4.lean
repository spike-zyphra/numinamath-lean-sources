import Mathlib

theorem number_theory_181524 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : Nat.factorial 22 = 11240007277000000 * 100 + 10 * a + b + 607680000) :
    a = 7 ∧ b = 7 := by 
  norm_num [Nat.factorial] at h 
  omega