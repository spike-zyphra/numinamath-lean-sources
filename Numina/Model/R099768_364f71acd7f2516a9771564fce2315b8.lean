import Mathlib

theorem number_theory_56831 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : Nat.factorial 17 = 355687000000 + 100 * a + 10 * b + 809600) :
    10 * a + b = 75 := by
  norm_num [Nat.factorial] at h 
  omega