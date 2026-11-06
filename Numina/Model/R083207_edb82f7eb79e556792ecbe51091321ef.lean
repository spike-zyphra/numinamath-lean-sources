import Mathlib

theorem number_theory_97411 (T M H : ℕ) (h : Nat.factorial 19 = 121600400 + 1000000 * T + 100000 * M + 10000 * H) :
    T + M + H = 12 := by
  norm_num [Nat.factorial] at h 
  omega