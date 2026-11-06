import Mathlib

theorem number_theory_195187 {n : ℕ} (h : n * (n + 1) = 420) :
    n + (n + 1) = 41 := by
  have h2 : n = 20 := by
    nlinarith
  calc
    n + (n + 1) = 20 + (20 + 1) := by rw [h2]
    _ = 41 := by norm_num