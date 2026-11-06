import Mathlib

theorem number_theory_23372 {n : ℕ} (h : n % 7 = 5) : (5 * n) % 7 = 4 := by 
  have h1 : n % 7 = 5 := h
  calc
    (5 * n) % 7 = (5 * (n % 7)) % 7 := by simp [Nat.mul_mod]
    _ = (5 * 5) % 7 := by rw [h1]
    _ = 25 % 7 := by norm_num
    _ = 4 := by norm_num