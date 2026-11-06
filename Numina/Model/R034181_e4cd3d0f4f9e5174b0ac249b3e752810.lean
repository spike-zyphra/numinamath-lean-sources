import Mathlib

theorem number_theory_81079 {n : ℕ} (h : 3 * n = 999 ^ 1000) :
    n % 10 = 7 := by 
  have h1 : n % 10 = 7 := by
    have h2 : (3 * n) % 10 = 1 := by
      have h3 : (3 * n) % 10 = 999 ^ 1000 % 10 := by 
        omega
      rw [h3]
      norm_num
    omega
  exact h1