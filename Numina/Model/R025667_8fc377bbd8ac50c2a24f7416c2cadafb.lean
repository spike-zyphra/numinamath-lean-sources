import Mathlib

theorem number_theory_195097 (n : ℕ) (h₀ : n > 0) (h₁ : (n + 1)^2 - 9 = (n + 2)^2 - 7) :
    (n + 1)^2 - 9 = 105 := by 
  have h4 : 2 * n + 5 = 0 := by 
    have eq1 : (n + 1 : ℕ) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have eq2 : (n + 2 : ℕ) ^ 2 = n ^ 2 + 4 * n + 4 := by ring
    have eq3 : (n + 1 : ℕ) ^ 2 - 9 = n ^ 2 + 2 * n + 1 - 9 := by 
      rw [eq1]
    have eq4 : (n + 2 : ℕ) ^ 2 - 7 = n ^ 2 + 4 * n + 4 - 7 := by 
      rw [eq2]
    rw [eq3, eq4] at h₁
    omega 
  have h5 : False := by 
    omega 
  contradiction