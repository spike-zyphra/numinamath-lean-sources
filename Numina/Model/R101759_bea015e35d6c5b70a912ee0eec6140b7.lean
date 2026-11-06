import Mathlib

theorem number_theory_168326 (n m : ℕ) (h₀ : n % 5 = 3) (h₁ : m % 5 = 3) :
    (n * m) % 5 = 4 := by 
  calc 
    (n * m) % 5 = ((n % 5) * (m % 5)) % 5 := by 
      simp [Nat.mul_mod]
    _ = (3 * 3) % 5 := by 
      rw [h₀, h₁]
    _ = 4 := by 
      norm_num