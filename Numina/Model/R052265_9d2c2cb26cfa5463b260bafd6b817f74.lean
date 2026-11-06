import Mathlib

theorem number_theory_197125 {n : ℕ} (h : ¬ 3 ∣ n) : 3 ∣ (n^2 - 1) := by 
  have h1 : n % 3 = 1 ∨ n % 3 = 2 := by 
    omega 
  rcases h1 with (h1 | h1)
  · -- Case where n % 3 = 1 
    have h2 : (n ^ 2) % 3 = 1 := by 
      simp [Nat.pow_mod, h1]
    omega 
  · -- Case where n % 3 = 2 
    have h2 : (n ^ 2) % 3 = 1 := by 
      simp [Nat.pow_mod, h1]
    omega