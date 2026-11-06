import Mathlib

theorem number_theory_233023 : ¬ ∃ n, (425102348541 : ℕ) = n ^ 2 := by
  rintro ⟨n, hn⟩
  have h1 : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
    have h2 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
      simp [pow_two, Nat.mul_mod, h2] 
  have h2 : n ^ 2 = 425102348541 := by linarith
  have h3 : n ^ 2 % 8 = 5 := by
    omega 
  omega