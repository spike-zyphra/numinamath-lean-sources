import Mathlib

theorem number_theory_274350 (x y : ℤ) :
    x * (x + 1) ≠ 2 * (5 * y + 2) := by
  intro h
  have h1 : x * (x + 1) % 5 = 0 ∨ x * (x + 1) % 5 = 1 ∨ x * (x + 1) % 5 = 2 := by
    have h1 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> simp [h1, Int.add_emod, Int.mul_emod]
  have h2 : x * (x + 1) % 5 = 4 := by
    have h3 : x * (x + 1) = 2 * (5 * y + 2) := by
      exact h
    omega
  omega