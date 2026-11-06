import Mathlib

theorem number_theory_126336 : ¬ ∃ x y : ℤ, x ^ 2 - 7 * y ^ 2 = 117 := by 
  rintro ⟨x, y, h⟩
  have h1 : x ^ 2 % 7 = 0 ∨ x ^ 2 % 7 = 1 ∨ x ^ 2 % 7 = 2 ∨ x ^ 2 % 7 = 4 := by
    have h2 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h2]

  have h2 : x ^ 2 % 7 = 5 := by
    have h3 : x ^ 2 = 7 * y ^ 2 + 117 := by linarith
    omega
  omega