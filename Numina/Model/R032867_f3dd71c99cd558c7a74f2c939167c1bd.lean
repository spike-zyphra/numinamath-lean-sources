import Mathlib

theorem number_theory_193250 (x y : ℤ) : x^2 + 4 * x - 11 = 8 * y → False := by
  intro h
  have h1 : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
    have h1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod]
    <;> omega
  have h2 : (x ^ 2 + 4 * x) % 8 = 3 := by
    omega
  omega