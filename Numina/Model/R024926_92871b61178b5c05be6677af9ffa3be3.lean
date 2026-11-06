import Mathlib

theorem algebra_303502 (m n : ℤ) (h : ∃ x : ℤ, x^2 + 10 * m * x - 5 * n + 3 = 0) :
    False := by
  rcases h with ⟨x, hx⟩
  have h1 : x ^ 2 % 5 = 0 ∨ x ^ 2 % 5 = 1 ∨ x ^ 2 % 5 = 4 := by
    have h2 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    <;> omega
  have h2 : x ^ 2 % 5 = 2 := by
    have h3 : x ^ 2 + 3 = 5 * (n - 2 * m * x) := by
      linarith
    have h4 : (x ^ 2 + 3) % 5 = 0 := by
      omega
    omega
  omega