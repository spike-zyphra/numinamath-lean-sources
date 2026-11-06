import Mathlib

theorem number_theory_5842 (n : ℤ) (hn : n = 2891) :
    ¬∃ x y : ℤ, x ^ 3 - 3 * x * y ^ 2 + y ^ 3 = n := by
  rw [hn]
  intro h
  rcases h with ⟨x, y, h_eq⟩
  have eq1 : (x ^ 3 - 3 * x * y ^ 2 + y ^ 3 : ℤ) % 9 = 2 := by
    omega
  have eq3 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by
    omega
  have eq4 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by
    omega
  have eq2 : (x ^ 3 - 3 * x * y ^ 2 + y ^ 3) % 9 = 2 := eq1
  rcases eq3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> rcases eq4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, pow_succ, h3, h4] at eq2 <;> omega