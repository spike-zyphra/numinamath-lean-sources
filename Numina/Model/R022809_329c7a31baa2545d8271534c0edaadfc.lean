import Mathlib

theorem number_theory_236175 : ∃ x y, x^2 - y^2 = 1993 ∧ ¬∃ x y, x^3 - y^3 = 1993 ∧ ¬∃ x y, x^4 - y^4 = 1993 := by
  use 997, 996
  constructor
  · -- Show that 997² - 996² = 1993
    norm_num
  · -- Show that it's impossible to find natural numbers x and y such that x^3 - y^3 = 1993
    intro h
    rcases h with ⟨x, y, h1, h2⟩
    have h3 : x^3 - y^3 = 1993 := by linarith
    -- Now we perform modulo 9 arithmetic to show contradiction
    have eq1 : x^3 % 9 = 0 ∨ x^3 % 9 = 1 ∨ x^3 % 9 = 8 := by
      have h1 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, pow_succ, Nat.mul_mod, Nat.pow_mod]
    -- Now we perform modulo 9 arithmetic to show contradiction
    have eq2 : y^3 % 9 = 0 ∨ y^3 % 9 = 1 ∨ y^3 % 9 = 8 := by
      have h1 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, pow_succ, Nat.mul_mod, Nat.pow_mod]
    omega