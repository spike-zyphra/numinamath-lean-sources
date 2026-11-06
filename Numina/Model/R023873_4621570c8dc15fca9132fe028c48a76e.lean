import Mathlib

theorem algebra_322582 (a c : ℤ) (ha : 0 < a) (hc : 0 < c)
    (h1 : ∃ p : ℕ, p.Prime ∧ p^2 + a * p + 18 = 0) (h2 : ∃ p : ℕ, p.Prime ∧ p^2 - a * p + c = 0) :
    c = -26 ∨ c = -36 := by

  rcases h1 with ⟨p, hp, heq1⟩

  have eq1 : (p : ℤ) ^ 2 + a * (p : ℤ) + 18 = 0 := by
    exact_mod_cast heq1

  have hp2 : p ≥ 2 := Nat.Prime.two_le hp

  have eq2 : (p : ℤ) ≥ 2 := by exact_mod_cast hp2

  have ha1 : a ≥ 1 := by linarith

  nlinarith [sq_nonneg ( (p : ℤ) ), sq_nonneg ( (a : ℤ) ), sq_pos_of_pos ha, 
          sq_nonneg ( (p : ℤ) - 2 ), sq_nonneg ( (a : ℤ) - 1 ), 
          Nat.Prime.two_le hp, ha
        ]