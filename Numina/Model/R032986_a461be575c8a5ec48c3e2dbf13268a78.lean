import Mathlib

theorem number_theory_293744 : ∃ a b, a^2 + b^2 = 2005^2005 ∧ ¬∃ c d, c^3 + d^3 = 2005^2005 := by
  use 39 * 2005^1002, 22 * 2005^1002
  constructor
  · -- Show that (39 * 2005^1002)^2 + (22 * 2005^1002)^2 = 2005^2005
    norm_num
  · -- Show that 2005^2005 is not a sum of two cubes
    intro h
    rcases h with ⟨c, d, h1⟩
    have h4 : c^3 % 7 = 0 ∨ c^3 % 7 = 1 ∨ c^3 % 7 = 6 := by
      have h1 : c % 7 = 0 ∨ c % 7 = 1 ∨ c % 7 = 2 ∨ c % 7 = 3 ∨ c % 7 = 4 ∨ c % 7 = 5 ∨ c % 7 = 6 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, 
          pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
    have h5 : d^3 % 7 = 0 ∨ d^3 % 7 = 1 ∨ d^3 % 7 = 6 := by
      have h2 : d % 7 = 0 ∨ d % 7 = 1 ∨ d % 7 = 2 ∨ d % 7 = 3 ∨ d % 7 = 4 ∨ d % 7 = 5 ∨ d % 7 = 6 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, 
          pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
    have h6 : (c^3 + d^3) % 7 = 3 := by
      have h7 : 2005 ^ 2005 % 7 = 3 := by
        norm_num
      omega
    omega