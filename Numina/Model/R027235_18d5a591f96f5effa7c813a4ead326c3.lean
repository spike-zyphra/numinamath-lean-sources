import Mathlib

theorem number_theory_3760 : ¬∃ x y : ℕ, 0 < x ∧ 0 < y ∧ 2 + 3 * x ^ 2 + 5 * x ^ 4 = y ^ 2 := by
  rintro ⟨x, y, hx, hy, heq⟩
  have eq1 : (2 + 3 * x ^ 2 + 5 * x ^ 4) % 4 = 2 := by
    have h1 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
    rcases h1 with (h | h | h | h)
    · 
      simp [Nat.add_mod, Nat.mul_mod, pow_two, pow_succ, h]
    · 
      simp [Nat.add_mod, Nat.mul_mod, pow_two, pow_succ, h]
    · 
      simp [Nat.add_mod, Nat.mul_mod, pow_two, pow_succ, h]
    · 
      simp [Nat.add_mod, Nat.mul_mod, pow_two, pow_succ, h]
  have eq2 : (2 + 3 * x ^ 2 + 5 * x ^ 4) % 4 = y ^ 2 % 4 := by 
    omega
  have eq3 : y ^ 2 % 4 = 0 ∨ y ^ 2 % 4 = 1 := by
    have h1 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
    rcases h1 with (h1 | h1 | h1 | h1)
    · 
      simp [Nat.add_mod, Nat.mul_mod, pow_two, h1]
    · 
      simp [Nat.add_mod, Nat.mul_mod, pow_two, h1]
    · 
      simp [Nat.add_mod, Nat.mul_mod, pow_two, h1]
    · 
      simp [Nat.add_mod, Nat.mul_mod, pow_two, h1]
  omega