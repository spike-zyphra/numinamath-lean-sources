import Mathlib

theorem number_theory_150483 (a b c : ℕ) (h₀ : a^2 + b^2 + c^2 ≡ 0 [MOD 9]) :
    a^2 ≡ b^2 [MOD 9] ∨ b^2 ≡ c^2 [MOD 9] ∨ a^2 ≡ c^2 [MOD 9] := by
  norm_num [Nat.ModEq] at h₀ ⊢
  have hres_a : a ^ 2 % 9 = 0 ∨ a ^ 2 % 9 = 1 ∨ a ^ 2 % 9 = 4 ∨ a ^ 2 % 9 = 7 := by
    have ha0 : a % 9 = 0 ∨ a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 3 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨ a % 9 = 6 ∨ a % 9 = 7 ∨ a % 9 = 8 := by
      omega
    rcases ha0 with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod]
  have hres_b : b ^ 2 % 9 = 0 ∨ b ^ 2 % 9 = 1 ∨ b ^ 2 % 9 = 4 ∨ b ^ 2 % 9 = 7 := by
    have hb0 : b % 9 = 0 ∨ b % 9 = 1 ∨ b % 9 = 2 ∨ b % 9 = 3 ∨ b % 9 = 4 ∨ b % 9 = 5 ∨ b % 9 = 6 ∨ b % 9 = 7 ∨ b % 9 = 8 := by
      omega
    rcases hb0 with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod]
  have hres_c : c ^ 2 % 9 = 0 ∨ c ^ 2 % 9 = 1 ∨ c ^ 2 % 9 = 4 ∨ c ^ 2 % 9 = 7 := by
    have hc0 : c % 9 = 0 ∨ c % 9 = 1 ∨ c % 9 = 2 ∨ c % 9 = 3 ∨ c % 9 = 4 ∨ c % 9 = 5 ∨ c % 9 = 6 ∨ c % 9 = 7 ∨ c % 9 = 8 := by
      omega
    rcases hc0 with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod]
  omega