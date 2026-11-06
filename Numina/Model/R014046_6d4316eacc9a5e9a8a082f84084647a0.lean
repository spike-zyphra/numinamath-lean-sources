import Mathlib

theorem number_theory_6598 :
    ¬∃ x : ℕ, 3 * x ^ 6 ≡ 5 [MOD 7] ∧
    ¬∃ x : ℕ, x ^ 12 ≡ 16 [MOD 17] ∧
    ¬∃ x : ℕ, 5 * x ^ 11 ≡ -6 [ZMOD 17] ∧
    ¬∃ x : ℕ, 3 * x ^ 14 ≡ 2 [MOD 23] ∧
    ¬∃ x : ℕ, x ^ 15 ≡ 14 [MOD 41] ∧
    ¬∃ x : ℕ, 7 * x ^ 7 ≡ 11 [MOD 41] ∧
    ¬∃ x : ℕ, 3 ^ x ≡ 2 [MOD 23] ∧
    ¬∃ x : ℕ, 13 ^ x ≡ 5 [MOD 23] := by 
  rintro ⟨x, hx₁, hx₂⟩
  have h1 : 3 * x ^ 6 % 7 = 5 % 7 := hx₁
  norm_num at h1
  have h2 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by 
    omega
  rcases h2 with (h | h | h | h | h | h | h)
  all_goals
    simp [h, Nat.pow_mod, Nat.mul_mod] at h1
    all_goals omega