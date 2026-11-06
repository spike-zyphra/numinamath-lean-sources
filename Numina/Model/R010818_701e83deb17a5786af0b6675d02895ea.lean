import Mathlib

theorem number_theory_17010 (n : ℕ) (h₀ : 0 ≤ n) (h₁ : n < 31) (h₂ : 3 * n ≡ 1 [MOD 31]) :
    (2 ^ n) ^ 3 - 2 ≡ 6 [MOD 31] := by
  norm_num [Nat.ModEq] at h₂ ⊢
  have hn : n = 21 := by
    omega
  rw [hn]
  all_goals norm_num