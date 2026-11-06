import Mathlib

theorem number_theory_13381 (x : ℕ) (h₀ : 273 < x) (h₁ : x ≤ 336)
    (h₂ : x ≡ 2 [MOD 7]) (h₃ : x ≡ 3 [MOD 9]) : x = 282 := by
  norm_num [Nat.ModEq] at h₂ h₃ ⊢
  omega