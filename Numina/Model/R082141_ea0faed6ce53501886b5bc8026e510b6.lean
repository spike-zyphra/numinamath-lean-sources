import Mathlib

theorem number_theory_22812 (m n : ℤ) (h₀ : m ≡ 4 [ZMOD 14]) (h₁ : m - n ≡ 10 [ZMOD 14]) :
    m + n ≡ 12 [ZMOD 14] := by
  norm_num [Int.ModEq] at h₀ h₁ ⊢
  omega