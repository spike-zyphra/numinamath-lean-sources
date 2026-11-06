import Mathlib

theorem number_theory_185337 (x : ℤ) (h : (x ^ 2) % 1000 = 1) :
    x % 1000 = 1 ∨ x % 1000 = 249 ∨ x % 1000 = 251 ∨ x % 1000 = 499 ∨
    x % 1000 = 501 ∨ x % 1000 = 749 ∨ x % 1000 = 751 ∨ x % 1000 = 999 := by
  have h1 : x % 1000 ≥ 0 := by
    omega
  have h2 : x % 1000 < 1000 := by
    omega
  have h3 : (x % 1000) ^ 2 % 1000 = 1 := by
    have h4 : x ^ 2 % 1000 = 1 := h
    have h5 : (x % 1000 : ℤ) ^ 2 % 1000 = 1 := by
      have h6 : (x % 1000 : ℤ) ^ 2 % 1000 = x ^ 2 % 1000 := by
        have h7 : (x % 1000 : ℤ) ≡ x [ZMOD 1000] := by
          exact Int.mod_modEq x 1000
        have h8 : (x % 1000 : ℤ) ^ 2 ≡ x ^ 2 [ZMOD 1000] := by
          exact Int.ModEq.pow 2 h7
        exact h8
      rw [h6, h4]
    assumption
  interval_cases h6 : x % 1000 <;> omega