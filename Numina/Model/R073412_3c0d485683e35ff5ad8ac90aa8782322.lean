import Mathlib

theorem algebra_291346 (a b c d e : ℕ)
    (h₀ : a < b ∧ b < c ∧ c < d ∧ d < e)
    (h₁ : a + b + c + d + e = 31)
    (h₂ : e = 3 * a) :
    d = 8 := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  omega