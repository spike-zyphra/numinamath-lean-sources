import Mathlib

theorem number_theory_108988 (a b : ℤ) (_ : 0 < a) (h₀ : 0 < b)
    (h₁ : a + b^3 ≡ 0 [ZMOD a^2 + 3 * a * b + 3 * b^2 - 1]) :
    ∃ c, c^3 ∣ a^2 + 3 * a * b + 3 * b^2 - 1 := by
  use 1
  simp