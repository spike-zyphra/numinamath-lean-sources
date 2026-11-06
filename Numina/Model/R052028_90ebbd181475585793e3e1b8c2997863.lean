import Mathlib

theorem algebra_185072 (r w b : ℕ)
    (h₀ : b ≥ (1 / 2 : ℚ) * w)
    (h₁ : b ≤ (1 / 3 : ℚ) * r)
    (h₂ : w + b ≥ 55) :
    r ≥ 57 := by
  have h3 : (2 : ℚ) * b ≥ (w : ℚ) := by
    linarith
  have h4 : (3 : ℚ) * b ≤ (r : ℚ) := by
    linarith
  have h5 : 2 * b ≥ w := by
    exact_mod_cast h3
  have h6 : 3 * b ≤ r := by
    exact_mod_cast h4
  omega