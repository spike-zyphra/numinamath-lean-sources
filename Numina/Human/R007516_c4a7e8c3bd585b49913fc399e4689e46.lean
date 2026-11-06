import Mathlib

/- If 7 knicks = 2 knacks and 3 knacks = 4 knocks, how many knicks are equal to 24 knocks? -/
theorem algebra_15279 (n m p : ℕ) (h₀ : 7 * n = 2 * m) (h₁ : 3 * m = 4 * p) :
    24 * p = 63 * n := by
  linarith