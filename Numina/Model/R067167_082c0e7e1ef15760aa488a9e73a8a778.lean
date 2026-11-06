import Mathlib

theorem number_theory_118264 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 7 ∣ (2 * a + 5 * b)) : 7 ∣ (5 * a + 2 * b) := by
  omega