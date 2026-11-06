import Mathlib

theorem inequalities_302436 (a b : ℝ) (m : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (h1 : a + b ≤ 14) (h2 : a * b ≥ 48 + m) :
    m = 1 := by
  have h3 : a * b ≤ (a + b) ^ 2 / 4 := by
    nlinarith [sq_nonneg (a - b)]
  have h4 : a * b ≤ 49 := by
    nlinarith [h1, h3]
  have h5 : (m : ℝ) ≤ 1 := by 
    nlinarith
  have h6 : m ≤ 1 := by
    exact_mod_cast h5
  have h7 : m = 1 := by
    linarith
  exact h7