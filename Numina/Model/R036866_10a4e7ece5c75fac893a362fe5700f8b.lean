import Mathlib

theorem algebra_307909 (a b : ℝ) (ha : a + b - 2 ≥ 0) (hb : b - a - 1 ≤ 0) (h : a ≤ 1) :
    (a + 2 * b) / (2 * a + b) ≤ 7 / 5 := by
  have h1 : 2 * a + b > 0 := by
    linarith
  have h2 : b ≤ 3 * a := by
    nlinarith
  have h3 : (a + 2 * b) / (2 * a + b) ≤ 7 / 5 := by
    apply (div_le_div_iff (by positivity) (by norm_num)).mpr
    linarith
  exact h3