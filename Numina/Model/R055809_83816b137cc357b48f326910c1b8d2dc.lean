import Mathlib

theorem algebra_233181 (a b c : ℕ) (ha : a + b + c = 100) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : (a + b / 2 : ℝ) = 40) : (a - c : ℝ) = -20 := by
  have h1 : (a : ℝ) + (b : ℝ) / 2 = 40 := by
    exact_mod_cast h
  have h2 : 2 * (a : ℝ) + (b : ℝ) = 80 := by
    linarith [h1]
  have h3 : (a : ℝ) + (b : ℝ) + (c : ℝ) = 100 := by
    exact_mod_cast ha
  have h4 : (c : ℝ) = (a : ℝ) + 20 := by
    linarith [h2, h3]
  have h5 : (a : ℝ) - (c : ℝ) = -20 := by
    rw [h4]
    linarith
  exact_mod_cast h5