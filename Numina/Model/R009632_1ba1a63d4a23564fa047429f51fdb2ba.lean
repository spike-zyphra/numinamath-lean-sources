import Mathlib

theorem algebra_10553 {a b : ℝ} (h1 : 2010 * a + 2014 * b = 2018) (h2 : 2012 * a + 2016 * b = 2020) : a - b = -3 := by
  have h3 : a + b = 1 := by
    linarith
  have h4 : b = 2 := by
    linarith [h1, h3]
  have h5 : a = -1 := by
    linarith [h3, h4]
  -- Now compute a - b
  linarith [h5, h4]