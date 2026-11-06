import Mathlib

/- If $2010a + 2014b = 2018$ and $2012a + 2016b = 2020$, what is the value of $a - b$ ? -/
theorem algebra_10553 {a b : ℝ} (h1 : 2010 * a + 2014 * b = 2018) (h2 : 2012 * a + 2016 * b = 2020) : a - b = -3 := by 
  linarith