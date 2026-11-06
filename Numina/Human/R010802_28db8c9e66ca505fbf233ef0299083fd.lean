import Mathlib

/- On a particular January day, the high temperature in Lincoln, Nebraska, was $16$ degrees higher than the low temperature, and the average of the high and the low temperatures was $3\,^\circ$. In degrees, what was the low temperature in Lincoln that day? -/
theorem algebra_20076 (h l : ℝ) (h₀ : h = l + 16) (h₁ : (h + l) / 2 = 3) :
    l = -5 := by
  linarith
