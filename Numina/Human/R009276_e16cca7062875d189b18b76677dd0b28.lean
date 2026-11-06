import Mathlib

/- At the beginning of my bike ride I feel good, so I can travel   20 miles per hour.  Later, I get tired and travel only 12 miles  per hour.  If I travel a total of 122 miles in a total time of   8 hours, for how many hours did I feel good?  Express your  answer as a common fraction. -/
theorem algebra_14273 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h : x * 20 + y * 12 = 122 ∧ x + y = 8) :
    x = 13 / 4 := by
  have h₁ : x = 13 / 4 := by
    linarith
  linarith