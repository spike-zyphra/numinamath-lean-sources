import Mathlib

/- A 10-by-12-inch page has margins of 1.5 inches on all sides. What fraction of the area of the page is taken up by the margins? Express your answer as a common fraction. -/
theorem algebra_21738 (a b c : ℝ) (ha : a = 10) (hb : b = 12) (hc : c = 1.5):
    (a * b - (a - 2 * c) * (b - 2 * c)) / (a * b) = 19 / 40 := by
        rw [ha, hb, hc]
        norm_num
