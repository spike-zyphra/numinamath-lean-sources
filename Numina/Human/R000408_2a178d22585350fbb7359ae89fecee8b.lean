import Mathlib

/- A car travels the 120 miles from $A$ to $B$ at 60 miles per hour, and then returns to $A$ on the same road. If the average rate of the round trip is 45 miles per hour, what is the rate, in miles per hour, of the car traveling back from $B$ to $A$? -/
theorem algebra_10356 (d : ℝ) (h : d = 120) (v1 v2 : ℝ) (h1 : v1 = 60) (h2 : (2 * d) / (d / v1 + d / v2) = 45) :
    v2 = 36 := by
  -- Simple calculations breaken into steps.
  rw [h, h1] at h2
  norm_num at h2
  have h3 : 240 / (2 + 120 / v2) ≠ 0 := by
    linarith only [h2]
  have h4 : 240 = 45 * (2 + 120 / v2) := by
    calc
      240 = 240 / (2 + 120 / v2) * (2 + 120 / v2) := by rw [div_mul_cancel₀]; rw [div_ne_zero_iff] at h3; tauto
      _ = 45 * (2 + 120 / v2) := by rw [h2]
  norm_num at h4
  have h5 : 240 / 45 - 2 = 120 / v2 := by
    calc
      240 / 45 - 2 = 45 * (2 + 120 / v2) / 45 - 2 := by rw [h4]
      _ = 2 + 120 / v2 - 2 := by rw [mul_div_cancel_left₀]; norm_num
      _ = 120 / v2 := by ring
  have h6 : v2 = 120 / (240 / 45 - 2) := by
    calc
      v2 = 120 / (120 / v2) := by field_simp
      _ = 120 / (240 / 45 - 2) := by rw [h5]
  norm_num at h6
  exact h6
