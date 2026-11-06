import Mathlib

theorem algebra_326748 {a b c : ℝ} (ha : a + b + c = 5) (hb : a^2 + b^2 + c^2 = 15)
    (hc : a^3 + b^3 + c^3 = 47) :
    (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) = 625 := by
  have h1 : a * b + b * c + c * a = 5 := by
    have h2 : a * b + b * c + c * a = ( (a + b + c)^2 - (a^2 + b^2 + c^2) ) / 2 := by
      ring
    rw [h2]
    rw [ha, hb]
    norm_num
  have h3 : a * b * c = -1 := by
    have h4 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) := by
      ring
    rw [ha, h1] at h4
    nlinarith [hc]
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a + b + c - 5), sq_nonneg (a * b + b * c + c * a - 5), 
          sq_nonneg (a * b * c + 1)
          ]