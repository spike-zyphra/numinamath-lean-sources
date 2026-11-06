import Mathlib

theorem algebra_309729 {a b c : ℝ} (ha : a + b + c = 5) (h1 : a^2 + b^2 + c^2 = 15) (h2 : a^3 + b^3 + c^3 = 47) :
    (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) = 625 := by
  have h3 : a * b + a * c + b * c = 5 := by 
    have h4 : a^2 + b^2 + c^2 = (a + b + c)^2 - 2 * (a * b + a * c + b * c) := by 
      ring
    rw [ha] at h4
    linarith
  have h4 : a * b * c = -1 := by
    have h5 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * ((a^2 + b^2 + c^2) - (a * b + a * c + b * c)) := by 
      ring
    rw [ha, h1, h3] at h5
    linarith
  have h5 : (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) = 625 := by 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a + b + c - 5), sq_nonneg ((a * b + a * c + b * c) - 5), sq_nonneg ((a * b * c) + 1)]
  exact h5