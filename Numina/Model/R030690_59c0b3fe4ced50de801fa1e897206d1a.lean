import Mathlib

theorem inequalities_36231 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (h : d = a + b + c + 2 * Real.sqrt (a * b + b * c + c * a)) :
    a = b + c + d - 2 * Real.sqrt (b * c + c * d + d * b) := by
  have h1 : b * c + c * d + d * b = (Real.sqrt (a * b + b * c + c * a) + b + c) ^ 2 := by
    rw [h]
    nlinarith [Real.sqrt_nonneg (a * b + b * c + c * a), Real.sq_sqrt (show 0 ≤ a * b + b * c + c * a by positivity)]
  have h2 : Real.sqrt (b * c + c * d + d * b) = Real.sqrt (a * b + b * c + c * a) + b + c := by
    rw [h1]
    have h3 : Real.sqrt ((Real.sqrt (a * b + b * c + c * a) + b + c) ^ 2) = Real.sqrt (a * b + b * c + c * a) + b + c := by
      rw [Real.sqrt_sq (show 0 ≤ Real.sqrt (a * b + b * c + c * a) + b + c by positivity)]
    exact h3
  calc
    a = d - 2 * Real.sqrt (a * b + b * c + c * a) - b - c := by
      nlinarith [Real.sqrt_nonneg (a * b + b * c + c * a), Real.sq_sqrt (show 0 ≤ a * b + b * c + c * a by positivity)]
    _ = b + c + d - 2 * Real.sqrt (b * c + c * d + d * b) := by
      rw [show Real.sqrt (b * c + c * d + d * b) = Real.sqrt (a * b + b * c + c * a) + b + c by exact h2]
      nlinarith [Real.sqrt_nonneg (a * b + b * c + c * a), Real.sq_sqrt (show 0 ≤ a * b + b * c + c * a by positivity)]