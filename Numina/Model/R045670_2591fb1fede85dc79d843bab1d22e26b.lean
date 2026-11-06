import Mathlib

theorem algebra_13662 (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (28 * x) * Real.sqrt (15 * x) * Real.sqrt (21 * x) =
    42 * x * Real.sqrt (5 * x) := by
  have h1 : Real.sqrt (28 * x) * Real.sqrt (15 * x) * Real.sqrt (21 * x) =
    Real.sqrt ((28 * x) * (15 * x) * (21 * x)) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  rw [h1]
  have h2 : (28 * x) * (15 * x) * (21 * x) = (42 * x) ^ 2 * (5 * x) := by
    nlinarith [sq_nonneg (x), sq_nonneg (42 * x)]
  rw [h2]
  have h3 : Real.sqrt ((42 * x) ^ 2 * (5 * x)) =
    (42 * x) * Real.sqrt (5 * x) := by
    calc
      Real.sqrt ((42 * x) ^ 2 * (5 * x))
          = Real.sqrt ((42 * x) ^ 2) * Real.sqrt (5 * x) := by
            rw [Real.sqrt_mul (by positivity)]
      _ = (42 * x) * Real.sqrt (5 * x) := by
        rw [Real.sqrt_sq (by positivity)]
  rw [h3]
  all_goals ring_nf <;> norm_num