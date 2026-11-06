import Mathlib

theorem algebra_21368 (x : ℝ) (hx : x ≥ 0) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by

  have h1 : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt ((60 * x) * (12 * x) * (63 * x)) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]

  have h2 : (60 * x) * (12 * x) * (63 * x) = (36 * x) ^ 2 * (35 * x) := by
    ring_nf

  rw [h1, h2]

  have h3 : Real.sqrt ((36 * x) ^ 2 * (35 * x)) = (36 * x) * Real.sqrt (35 * x) := by
    have hx2 : Real.sqrt ((36 * x) ^ 2 * (35 * x)) = Real.sqrt ((36 * x) ^ 2) * Real.sqrt (35 * x) := by
      rw [Real.sqrt_mul (by positivity)]
    have hx3 : Real.sqrt ((36 * x) ^ 2) = (36 * x) := by
      rw [Real.sqrt_sq (by positivity)]
    rw [hx2, hx3]

  exact h3