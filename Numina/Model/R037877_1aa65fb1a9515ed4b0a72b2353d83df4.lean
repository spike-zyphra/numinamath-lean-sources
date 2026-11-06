import Mathlib

theorem algebra_14595 (p : ℝ) (hp : 0 ≤ p) :
    Real.sqrt (30 * p) * Real.sqrt (5 * p) * Real.sqrt (6 * p) = 30 * p * Real.sqrt p := by
  have h1 : Real.sqrt (30 * p) * Real.sqrt (5 * p) * Real.sqrt (6 * p) =
      Real.sqrt ((30 * p) * (5 * p) * (6 * p)) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  rw [h1]
  have h2 : (30 * p) * (5 * p) * (6 * p) = (900 * (p ^ 3)) := by 
    ring_nf
  rw [h2]
  have h3 : Real.sqrt (900 * (p ^ 3)) = Real.sqrt ((30 * p) ^ 2 * p) := by
    ring_nf
  rw [h3]
  have h4 : Real.sqrt ((30 * p) ^ 2 * p) = Real.sqrt ((30 * p) ^ 2) * Real.sqrt p := by
    rw [← Real.sqrt_mul (by positivity)]
  rw [h4]
  have h5 : Real.sqrt ((30 * p) ^ 2) = 30 * p := by
    rw [Real.sqrt_sq (by linarith)]
  rw [h5]
  all_goals ring_nf