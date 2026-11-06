import Mathlib

theorem algebra_16026 (p : ℝ) (hp : 0 ≤ p) :
    Real.sqrt (10 * p) * Real.sqrt (5 * p ^ 2) * Real.sqrt (6 * p ^ 4) =
    10 * p ^ 3 * Real.sqrt (3 * p) := by
  have h1 : Real.sqrt (10 * p) * Real.sqrt (5 * p ^ 2) * Real.sqrt (6 * p ^ 4) =
      Real.sqrt ((10 * p) * (5 * p ^ 2) * (6 * p ^ 4)) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    all_goals
      positivity
  rw [h1]
  have h2 : (10 * p) * (5 * p ^ 2) * (6 * p ^ 4) = (10 * p ^ 3) ^ 2 * (3 * p) := by
    ring_nf
  rw [h2]
  have h3 : 0 ≤ (10 * p ^ 3 : ℝ) := by positivity
  have h4 : Real.sqrt (( (10 * p ^ 3 : ℝ ) ^ 2 * (3 * p))) = (10 * p ^ 3) * Real.sqrt (3 * p) := by
    calc
      Real.sqrt (((10 * p ^ 3 : ℝ ) ^ 2 * (3 * p))) = Real.sqrt (((10 * p ^ 3 : ℝ ) ^ 2) * (3 * p)) := by ring_nf
      _ = Real.sqrt (((10 * p ^ 3 : ℝ ) ) ^ 2) * Real.sqrt (3 * p) := by rw [Real.sqrt_mul (by positivity)]
      _ = (10 * p ^ 3 : ℝ) * Real.sqrt (3 * p) := by 
        rw [Real.sqrt_sq (by positivity)]
        <;> ring_nf
        <;> try tauto
  rw [h4]
  <;> ring_nf
  <;> try tauto