import Mathlib

/- Solve for $p$: $3p - 2(p-4) = 7p + 6$ -/
theorem algebra_18633 (p : ℝ) : 3 * p - 2 * (p - 4) = 7 * p + 6 ↔ p = 1 / 3 := by
  --simplify left side, is p + 8
  have h1: 3*p - 2*(p-4) = p+8 := by ring
  -- p+8 = 7p+6, then 6p = 2
  have h2: 3 * p - 2 * (p - 4) = 7 * p + 6 ↔ 6*p = 2 := by
    rw [h1]
    constructor <;> intro h <;> linarith [h]
  rw [h2]
  -- 6p=2, so p = 1/3
  constructor <;> intro h <;> linarith [h]