import Mathlib

/- Simplify $(2x+5)-(-3x+8)$. -/
theorem algebra_19932 (x : ℝ) : (2 * x + 5) - (-3 * x + 8) = 5 * x - 3 := by
    -- 使用 ring_nf 策略自动进行代数化简
    ring_nf
