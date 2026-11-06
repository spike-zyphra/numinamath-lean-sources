import Mathlib

theorem algebra_298803 {x y : ℝ} (hx : 1300 ≤ x ∧ x ≤ 2800) (hy : y = (x - 1300) * 10 / 100 + 25) :
    y = 55 ↔ x = 1600 := by
  constructor
  · -- Forward direction: assume y = 55, prove x = 1600
    intro hy1
    rw [hy] at hy1
    -- solve the equation (x - 1300) * 10 / 100 + 25 = 55
    linarith
  · -- Backward direction: assume x = 1600, prove y = 55
    intro hx1
    rw [hx1] at hy
    -- compute y from x = 1600
    linarith [hy]