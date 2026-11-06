import Mathlib

theorem calculus_12781 {v w : ℝ × ℝ} (hw : w ≠ 0) (h : v.1 * w.1 + v.2 * w.2 = 3 * w.1 + 2 * w.2) :
    (5 * v).1 * w.1 + (5 * v).2 * w.2 = 15 * w.1 + 10 * w.2 := by
  -- First, compute $(5v) \cdot w$. Note $5v$ means scalar multiplication
  simp [mul_add] at *
  -- $(5*v_1*w_1 + 5*v_2*w_2) = 5*(v_1*w_1 + v_2*w_2)$
  -- so we can factor the 5
  linarith [h]