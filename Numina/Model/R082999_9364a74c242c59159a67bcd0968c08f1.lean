import Mathlib

theorem algebra_2489 {x : ℝ} (hx : 0 ≤ -x) : (- Real.sqrt (- x) ) ^ 2 = x ↔ x = 0 := by
  constructor
  · -- Forward direction: If $(-\sqrt{-x})^2 = x$, then $x = 0$
    intro h
    have h1 : Real.sqrt (-x) ^ 2 = -x := by
      rw [Real.sq_sqrt]
      linarith
    have h3 : Real.sqrt (-x) ^ 2 = x := by
      nlinarith [h]
    have h4 : x = -x := by
      nlinarith [h1, h3]
    linarith
  · -- Reverse direction: If $x = 0$, prove $(- Real.sqrt (- x)) ^ 2 = x$
    intro h
    rw [show x = 0 by linarith [h]]
    have h1 : Real.sqrt (- (0 : ℝ)) = 0 := by
      norm_num [Real.sqrt_eq_zero]
    nlinarith [h1]