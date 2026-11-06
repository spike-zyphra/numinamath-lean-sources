import Mathlib

/- The sum of two nonzero real numbers is 4 times their product. What is the sum of the reciprocals of the two numbers?
(A) 1
(B) 2
(C) 4
(D) 8
(E) 12
-/

theorem algebra_97534 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
(h : x + y = 4 * x * y) : 1 / x + 1 / y = 4 := by
  -- make sure to declare x, y as invertible as division related facts will be used
  have : Invertible y := invertibleOfNonzero hy
  have : Invertible x := invertibleOfNonzero hx
  calc
    -- manipulate to turn 1/x + 1/y into (x + y) / (x * y) as terms in that expression are in hypothesis
    1 / x + 1 / y = 1 / x * y / y + 1 / y := by  rw [mul_div_cancel_of_invertible]
    _ = 1 / x * y / y + 1 / y * x / x := by rw [mul_div_cancel_of_invertible (1/y)]
    _ = y / (x * y) + x / (x * y) := by ring
    _ = (x + y) / (x * y) := by ring
    -- rewrite to turn x + y into 4 * x * y, then x * y will get cancelled
    _ = 4 * x * y / (x * y) := by rw [h]
    -- reorder terms to easily use mul_div_cancel twice
    _ = 4 * x / x * y / y := by ring
    _ = 4 * x / x := by rw [mul_div_cancel_of_invertible]
    _ = 4 := by rw [mul_div_cancel_of_invertible]