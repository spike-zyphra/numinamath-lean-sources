import Mathlib

/-- Susie pays for 4 muffins and 3 bananas.
Calvin spends twice as much paying for 2 muffins and 16 bananas.
A muffin is how many times as expensive as a banana?
(A) 3/2  (B)5/3  (C)7/4  (D)2  (E)13​/4 -/
theorem algebra_96384 {m b : ℝ} (hb : b > 0)
    (h1 : 2 * (4 * m + 3 * b) = 2 * m + 16 * b) :
    m / b = 5 / 3 := by

  -- we rewrite the arithmetic equality in a form that is simpler
  field_simp

  -- We have the equality 8m + 6b = 2m + 16b
  ring_nf at h1

  -- Canceling out the common factors, we get 6m = 10b
  replace h1 : 6 * m = 10 * b := by
    calc _ = (m * 8 + b * 6) - 2 * m - 6 * b := by ring
         _ = (2 * m + 16 * b) - 2 * m - 6 * b := by rw [h1]; ring
         _ = _ := by ring

  -- Canceling out the two factors, we get 3m = 5b
  replace h1 : 3 * m = 5 * b := by
    calc _ = 6 * m / 2 := by ring
         _ = 10 * b / 2 := by rw [h1]
         _ = _ := by ring

  -- We are done
  rw [←h1, mul_comm]