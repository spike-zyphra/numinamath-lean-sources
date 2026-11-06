import Mathlib

theorem algebra_11157 {x y z : ℝ} (hy : y ≠ x) (hz : z ≠ y) (hx : x ≠ z)
    (h1 : y = (x - 2)^2) (h2 : z = (y - 2)^2) (h3 : x = (z - 2)^2) :
    x + y + z = 5 ∨ x + y + z = 6 := by
  have h4' : (x + y + z - 5) * (x + y + z - 6) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by 
      intro h'
      apply hy
      linarith
    ), sq_pos_of_ne_zero (show y - z ≠ 0 by 
      intro h'
      apply hz
      linarith
    ), sq_pos_of_ne_zero (show z - x ≠ 0 by 
      intro h'
      apply hx
      linarith
    )]
  cases' (mul_eq_zero.1 h4') with h5 h6
  · -- Case where (x + y + z) - 5 = 0, so (x + y + z) = 5
    left
    linarith
  · -- Case where (x + y + z) - 6 = 0, so (x + y + z) = 6
    right
    linarith