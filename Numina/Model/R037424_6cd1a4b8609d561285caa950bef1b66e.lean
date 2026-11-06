import Mathlib

theorem algebra_604746 {x y z : ℝ} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    (h : (y * z - x ^ 2) / (1 - x) = (x * z - y ^ 2) / (1 - y)) :
    (y * z - x ^ 2) / (1 - x) = x + y + z := by
  have eq1 : (y * z - x ^ 2) / (1 - x) = (x * z - y ^ 2) / (1 - y) := h
  have hx1 : 1 - x ≠ 0 := by
    intro h_eq
    apply hx
    linarith
  have hy1 : 1 - y ≠ 0 := by
    intro h_eq
    apply hy
    linarith
  -- clear fractions by cross multiplying
  have eq2 : (y * z - x ^ 2) * (1 - y) = (x * z - y ^ 2) * (1 - x) := by
    field_simp [hx1, hy1] at eq1 ⊢
    linarith
  -- from the cross multiplied equation, derive claimed result
  have eq3 : y * z + x * y + x * z - x - y - z = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (x - 1 : ℝ) ≠ 0 by
      intro h1
      apply hx
      linarith
    ), sq_pos_of_ne_zero (show (y - 1 : ℝ) ≠ 0 by
      intro h1
      apply hy
      linarith
    ), sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
      intro h1
      apply hxy
      linarith
    ), sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  -- now, from eq3, show that $\frac{yz - x^2}{1 - x} = x + y + z$.
  have eq4 : y * z - x ^ 2 = (1 - x) * (x + y + z) := by
    nlinarith [eq3]
  -- now divide both sides by 1 - x to get the final result.
  have hx2 : 1 - x ≠ 0 := hx1
  field_simp [hx2] at eq4 ⊢
  <;> linarith [eq4]
  all_goals nlinarith