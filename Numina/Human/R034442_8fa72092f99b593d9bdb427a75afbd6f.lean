import Mathlib

/- Real numbers x, y, and z satisfy the inequalities 0 < x < 1, -1 < y < 0, and 1 < z < 2. Which of the following numbers is necessarily positive?
(A) y + x^2
(B) y + xz
(C) y + y^2
(D) y + 2y^2
(E) y + z
-/
theorem inequalities_96524 (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : -1 < y ∧ y < 0) (hz : 1 < z ∧ z < 2) : 0 < y + z :=
  -- adding up lower bounds of y, z we see lower bound is 0 so y + z > 0
  calc
    0 = -1 + 1 := by norm_num
    _ < y + z := by
      apply add_lt_add
      . exact hy.left
      . exact hz.left