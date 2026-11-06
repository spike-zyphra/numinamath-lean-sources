import Mathlib

  theorem algebra_12574 {r : ℝ} (hr : r ≠ 0) (h : (r + 1 / r) ^ 2 = 3) :
  r ^ 3 + (1 / r) ^ 3 = 0 := by
    have h1 : r ^ 2 + (1 / r) ^ 2 = 1 := by
      have eq1 : r ^ 2 + (1 / r) ^ 2 = (r + 1 / r) ^ 2 - 2 := by
        field_simp
        <;> ring
      linarith [h, eq1]
    have eq2 : r ^ 3 + (1 / r) ^ 3 = (r + 1 / r) * ( (r ^ 2 + (1 / r) ^ 2 ) - 1 ) := by
      field_simp
      ring
    rw [eq2, h1]
    all_goals norm_num
    all_goals linarith