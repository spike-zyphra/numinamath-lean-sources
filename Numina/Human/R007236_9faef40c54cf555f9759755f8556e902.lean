import Mathlib

theorem algebra_215374 {x : ℝ} (hx : x ≠ 0) (h : x + 1 / x = Real.sqrt 2) :
    x ^ 8 + 1 / x ^ 8 = 2 := by
  have h1 : x ^ 2 + 1 / x ^ 2 = 0 := by
    calc
      x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by
        field_simp [hx]
        ring
      _ = (Real.sqrt 2) ^ 2 - 2 := by rw [h]
      _ = 2 - 2 := by rw [Real.sq_sqrt]; linarith
      _ = 0 := by norm_num
  have h2 : x ^ 2 ≥ 0 := by
    exact sq_nonneg x
  have h3 : 1 / x ^ 2 > 0 := by
    apply div_pos
    norm_num
    exact pow_two_pos_of_ne_zero hx
  have h4 : x ^ 2 + 1 / x ^ 2 > 0 := by linarith
  linarith