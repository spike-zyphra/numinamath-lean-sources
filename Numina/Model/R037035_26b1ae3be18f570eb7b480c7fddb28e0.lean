import Mathlib

theorem algebra_194382 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : 228 / x = y + 5) (h2 : 180 / y = x - 90 / 100) :
    x + y = 85 := by
  have eq1 : x * (y + 5) = 228 := by
    field_simp at h1 ⊢
    nlinarith
    <;> nlinarith [h1, sq_pos_of_pos hx, sq_pos_of_pos hy]
          -- negatives cannot happen according to hx
  have eq2 : y * (x - 90 / 100) = 180 := by
    field_simp at h2 ⊢
    nlinarith
    <;> nlinarith [h2, sq_pos_of_pos hx, sq_pos_of_pos hy]
  nlinarith [sq_nonneg (x - 35/2), sq_nonneg (y - 35/2), sq_nonneg (x - 28), sq_nonneg (y - 57), sq_nonneg (x - 9), sq_nonneg (y - 9),
            sq_nonneg (x * (x - 9)), sq_nonneg (y * (y - 9)), mul_pos hx hy]