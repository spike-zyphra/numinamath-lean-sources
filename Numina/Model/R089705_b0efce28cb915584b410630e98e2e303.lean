import Mathlib

theorem algebra_13922 : IsLeast {4 * x ^ 2 + (x + 2 * y - 6) ^ 2 + 16 * y - 23 | (x : ℝ) (y : ℝ)} 5 := by 
  constructor 
  · -- First part: show 5 is achievable by some x and y.
    use 1, 1 / 2
    norm_num 
  · -- Show that 5 is a lower bound
    rintro z ⟨x, y, hx⟩
    have h1 : 4 * x ^ 2 + (x + 2 * y - 6) ^ 2 + 16 * y - 23 ≥ 5 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1 / 2), sq_nonneg (x - 1 + 2 * (y - 1 / 2)), sq_nonneg (2 * (x - 1) + (y - 1 / 2))]
    linarith