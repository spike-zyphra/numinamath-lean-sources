import Mathlib

theorem algebra_20425 (x : ℕ → ℝ) (hx1 : x 1 = 97) (hxn : ∀ n > 1, x n = n / x (n - 1)) :
    x 1 * x 2 * x 3 * x 4 * x 5 * x 6 * x 7 * x 8 = 384 := by
  have h2 : x 2 = 2 / 97 := by
    specialize hxn 2 (by norm_num)
    rw [hxn, hx1]
    all_goals norm_num
  have h3 : x 3 = 3 * 97 / 2 := by
    specialize hxn 3 (by norm_num)
    rw [hxn, h2]
    all_goals norm_num
  have h4 : x 4 = 8 / 291 := by
    specialize hxn 4 (by norm_num)
    rw [hxn, h3]
    all_goals norm_num
  have h5 : x 5 = 1455 / 8 := by
    specialize hxn 5 (by norm_num)
    rw [hxn, h4]
    all_goals norm_num
  have h6 : x 6 = 48 / 1455 := by
    specialize hxn 6 (by norm_num)
    rw [hxn, h5]
    all_goals norm_num
  have h7 : x 7 = 3395 / 16 := by
    specialize hxn 7 (by norm_num)
    rw [hxn, h6]
    all_goals norm_num
  have h8 : x 8 = 128 / 3395 := by
    specialize hxn 8 (by norm_num)
    rw [hxn, h7]
    all_goals norm_num
  rw [hx1, h2, h3, h4, h5, h6, h7, h8]
  all_goals norm_num