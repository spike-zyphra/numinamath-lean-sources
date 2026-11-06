import Mathlib

theorem algebra_137737 {a : ℕ → ℝ} (ha : ∀ n, 0 < n → a (n + 1) * 3 + a n = 0)
    (ha' : a 2 = 6) : a 1 * a 2 * a 3 * a 4 * a 5 = -32 := by
  have h1 : a 1 = -18 := by
    have eq1 := ha 1 (by norm_num)
    rw [show a 2 = 6 by linarith [ha']] at eq1
    linarith
  have h3 : a 3 = -2 := by 
    have eq1 := ha 2 (by norm_num)
    rw [show a 2 = 6 by linarith [ha']] at eq1
    linarith
  have h4 : a 4 = 2 / 3 := by 
    have eq1 := ha 3 (by norm_num)
    rw [h3] at eq1
    linarith
  have h5 : a 5 = -2 / 9 := by 
    have eq1 := ha 4 (by norm_num)
    rw [h4] at eq1
    linarith
  have h2 : a 2 = 6 := ha'
  rw [h1, h2, h3, h4, h5]
  norm_num