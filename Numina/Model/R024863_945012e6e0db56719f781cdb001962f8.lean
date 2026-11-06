import Mathlib

theorem algebra_199693 {x y : ℝ} (h1 : x + x * y + x * y ^ 2 = -21) (h2 : y + x * y + x ^ 2 * y = 14) (h3 : x + y = -1) :
    (x, y) = (-3, 2) := by 
  have h4 : y = -1 - x := by
    linarith
  rw [h4] at h1 h2
  have eq1 : x ^ 3 + x ^ 2 + x + 21 = 0 := by
    nlinarith
  have eq2 : x ^ 3 + 2 * x ^ 2 + 2 * x + 15 = 0 := by
    nlinarith
  have h5 : x ^ 2 + x - 6 = 0 := by
    nlinarith [eq1, eq2]
  have h6 : (x + 3) * (x - 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case $x + 3 = 0$
    have hx1 : x = -3 := by linarith
    have hy1 : y = 2 := by 
      rw [hx1] at h4
      linarith
    simp [hx1, hy1]
    all_goals linarith
  · -- Case $x - 2 = 0$
    have hx2 : x = 2 := by linarith
    have hy2 : y = -3 := by 
      rw [hx2] at h4
      linarith
    exfalso
    rw [hx2] at h1 h2
    norm_num at h1 h2