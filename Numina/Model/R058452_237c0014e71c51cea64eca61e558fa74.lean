import Mathlib

theorem algebra_21220 {x y : ℝ} (hx : -1 < x) (hy : x < y) (h1 : y < 1)
    (G G' : ℝ) (hG : G = x / (1 - y)) (hG' : G' = y / (1 - x)) (hG1 : G = G') :
    x + y = 1 := by
  rw [hG, hG'] at hG1
  have h2 : 1 - y ≠ 0 := by linarith
  have h3 : 1 - x ≠ 0 := by linarith
  field_simp [h2, h3] at hG1
  have h4 : (y - x) * (x + y - 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h4) with hy1 hy2
  · -- Case 1: y - x = 0, which implies y = x, but we know x < y
    linarith
  · -- Case 2: x + y - 1 = 0, which implies x + y = 1
    linarith