import Mathlib

theorem algebra_1656 {x y z a b c : ℝ} (ha : a < 0) (hb : b < 0) (hc : c < 0)
    (h : abs (x - a) + abs (y - b) + abs (z - c) = 0) : x * y * z < 0 := by
  have h1 : abs (x - a) = 0 := by
    linarith [abs_nonneg (x - a), abs_nonneg (y - b), abs_nonneg (z - c)]
  have h2 : abs (y - b) = 0 := by 
    linarith [abs_nonneg (x - a), abs_nonneg (y - b), abs_nonneg (z - c)]
  have h3 : abs (z - c) = 0 := by 
    linarith [abs_nonneg (x - a), abs_nonneg (y - b), abs_nonneg (z - c)]
  have hx : x = a := by 
    rw [abs_eq_zero] at h1
    linarith
  have hy : y = b := by 
    rw [abs_eq_zero] at h2
    linarith
  have hz : z = c := by 
    rw [abs_eq_zero] at h3
    linarith
  rw [hx, hy, hz]
  have h1 : a * b > 0 := by 
    exact mul_pos_of_neg_of_neg ha hb
  exact mul_neg_of_pos_of_neg h1 hc