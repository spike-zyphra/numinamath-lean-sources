import Mathlib

theorem algebra_1656 {x y z a b c : ℝ} (ha : a < 0) (hb : b < 0) (hc : c < 0)
    (h : abs (x - a) + abs (y - b) + abs (z - c) = 0) : x * y * z < 0 := by
  have h1 : abs (x - a) = 0 := by
    linarith [abs_nonneg (x - a), abs_nonneg (y - b), abs_nonneg (z - c)]
  have h2 : abs (y - b) = 0 := by
    linarith [abs_nonneg (x - a), abs_nonneg (y - b), abs_nonneg (z - c)]
  have h3 : abs (z - c) = 0 := by
    linarith [abs_nonneg (x - a), abs_nonneg (y - b), abs_nonneg (z - c)]
  have h4 : x - a = 0 := by
    rwa [abs_eq_zero] at h1
  have h5 : y - b = 0 := by
    rwa [abs_eq_zero] at h2
  have h6 : z - c = 0 := by
    rwa [abs_eq_zero] at h3
  have hx : x < 0 := by
    linarith
  have hy : y < 0 := by
    linarith
  have hz : z < 0 := by
    linarith
  have h7 : x * y * z < 0 := by
    have h8 : x * y > 0 := by
      apply mul_pos_of_neg_of_neg
      linarith
      linarith
    have h9 : (x * y) * z < 0 := by
      apply mul_neg_of_pos_of_neg
      linarith
      linarith
    linarith
  linarith