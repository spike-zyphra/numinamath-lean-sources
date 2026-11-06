import Mathlib

theorem algebra_280744 (a b c d : ℝ) (ha : a < 0) (hb : b < 0) (hc : c < 0) (hd : d < 0)
    (h : abs (x1 - a) + abs (x2 + b) + abs (x3 - c) + abs (x4 + d) = 0) :
    x1 * x2 / (x3 * x4) > 0 := by

  have h1 : abs (x1 - a) = 0 := by
    linarith [abs_nonneg (x1 - a), abs_nonneg (x2 + b), abs_nonneg (x3 - c), abs_nonneg (x4 + d)]
  have h2 : abs (x2 + b) = 0 := by
    linarith [abs_nonneg (x1 - a), abs_nonneg (x2 + b), abs_nonneg (x3 - c), abs_nonneg (x4 + d)]
  have h3 : abs (x3 - c) = 0 := by
    linarith [abs_nonneg (x1 - a), abs_nonneg (x2 + b), abs_nonneg (x3 - c), abs_nonneg (x4 + d)]
  have h4 : abs (x4 + d) = 0 := by
    linarith [abs_nonneg (x1 - a), abs_nonneg (x2 + b), abs_nonneg (x3 - c), abs_nonneg (x4 + d)]

  have hx1 : x1 = a := by
    rw [abs_eq_zero] at h1
    linarith

  have hx2 : x2 = -b := by
    rw [abs_eq_zero] at h2
    linarith

  have hx3 : x3 = c := by
    rw [abs_eq_zero] at h3
    linarith

  have hx4 : x4 = -d := by
    rw [abs_eq_zero] at h4
    linarith

  rw [hx1, hx2, hx3, hx4]

  have hab_pos : a * b > 0 := by 
    apply mul_pos_of_neg_of_neg
    linarith
    linarith

  have hcd_pos : c * d > 0 := by
    apply mul_pos_of_neg_of_neg
    linarith
    linarith
  
  have hpos : (a * (-b)) / (c * (-d)) > 0 := by
    have h1 : a * (-b) = -(a * b) := by ring
    have h2 : c * (-d) = -(c * d) := by ring
    rw [h1, h2]
    have h3 : -(a * b) / (-(c * d)) = (a * b) / (c * d) := by 
      field_simp
    rw [h3]
    apply div_pos
    · linarith
    · linarith

  linarith [hpos]