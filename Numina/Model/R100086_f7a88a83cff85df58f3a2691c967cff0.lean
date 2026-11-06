import Mathlib

theorem algebra_2991 (x t : ℝ) (ht : t = 1 / 3) (hx1 : x ≥ 0) (hx2 : 1 / 2 / 2 + 1 / 2 / x = t) : x = 6 := by
  rw [ht] at hx2
  have h1 : x ≠ 0 := by
    by_contra h
    rw [h] at hx2
    norm_num at hx2
    all_goals try { nlinarith }

  field_simp [h1] at hx2
  have h2 : x > 0 := by
    nlinarith [h1, hx1]
  
  nlinarith [sq_nonneg (x - 6), sq_nonneg (x + 6), sq_nonneg (x), sq_nonneg (x - 6)]