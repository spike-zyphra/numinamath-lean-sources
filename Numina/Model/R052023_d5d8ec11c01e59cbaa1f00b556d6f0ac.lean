import Mathlib

theorem algebra_5016 {x : ℝ} (hx : x > 0) (h : x + 1/x = 5) :
    2 * x ^ 2 + 2 / x ^ 2 = 46 := by 
  have h1 : x ≠ 0 := by
    linarith
  have h2 : x ^ 2 + 1 / x ^ 2 = 23 := by
    have h3 : x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by
      field_simp [h1]
      <;> ring 
    rw [h3, h]
    norm_num 
  have h4 : 2 * x ^ 2 + 2 / x ^ 2 = 2 * (x ^ 2 + 1 / x ^ 2) := by 
    ring_nf 
  rw [h4, h2]
  all_goals norm_num