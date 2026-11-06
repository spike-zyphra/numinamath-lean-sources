import Mathlib

theorem algebra_12322 (a : ℝ) (h : a ≠ 0) (r : ℝ) (hr : r = -1 / 3) (hsum : ∑' n : ℕ, a * r ^ n = 25) :
    a * r = -100 / 9 := by 
  have h1 : ∑' n : ℕ, a * r ^ n = a / (1 - r) := by 
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring_nf
    · rw [hr]
      norm_num [abs_lt]
      all_goals norm_num [abs_lt]
  rw [h1] at hsum
  rw [hr] at hsum 
  have ha : a = 100 / 3 := by 
    field_simp at hsum ⊢
    linarith 
  rw [ha, hr]
  norm_num