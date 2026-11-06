import Mathlib

theorem algebra_13314 {x : ℕ} (hx : x ≠ 0) (h : (10 / 15 : ℝ) * 24 = x) : x = 16 := by 
  have h1 : (x : ℝ) = (10 / 15 : ℝ) * 24 := by 
    linarith [h]
  have h2 : (x : ℝ) = 16 := by
    norm_num at h1 ⊢
    linarith
  have h3 : x = 16 := by
    exact_mod_cast h2
  exact h3