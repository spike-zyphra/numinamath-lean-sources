import Mathlib

theorem algebra_240778 {x : ℝ} (hx : x > 0) (h1 : (1 / x) * (1 + 3 / x) = 75 / 100 * (1 / x)) (h2 : (1 / x) * (1 - 3 / x) > 1 / x) :
    x = 5 / 3 := by
  have h3 : (1 + 3 / x) = 75 / 100 := by 
    have h4 : x ≠ 0 := by linarith
    field_simp at h1 ⊢
    nlinarith
  have h4 : 3 / x < 0 := by 
    nlinarith
  have h5 : 3 / x > 0 := by
    apply div_pos
    all_goals linarith
  linarith