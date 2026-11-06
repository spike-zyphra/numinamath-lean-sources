import Mathlib

theorem algebra_6907 {x : ℝ} (hx : x > 0) (h : x^2 + 1/x^2 = 7) :
    x + 1/x = 3 := by
  have h1 : (x + 1/x)^2 = 9 := by
    have h2 : x ≠ 0 := by linarith
    have h3 : (x + 1/x)^2 = x^2 + 1/x^2 + 2 := by
      field_simp [h2]
      <;> ring
    rw [h3, h]
    all_goals norm_num
  have h2 : x + 1/x > 0 := by
    have hx1 : x > 0 := hx
    have hx2 : 1/x > 0 := by
      apply div_pos
      norm_num
      all_goals linarith
    linarith
  have h3 : x + 1/x = 3 := by
    nlinarith
  exact h3