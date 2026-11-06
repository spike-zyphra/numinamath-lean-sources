import Mathlib

theorem algebra_286347 {x : ℝ} (hx : x > 0) (h : x^2 + 1 / x^2 = 7) :
    x^5 + 1 / x^5 = 123 := by
  have h1 : x + 1 / x = 3 := by
    have h2 : (x + 1 / x) ^ 2 = 9 := by
      have h3 : (x + 1 / x) ^ 2 = x^2 + 1 / x^2 + 2 := by
        field_simp
        ring
      rw [h3, h]
      all_goals linarith
    have h4 : x + 1 / x > 0 := by
      have hx1 : x > 0 := hx
      have hx2 : 1 / x > 0 := by
        apply div_pos
        norm_num
        linarith
      have hx3 : x + 1 / x > 0 := by linarith [hx1, hx2]
      linarith
    have h5 : x + 1 / x = 3 := by nlinarith
    exact h5
  have h3 : x^3 + 1 / x^3 = 18 := by
    have h2 : x^3 + 1 / x^3 = (x + 1 / x) * (x^2 + 1 / x^2) - (x + 1 / x) := by
      field_simp
      ring
    rw [h2, h1, h]
    all_goals nlinarith
  have h4 : x^4 + 1 / x^4 = 47 := by
    have h5 : x^4 + 1 / x^4 = (x + 1 / x) * (x^3 + 1 / x^3) - (x^2 + 1 / x^2) := by
      field_simp
      ring
    rw [h5, h1, h3, h]
    all_goals nlinarith
  have h5 : x^5 + 1 / x^5 = 123 := by
    have h6 : x^5 + 1 / x^5 = (x + 1 / x) * (x^4 + 1 / x^4) - (x^3 + 1 / x^3) := by
      field_simp
      ring
    rw [h6, h1, h4, h3]
    all_goals nlinarith
  exact h5