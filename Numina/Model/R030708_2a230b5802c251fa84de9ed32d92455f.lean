import Mathlib

theorem algebra_22285 {x : ℝ} (hx : x > 0) (h : x - 1/x = 3) : x + 1/x = Real.sqrt 13 := by
  have h1 : x + 1/x > 0 := by
    have hx' : x > 0 := hx
    have hx2 : 1/x > 0 := by
      apply div_pos
      norm_num
      all_goals linarith
    linarith
  have h2 : (x + 1 / x) ^ 2 = 13 := by
    have eq1 : x ^ 2 - 2 + 1 / x ^ 2 = 9 := by
      have h1' : x - 1 / x = 3 := h
      have h2' : (x - 1 / x) ^ 2 = 9 := by 
        rw [h1']
        norm_num
      have h3 : (x - 1 / x) ^ 2 = x^2 - 2 + 1 / x ^ 2 := by
        field_simp
        ring
      rw [h3] at h2'
      linarith
    have eq2 : (x + 1 / x) ^ 2 = x ^ 2 + 2 + 1 / x ^ 2 := by
      field_simp
      ring
    have eq3 : x ^ 2 + 1 / x ^ 2 = 11 := by 
      linarith [eq1]
    rw [eq2]
    linarith [eq3]
  have h3 : x + 1 / x = Real.sqrt 13 := by
    have h4 : (x + 1 / x) ^ 2 = 13 := h2
    have h5 : x + 1 / x ≥ 0 := by
      linarith [h1]
    have h6 : Real.sqrt ((x + 1 / x) ^ 2) = Real.sqrt (13) := by 
      rw [h4]
    have h7 : Real.sqrt ((x + 1 / x) ^ 2) = x + 1 / x := by
      rw [Real.sqrt_sq]
      linarith [h1]
    have h8 : (x + 1 / x) = Real.sqrt 13 := by 
      nlinarith [h6, h7]
    exact h8
  exact h3