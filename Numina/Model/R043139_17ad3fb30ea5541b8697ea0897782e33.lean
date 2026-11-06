import Mathlib

theorem algebra_198005 (x : ℝ) (hx : x > 0) (h : 60 / 100 + 5 = x / (1 - 5 / x)) :
    x = 20 := by
  have h1 : x - 5 ≠ 0 := by
    by_contra h2
    have h2 : x = 5 := by linarith
    rw [h2] at h
    norm_num at h
    all_goals try { nlinarith }
  have h2 : (1 - 5 / x) ≠ 0 := by
    by_contra h3
    have h3 : 1 - 5 / x = 0 := h3
    have h4 : 5 / x = 1 := by linarith
    have h5 : x = 5 := by
      field_simp at h4
      all_goals linarith
    exfalso
    apply h1
    linarith
  have h3 : (60 / 100 + (5 : ℝ)) * (x - 5) = x^2 := by
    have eq1 : (1 - 5 / x) = (x - 5) / x := by 
      field_simp [show x ≠ 0 by linarith]
      <;> nlinarith
    have eq2 : x / (1 - 5 / x) = x^2 / (x - 5) := by
      rw [eq1]
      field_simp [(show x ≠ 0 by linarith), h1]
      <;> nlinarith
    have eq4 : (60 / 100 + (5 : ℝ)) = (28 / 5 : ℝ) := by norm_num
    have eq6 : (60 / 100 + (5 : ℝ)) = (28 / 5 : ℝ) := eq4
    have eq7 : x / (1 - 5 / x) = x^2 / (x - 5) := eq2
    have h6 : (28 / 5 : ℝ) * (x - 5) = x^2 := by 
      have h : (60 / 100 + (5 : ℝ)) = x / (1 - 5 / x) := by linarith [h]
      rw [eq6] at h
      rw [eq7] at h
      have h7 : x - 5 ≠ 0 := h1
      field_simp [(show x ≠ 0 by linarith), h7] at h ⊢
      <;> nlinarith [sq_nonneg (x - 5), sq_nonneg (x ^ 2)]
    linarith
  have h4 : (5 * x ^ 2 - 28 * x + 140 : ℝ) = 0 := by 
    have h5 : (28 / 5 : ℝ) * (x - 5) = x^2 := by linarith [h3]
    linarith
  have h5 : (5 * x ^ 2 - 28 * x + 140 : ℝ) > 0 := by
    nlinarith [sq_nonneg (x - (14 / 5) : ℝ), sq_nonneg (x - 5 : ℝ), mul_pos hx (show (0 : ℝ) < 1 by linarith), sq_pos_of_pos hx]
  linarith