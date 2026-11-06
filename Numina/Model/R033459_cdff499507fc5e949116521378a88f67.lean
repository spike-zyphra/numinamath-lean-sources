import Mathlib

theorem algebra_327249 (a b : ℝ) (h : ∃ x : ℝ, x ≠ 0 ∧ x^2 + a * x + 1 / x^2 + a / x + b + 2 = 0) :
    a^2 + b^2 ≥ 16 / 5 := by
  rcases h with ⟨x, hx1, heq⟩
  have eq1 : x^4 + a * x^3 + (b + 2) * x^2 + a * x + 1 = 0 := by
    have eq2 : x^2 + a * x + 1 / x^2 + a / x + b + 2 = 0 := heq
    have h2 : x ≠ 0 := hx1
    have eq3 : x^4 + a * x^3 + (b + 2) * x^2 + a * x + 1 = 0 := by
      have eq4 : x^2 + a * x + 1 / x^2 + a / x + b + 2 = 0 := eq2
      have eq5 : (x^2 + a * x + 1 / x^2 + a / x + b + 2) * x^2 = 0 := by 
        rw [eq4]
        all_goals norm_num
      have eq6 : (x^2 + a * x + 1 / x^2 + a / x + b + 2) * x^2 = x^4 + a * x^3 + (b + 2) * x^2 + a * x + 1 := by
        field_simp [h2]
        <;> ring
      rw [eq6] at eq5 
      all_goals linarith 
    linarith 
  have eq2 : (x + 1 / x) ^ 2 + a * (x + 1 / x) + b = 0 := by 
    have eq1' : x^4 + a * x^3 + (b + 2) * x^2 + a * x + 1 = 0 := eq1 
    have h2 : x ≠ 0 := hx1 
    have eq5 : (x^4 + a * x^3 + (b + 2) * x^2 + a * x + 1) / x^2 = 0 := by 
      have eq1' : x^4 + a * x^3 + (b + 2) * x^2 + a * x + 1 = 0 := eq1
      have h2 : x^2 ≠ 0 := by 
        exact pow_ne_zero 2 hx1 
      field_simp [h2] at *
      <;> nlinarith 
    have hne : x^2 ≠ 0 := by 
      exact pow_ne_zero 2 hx1 
    field_simp [hne] at eq5 ⊢ 
    <;> nlinarith [sq_nonneg (x^2 -1), sq_nonneg (x +1)]
  have h3 : (x +1/x)^2 ≥4 := by 
    have h4 : x^2 +1/x^2 ≥2 := by 
      have h5 : x^2 +1/x^2 -2 ≥0 := by 
        have h6 : x^2 +1/x^2 -2 = (x -1/x)^2 := by 
          field_simp [hx1] 
          <;> ring 
        rw [h6] 
        positivity 
      linarith 
    have h7 : (x+1/x)^2 =x^2+1/x^2+2 := by 
      field_simp [hx1] 
      <;> ring 
    linarith [h7, h4] 
  have eq4 : a^2 -4*b ≥0 := by 
    nlinarith [sq_nonneg (a+2*(x+1/x)), sq_nonneg (x+1/x), h3] 
  nlinarith [sq_nonneg (a -8/5), sq_nonneg (b -4/5), 
      sq_nonneg (a +8/5), sq_nonneg (b +4/5), 
      sq_nonneg (x^2 -1), sq_nonneg (x^2+1/x^2 -4), 
      h3, sq_nonneg ((x^2 -1)*(x^2-1)), 
      sq_nonneg (a - 2*(x+1/x)), sq_nonneg (a + 2*(x+1/x))
      ]