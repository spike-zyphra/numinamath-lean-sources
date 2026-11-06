import Mathlib

theorem algebra_289811 {x y z : ℝ} (h₀ : x^4 + y^2 + 4 = 5 * y * z) (h₁ : y^4 + z^2 + 4 = 5 * z * x)
    (h₂ : z^4 + x^2 + 4 = 5 * x * y) :
    (x = Real.sqrt 2 ∧ y = Real.sqrt 2 ∧ z = Real.sqrt 2) ∨
    (x = -Real.sqrt 2 ∧ y = -Real.sqrt 2 ∧ z = -Real.sqrt 2) := by
  -- add all three equation we get (x^4+y^4+z^4+3*(x^2+y^2+x^2)=5*(x*y+y*z+z*x))
  have h3 : x^4 + y^4 + z^4 + x^2 + y^2 + z^2 + 12 = 5 * (y * z + z * x + x * y) := by
    nlinarith
  have h4 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h5 : x^2 + y^2 + z^2 ≥ y * z + z * x + x * y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h6 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (y^2 - 2), sq_nonneg (z^2 - 2),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h3, h5, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h7 : x = y := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h8 : y = z := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h9 : x = z := by linarith
  have h10 : x^2 = 2 := by
    have eq1 := h₀
    have eq2 := h₁
    have eq3 := h₂
    rw [show y = x by linarith] at eq1
    rw [show z = x by linarith] at eq1
    nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (x - Real.sqrt 2), sq_nonneg (x + Real.sqrt 2),
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hx : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
    have h : x^2 = 2 := h10
    have h1 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      norm_num
      linarith
    exact h1
  cases hx with
  | inl hx_pos =>
    have hy : y = Real.sqrt 2 := by linarith [h7, hx_pos]
    have hz : z = Real.sqrt 2 := by linarith [h9, hx_pos]
    left
    exact ⟨hx_pos, hy, hz⟩
  | inr hx_neg =>
    have hy : y = -Real.sqrt 2 := by linarith [h7, hx_neg]
    have hz : z = -Real.sqrt 2 := by linarith [h9, hx_neg]
    right
    exact ⟨hx_neg, hy, hz⟩