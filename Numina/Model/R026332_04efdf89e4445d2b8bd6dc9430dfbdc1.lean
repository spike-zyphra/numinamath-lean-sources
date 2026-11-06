import Mathlib

theorem algebra_300260 {x y z : ℝ}
    (h₀ : x^4 + y^2 + 4 = 5 * y * z)
    (h₁ : y^4 + z^2 + 4 = 5 * z * x)
    (h₂ : z^4 + x^2 + 4 = 5 * x * y) :
    x + y + z = 3 * Real.sqrt 2 ∨ x + y + z = -3 * Real.sqrt 2 := by
  have h3 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (y^2 - 2), sq_nonneg (z^2 - 2),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h4 : x = y := by
    nlinarith
  have h5 : y = z := by
    nlinarith
  have h6 : x = z := by
    linarith
  have h7 : z = x := by
    linarith
  have h8 : x ^ 4 + x ^ 2 + 4 = 5 * x ^ 2 := by
    rw [show y = x by linarith [h4]] at h₀
    rw [show z = x by linarith [h7]] at h₀
    nlinarith
  have h9 : x^4 - 4 * x^2 + 4 = 0 := by
    nlinarith
  have h10 : (x^2 - 2)^2 = 0 := by
    nlinarith
  have h11 : x^2 - 2 = 0 := by
    apply pow_eq_zero 
    exact h10
  have h12 : x^2 = 2 := by
    linarith
  have h13 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
    have h14 : x^2 = (2 : ℝ) := h12
    have h15 : x ^ 2 = (2 : ℝ) := h14
    have h16 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      norm_num
      linarith
    tauto
  cases h13 with
  | inl h14 =>
    have h15 : y = Real.sqrt 2 := by
      nlinarith [h4, h14]
    have h16 : z = Real.sqrt 2 := by
      nlinarith [h5, h15]
    left
    have h17 : x + y + z = 3 * Real.sqrt 2 := by
      nlinarith [h14, h15, h16]
    linarith [h17]
  | inr h14 =>
    have h15 : y = -Real.sqrt 2 := by
      nlinarith [h4, h14]
    have h16 : z = -Real.sqrt 2 := by
      nlinarith [h5, h15]
    right
    have h17 : x + y + z = -3 * Real.sqrt 2 := by
      nlinarith [h14, h15, h16]
    linarith [h17]