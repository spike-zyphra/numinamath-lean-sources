import Mathlib

theorem algebra_289811 {x y z : ℝ} (h₀ : x^4 + y^2 + 4 = 5 * y * z) (h₁ : y^4 + z^2 + 4 = 5 * z * x)
    (h₂ : z^4 + x^2 + 4 = 5 * x * y) :
    (x = Real.sqrt 2 ∧ y = Real.sqrt 2 ∧ z = Real.sqrt 2) ∨
    (x = -Real.sqrt 2 ∧ y = -Real.sqrt 2 ∧ z = -Real.sqrt 2) := by

  have h3 : (x - y)^2 + (y - z)^2 + (z - x)^2 = 0 := by 
    nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (y^2 - 2), sq_nonneg (z^2 - 2),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - Real.sqrt 2), sq_nonneg (x + Real.sqrt 2),
      sq_nonneg (y - Real.sqrt 2), sq_nonneg (y + Real.sqrt 2),
      sq_nonneg (z - Real.sqrt 2), sq_nonneg (z + Real.sqrt 2),
      Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num),
      Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)
    ]

  have hx1 : x = y := by nlinarith 
  have hy1 : y = z := by nlinarith 
  have h5 : x = z := by nlinarith 
  have h4 : x^4 + x^2 + 4 = 5 * x^2 := by
    have eq1 : x^4 + y^2 + 4 = 5 * y * z := by linarith [h₀]
    rw [show y = x by linarith] at eq1 
    rw [show z = x by linarith] at eq1
    linarith 
  have h4a : x^4 - 4 * x^2 + 4 = 0 := by 
    nlinarith [h4]
  have h4b : (x^2 - 2)^2 = 0 := by 
    nlinarith [h4a]
  have h4c : x^2 - 2 = 0 := by 
    apply pow_eq_zero 
    exact h4b
  have h4d : x^2 = 2 := by
    linarith
  have h5b : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
    have h7 : x^2 = (2 : ℝ) := h4d
    have : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by 
      have h8 : x^2 - (2 : ℝ) = 0 := by linarith 
      have h9 : (x - Real.sqrt 2) * (x + Real.sqrt 2) = 0 := by 
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
      cases' (mul_eq_zero.1 h9) with h10 h11 
      · left 
        linarith 
      · right 
        linarith 
    assumption 
  cases h5b with
  | inl hx_pos =>
    -- x = Real.sqrt 2
    have hx : x = Real.sqrt 2 := hx_pos 
    have hy : y = Real.sqrt 2 := by 
      nlinarith 
    have hz : z = Real.sqrt 2 := by 
      nlinarith 
    left 
    exact ⟨hx, hy, hz⟩ 
  | inr hx_neg => 
    -- x = -Real.sqrt 2
    have hx : x = -Real.sqrt 2 := hx_neg 
    have hy : y = -Real.sqrt 2 := by 
      nlinarith 
    have hz : z = -Real.sqrt 2 := by 
      nlinarith 
    right 
    exact ⟨hx, hy, hz⟩