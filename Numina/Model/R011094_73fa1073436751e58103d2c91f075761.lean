import Mathlib
open Real

theorem algebra_611463 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h: a^2 + b^2 = 8*a*b): abs ((a+b)/(a-b)) = sqrt (5 / 3) := by
  have h1 : abs ((a + b) / (a - b)) = abs (a + b) / abs (a - b) := by
    field_simp [abs_div]
  rw [h1]
  have h2 : abs (a + b) = Real.sqrt ((a + b) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  have h3 : abs (a - b) = Real.sqrt ((a - b) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h2, h3]
  have h4 : (a + b) ^ 2 = 10 * (a * b) := by
    nlinarith [h]
  have h5 : (a - b) ^ 2 = 6 * (a * b) := by
    nlinarith [h]
  have h6 : (a * b) > 0 := by
    by_contra h7
    have h8 : (a * b) ≤ 0 := by linarith
    have h9 : a^2 + b^2 - 8 * a * b = 0 := by
      nlinarith
    have h10 : a^2 + b^2 ≥ 0 := by
      positivity
    have h11 : 8 * a * b ≥ 0 := by
      nlinarith [h9, h10]
    have h12 : a * b = 0 := by
      nlinarith
    have h13 : a * b = 0 := h12
    have h14 : a = 0 ∨ b = 0 := by
      cases (mul_eq_zero.mp h13) with
      | inl h15 => 
        left
        linarith
      | inr h16 => 
        right
        linarith
    cases h14 with
    | inl h15 => 
      contradiction
    | inr h16 => 
      contradiction
  have h8 : Real.sqrt ((a + b) ^ 2) / Real.sqrt ((a - b) ^ 2) = Real.sqrt ( ((a + b) ^ 2) / ((a - b) ^ 2) ) := by
    field_simp [Real.sqrt_div]
  rw [h8]
  have h10 : ((a + b) ^ 2) / ((a - b) ^ 2) = (5 / 3 : ℝ) := by
    have h11 : (a + b) ^ 2 = 10 * (a * b) := h4
    have h12 : (a - b) ^ 2 = 6 * (a * b) := h5
    rw [h11, h12]
    have h13 : (a * b) > 0 := h6
    field_simp [h13]
    <;> nlinarith
  rw [h10]
  all_goals linarith