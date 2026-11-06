import Mathlib

theorem algebra_305824 {x : ℝ} (hx : x ≠ 0) (h : x - 1/x = Real.sqrt 3) :
    x^5 + 1/x^5 = 19*Real.sqrt 7 ∨ x^5 + 1/x^5 = -19*Real.sqrt 7 := by
  have h1 : x^2 + 1/x^2 = 5 := by 
    have eq1 : x^2 + 1/x^2 = (x - 1/x) ^2 + 2 := by
      field_simp [hx]
      <;> nlinarith 
    rw [eq1, h]
    have h2 : (Real.sqrt 3 : ℝ) ^2 = 3 := Real.sq_sqrt (by linarith)
    linarith [h2]
  have h2 : (x + 1/x) ^2 = 7 := by 
    have eq1 : (x + 1/x) ^2 = x^2 + 1/x^2 + 2 := by 
      field_simp [hx]
      <;> nlinarith 
    rw [eq1, h1]
    <;> linarith 
  have h3 : x + 1/x = Real.sqrt 7 ∨ x + 1/x = -Real.sqrt 7 := by 
    have eq : (x + 1/x) ^2 - 7 = 0 := by 
      linarith [h2]
    have eq2 : (x + 1/x - Real.sqrt 7) * (x + 1/x + Real.sqrt 7) = 0 := by
      nlinarith [eq, Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by linarith)]
    cases (mul_eq_zero.mp eq2) with
    | inl h4 => 
      left 
      linarith 
    | inr h5 => 
      right 
      linarith 
  have h4 : x^3 + 1 / x^3 = (x + 1/x) ^3 - 3 * (x + 1/x) := by
    field_simp [hx]
    <;> nlinarith 
  have h5 : x^4 + 1 / x^4 = (x^2 + 1/x^2)^2 - 2 := by
    field_simp [hx]
    <;> nlinarith 
  have h6 : x^4 + 1 / x^4 = 23 := by
    rw [h5, h1]
    all_goals nlinarith 
  have h7 : x^5 + 1 / x^5 = (x + 1/x) * (x^4 + 1/x^4) - (x^3 + 1/x^3) := by 
    field_simp [hx]
    <;> nlinarith 
  rcases h3 with h3 | h3 
  · -- Assume x + 1/x = Real.sqrt 7 
    have h8 : x ^3 + 1 / x ^3 = Real.sqrt 7 * 4 := by 
      rw [h4, h3]
      ring_nf <;> nlinarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by linarith)]
    have h9 : x ^5 + 1 / x ^5 = Real.sqrt 7 * 19 := by 
      rw [h7, h8, h6, h3]
      nlinarith 
      <;> nlinarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by linarith)]
    left 
    linarith [h9]
  · -- Assume x + 1/x = -Real.sqrt 7 
    have h8 : x ^3 + 1 / x ^3 = -Real.sqrt 7 * 4 := by 
      rw [h4, h3]
      ring_nf <;> nlinarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by linarith)]
    have h9 : x ^5 + 1 / x ^5 = -Real.sqrt 7 * 19 := by 
      rw [h7, h8, h6, h3]
      nlinarith 
    right 
    linarith [h9]