import Mathlib

theorem algebra_214569 (x1 x2 : ℝ) (y1 y2 : ℝ)
    (h1 : x1^2 + y1 = 12) (h2 : x2^2 + y2 = 12) (h3 : x1 + y1 = 12) (h4 : x2 + y2 = 12)
    (h5 : x1 ≠ x2) :
    Real.sqrt ((x2 - x1)^2 + (y2 - y1)^2) = Real.sqrt 2 := by
  have eq1 : y1 = 12 - x1 := by linarith
  have eq2 : y2 = 12 - x2 := by linarith
  rw [eq1] at h1
  rw [eq2] at h2
  have eq3 : x1^2 - x1 = 0 := by linarith
  have eq4 : x2^2 - x2 = 0 := by linarith
  have h6 : x1 = 0 ∨ x1 = 1 := by
    have h7 : x1 * (x1 - 1) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h7) with
    | inl h8 => 
      left
      linarith
    | inr h9 =>
      right
      linarith
  have h7 : x2 = 0 ∨ x2 = 1 := by
    have h8 : x2 * (x2 - 1) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h8) with
    | inl h9 => 
      left
      linarith
    | inr h10 =>
      right
      linarith
  cases h6 with
  | inl hx1 =>
    cases h7 with
    | inl hx2 =>
      exfalso
      exact h5 (by linarith)
    | inr hx2 =>
      have h8 : (x2 - x1) ^ 2 + (y2 - y1) ^ 2 = (2 : ℝ) := by
        rw [show y1 = (12 : ℝ) by linarith, show y2 = (11 : ℝ) by linarith]
        rw [show x1 = (0 : ℝ) by linarith, show x2 = (1 : ℝ) by linarith]
        norm_num
      rw [h8]
  | inr hx1 =>
    cases h7 with
    | inl hx2 =>
      have h8 : (x2 - x1) ^ 2 + (y2 - y1) ^ 2 = (2 : ℝ) := by
        rw [show y1 = (11 : ℝ) by linarith, show y2 = (12 : ℝ) by linarith]
        rw [show x1 = (1 : ℝ) by linarith, show x2 = (0 : ℝ) by linarith]
        norm_num
      rw [h8]
    | inr hx2 =>
      exfalso
      exact h5 (by linarith)