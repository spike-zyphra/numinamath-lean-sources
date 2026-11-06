import Mathlib

theorem algebra_316174 {a b : ℝ} (ha : a ≥ 0) (hb : b ≥ 0)
    (h : ∀ x : ℝ, x^2 - 2 * Real.sqrt a * x + b > 0) :
    2 * Real.sqrt (b^2 + 2 * b + 1) - Real.sqrt ((a + b + 2)^2) -
    Real.sqrt ((a - b - 3)^2) = -3 := by
  have h1 : Real.sqrt a ^ 2 = a := by
    rw [Real.sq_sqrt]
    linarith
  have h2 : a < b := by
    have h' := h (Real.sqrt a)
    simp [Real.sq_sqrt, ha] at h'
    nlinarith
  have h3 : Real.sqrt (b ^ 2 + 2 * b + 1) = b + 1 := by
    have h4 : b ^ 2 + 2 * b + 1 = (b + 1) ^ 2 := by ring
    rw [h4]
    have h5 : Real.sqrt ((b + 1) ^ 2) = b + 1 := by
      rw [Real.sqrt_sq (show b + 1 ≥ 0 by linarith)]
    exact h5
  have h6 : Real.sqrt ((a + b + 2) ^ 2) = a + b + 2 := by
    rw [Real.sqrt_sq (show a + b + 2 ≥ 0 by linarith)]
  have h7 : Real.sqrt ((a - b - 3) ^ 2) = -(a - b - 3) := by
    rw [Real.sqrt_sq_eq_abs]
    have h8 : a - b - 3 < 0 := by linarith [h2]
    rw [abs_of_neg h8]
    all_goals nlinarith
  rw [h3, h6, h7]
  all_goals nlinarith