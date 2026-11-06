import Mathlib

theorem algebra_2690 {x : ℝ} (hx : x ≠ 0) (h : x^2 + 1/x^2 = 3) :
    x^3 + 1/x^3 = 2*Real.sqrt 5 ∨ x^3 + 1/x^3 = -2*Real.sqrt 5 := by
  have h1 : (x + 1 / x) ^ 2 = 5 := by
    have h1 : x^2 + 1 / x^2 = (x + 1 / x) ^ 2 - 2 := by
      field_simp
      ring
    rw [h1] at h
    nlinarith

  have h2 : x + 1 / x = Real.sqrt 5 ∨ x + 1 / x = -Real.sqrt 5 := by
    have h3 : (x + 1 / x) ^ 2 = (Real.sqrt 5) ^ 2 := by
      linarith [h1, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    have h4 : x + 1 / x = Real.sqrt 5 ∨ x + 1 / x = -Real.sqrt 5 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      all_goals nlinarith [Real.sqrt_nonneg 5]
    exact h4

  cases h2 with
  | inl h3 =>
    have h4 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      field_simp
      ring

    rw [h4, h3]

    have h5 : (Real.sqrt 5 : ℝ) ^ 3 = 5 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5 : ℝ) ^ 3 = (Real.sqrt 5 : ℝ) ^ 2 * (Real.sqrt 5 : ℝ) := by ring
        _ = 5 * (Real.sqrt 5 : ℝ) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

    have h6 : 5 * Real.sqrt 5 - 3 * Real.sqrt 5 = 2 * Real.sqrt 5 := by
      ring

    left
    nlinarith [h5, h6]

  | inr h3 =>
    have h4 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      field_simp
      ring

    rw [h4, h3]

    have h5 : (-Real.sqrt 5 : ℝ) ^ 3 = -5 * Real.sqrt 5 := by
      calc
        (-Real.sqrt 5 : ℝ) ^ 3 = -((Real.sqrt 5 : ℝ) ^ 3) := by ring
        _ = -(5 * (Real.sqrt 5 : ℝ)) := by rw [show (Real.sqrt 5 : ℝ) ^ 3 = 5 * (Real.sqrt 5 : ℝ) by
          calc
            (Real.sqrt 5 : ℝ) ^ 3 = (Real.sqrt 5 : ℝ) ^ 2 * (Real.sqrt 5 : ℝ) := by ring
            _ = 5 * (Real.sqrt 5 : ℝ) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
          ]
        _ = -5 * (Real.sqrt 5 : ℝ) := by ring

    have h6 : -5 * Real.sqrt 5 - 3 * (-Real.sqrt 5) = -2 * Real.sqrt 5 := by
      ring

    right
    nlinarith [h5, h6]