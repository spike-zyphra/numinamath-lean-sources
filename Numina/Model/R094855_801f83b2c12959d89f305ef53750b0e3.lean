import Mathlib

theorem algebra_320106 {x : ℝ} (hx : x ≠ 0) (h : x - 1 / x = Real.sqrt 5) :
    x + 1 / x = 3 ∨ x + 1 / x = -3 := by
  have h1 : (x - 1 / x)^2 = 5 := by
    rw [h]
    have : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by linarith)
    linarith

  have h2 : x^2 + 1 / x^2 = 7 := by
    have eq1 : (x - 1 / x) ^ 2 = x^2 - 2 + 1 / x^2 := by
      field_simp [hx]
      ring
    rw [eq1] at h1
    have eq2 : x^2 + 1 / x^2 = 7 := by
      linarith
    linarith [eq2]

  have h3 : (x + 1 / x)^2 = 9 := by
    have eq3 : (x + 1 / x)^2 = x^2 + 2 + 1 / x^2 := by
      field_simp [hx]
      ring
    rw [eq3]
    have eq4 : x^2 + 1 / x^2 = 7 := by
      linarith [h2]
    nlinarith

  have h4 : x + 1 / x = 3 ∨ x + 1 / x = -3 := by
    have h5 : (x + 1 / x) ^ 2 = 9 := by
      linarith [h3]
    have h6 : (x + 1 / x - 3) * (x + 1 / x + 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · left
      linarith
    · right
      linarith

  exact h4