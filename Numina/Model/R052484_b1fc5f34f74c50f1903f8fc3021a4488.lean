import Mathlib

theorem algebra_313597 {a b c : ℝ} (h₀ : (1 / 4) * (b - c) ^ 2 = (a - b) * (c - a)) (h₁ : a ≠ 0) :
    (b + c) / a = 2 := by
  have h2 : (b - c) ^ 2 = 4 * (a - b) * (c - a) := by
    linarith [h₀]

  have h3 : (b + c) ^ 2 = 4 * a * (b + c) - 4 * a ^ 2 := by
    nlinarith [h2]

  have h4 : (2 * a - (b + c)) ^ 2 = 0 := by
    nlinarith [h3]

  have h5 : 2 * a - (b + c) = 0 := by
    rw [sq_eq_zero_iff] at h4
    exact h4

  have h6 : b + c = 2 * a := by
    linarith

  field_simp [h₁]
  nlinarith [h6]