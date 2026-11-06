import Mathlib

theorem algebra_2481 {a b c d x : ℝ} (h₀ : a = -b) (h₁ : c * d = -1) (h₂ : abs x = 2 * (-x)) : x ^ 3 + a * b * c * d * x + a - b * c * d = 0 := by
  have h3 : x ≤ 0 := by
    cases le_or_lt 0 x with
    | inl h4 =>
      have h4' : abs x = x := abs_of_nonneg (show 0 ≤ x by linarith)
      rw [h4'] at h₂
      linarith
    | inr h5 =>
      have h5' : abs x = -x := abs_of_neg h5
      rw [h5'] at h₂
      linarith
  have h4 : x = 0 := by
    cases le_or_lt 0 x with
    | inl h5 =>
      have h5' : abs x = x := abs_of_nonneg (show 0 ≤ x by linarith)
      rw [h5'] at h₂
      linarith
    | inr h6 =>
      have h6' : abs x = -x := abs_of_neg h6
      rw [h6'] at h₂
      linarith
  have hx : x = 0 := h4
  rw [hx]
  have h5 : a = -b := h₀
  have h6 : c * d = -1 := h₁
  have eq1 : a - b * c * d = 0 := by
    have eq2 : b * c * d = -b := by
      calc
        b * c * d = b * (c * d) := by ring
        _ = b * (-1) := by rw [h6]
        _ = -b := by ring
    have eq3 : a - b * c * d = a - (-b) := by
      rw [show b * c * d = -b by
        calc
          b * c * d = b * (c * d) := by ring
          _ = b * (-1) := by rw [h6]
          _ = -b := by ring
      ]
    have eq4 : a + b = 0 := by
      linarith [h₀]
    rw [eq3]
    linarith [eq4]
  simp [hx, h₀, h₁, eq1]
  <;> nlinarith [h₀, h₁, hx, eq1]