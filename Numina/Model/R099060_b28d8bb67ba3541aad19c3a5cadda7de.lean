import Mathlib

theorem algebra_262183 {x y : ℝ} (h : x ≠ -y) (h1 : (x - y) / (x + y) = 5) :
    (2 * x + 3 * y) / (3 * x - 2 * y) = 0 := by
  have h2 : x + y ≠ 0 := by
    intro h3
    have h4 : x = -y := by linarith
    rw [show x = -y by linarith] at h
    exfalso
    exact h rfl
  have h3 : x - y = 5 * (x + y) := by
    have denom_ne_zero : x + y ≠ 0 := h2
    have h3 : (x - y) / (x + y) = 5 := h1
    field_simp [denom_ne_zero] at h3
    linarith
  have h5 : 2 * x + 3 * y = 0 := by 
    linarith [h3]
  have h6 : 3 * x - 2 * y ≠ 0 := by
    by_contra h7
    have h7 : 3 * x - 2 * y = 0 := by linarith
    have h9 : y = 0 := by
      linarith [h5, h7]
    have h10 : x = 0 := by
      linarith [h9, h3]
    have h11 : x + y = 0 := by linarith [h9, h10]
    have h12 : x + y ≠ 0 := h2
    contradiction
  rw [h5]
  field_simp [h6]