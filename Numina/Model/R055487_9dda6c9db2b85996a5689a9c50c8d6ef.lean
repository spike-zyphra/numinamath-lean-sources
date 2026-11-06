import Mathlib

theorem algebra_3420 {x : ℝ} (hx : x > 0) (h : x + 1 / x = 11) :
    Real.sqrt x - 1 / Real.sqrt x = 3 ∨ Real.sqrt x - 1 / Real.sqrt x = -3 := by
  have h1 : Real.sqrt x > 0 := by
    apply Real.sqrt_pos.2
    linarith
  have eq1 : (Real.sqrt x - 1 / Real.sqrt x) ^ 2 = 9 := by
    have h3 : (Real.sqrt x - 1 / Real.sqrt x) ^ 2 = (Real.sqrt x) ^ 2 - 2 * (Real.sqrt x * (1 / Real.sqrt x)) + (1 / Real.sqrt x) ^ 2 := by
      ring
    rw [h3]
    have h4 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show x ≥ 0 by linarith)
    have h5 : (1 / Real.sqrt x) ^ 2 = 1 / x := by
      have h6 : (Real.sqrt x) > 0 := h1
      field_simp [h6]
      <;> nlinarith [Real.sq_sqrt (show x ≥ 0 by linarith)]
    have h7 : Real.sqrt x * (1 / Real.sqrt x) = 1 := by
      have h6 : (Real.sqrt x) > 0 := h1
      field_simp [h6]
    rw [h4, h5, h7]
    field_simp [show x ≠ 0 by linarith] at h ⊢
    nlinarith
  have h6 : Real.sqrt x - 1 / Real.sqrt x = 3 ∨ Real.sqrt x - 1 / Real.sqrt x = -3 := by
    have h6 : (Real.sqrt x - 1 / Real.sqrt x) ^ 2 - 9 = 0 := by linarith
    have h7 : (Real.sqrt x - 1 / Real.sqrt x - 3) * (Real.sqrt x - 1 / Real.sqrt x + 3) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h7) with
    | inl h8 =>
      left
      linarith
    | inr h9 =>
      right
      linarith
  exact h6