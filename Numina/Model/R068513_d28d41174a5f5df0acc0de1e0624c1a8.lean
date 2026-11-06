import Mathlib

theorem algebra_318622 {x : ℝ} (hx : x > 0) (h : Real.sqrt x + 1 / Real.sqrt x = 3) :
    x / (x ^ 2 + 2018 * x + 1) = 1 / 2025 := by
  have h1 : Real.sqrt x > 0 := by
    apply Real.sqrt_pos.mpr
    exact hx
  have h2 : x + 1 / x = 7 := by
    have h3 : Real.sqrt x + 1 / Real.sqrt x = 3 := h
    have h4 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)
    have h5 : Real.sqrt x * (1 / Real.sqrt x) = 1 := by
      field_simp [h1]
      <;> nlinarith
    have h6 : (Real.sqrt x + 1 / Real.sqrt x)^2 = 9 := by nlinarith [h3]
    have h7 : (Real.sqrt x + 1 / Real.sqrt x)^2 = (Real.sqrt x)^2 + 2 * (Real.sqrt x * (1 / Real.sqrt x)) + (1 / Real.sqrt x)^2 := by
      ring
    have h8 : (1 / Real.sqrt x) ^ 2 = 1 / x := by
      field_simp [h1]
      <;> nlinarith
      <;> linarith
    rw [h7] at h6
    rw [show (Real.sqrt x) ^ 2 = x by linarith [h4]] at h6
    rw [show Real.sqrt x * (1 / Real.sqrt x) = 1 by linarith [h5]] at h6
    rw [show (1 / Real.sqrt x) ^ 2 = 1 / x by linarith [h8]] at h6
    field_simp at h6 ⊢
    nlinarith
    <;> linarith
  have h10 : x ^ 2 + 1 = 7 * x := by
    have h9 : x + 1 / x = 7 := h2
    field_simp at h9 ⊢
    linarith
  have h11 : x ^ 2 + 2018 * x + 1 = 2025 * x := by
    linarith [h10]
  rw [h11]
  field_simp
  <;> nlinarith