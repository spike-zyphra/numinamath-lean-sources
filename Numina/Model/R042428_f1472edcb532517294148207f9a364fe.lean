import Mathlib

theorem algebra_47858 {x y : ℝ} (hx : x > 0) (hy : y > 0) (h : (x + y) / 2 / Real.sqrt (x * y) = 25 / 24) :
    x / y = 9 / 16 ∨ x / y = 16 / 9 := by 
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : Real.sqrt (x * y) > 0 := by positivity

  have h3 : (x + y) / 2 / Real.sqrt (x * y) = 25 / 24 := h
  have h4 : (x + y) / (2 * Real.sqrt (x * y)) = 25 / 24 := by
    field_simp at h3 ⊢
    <;> nlinarith [Real.sqrt_nonneg (x * y)]
  have h5 : 24 * (x + y) = 50 * Real.sqrt (x * y) := by
    field_simp [show (2 : ℝ) * Real.sqrt (x * y) ≠ 0 by positivity, show (24 : ℝ) ≠ 0 by norm_num] at h4 ⊢
    nlinarith [Real.sqrt_nonneg (x * y)]
  have h6 : 12 * (x + y) = 25 * Real.sqrt (x * y) := by
    linarith

  have h7 : (12 * (x + y)) ^ 2 = (25 * Real.sqrt (x * y)) ^ 2 := by 
    rw [h6]
  have h8 : 144 * (x + y) ^ 2 = 625 * (x * y) := by
    calc
      144 * (x + y) ^ 2 = (12 * (x + y)) ^ 2 := by
        ring_nf
      _ = (25 * Real.sqrt (x * y)) ^ 2 := by
        rw [h7]
      _ = 625 * (Real.sqrt (x * y) ^ 2) := by
        ring_nf
      _ = 625 * (x * y) := by
        rw [Real.sq_sqrt (by positivity)]
        all_goals linarith
  have h9 : 144 * (x ^ 2 + 2 * x * y + y ^ 2) = 625 * (x * y) := by 
    have h10 : 144 * (x + y) ^ 2 = 625 * (x * y) := h8
    have h11 : 144 * (x + y) ^ 2 = 144 * (x ^ 2 + 2 * x * y + y ^ 2) := by ring
    linarith [h11, h8]
  have h10 : 144 * x ^ 2 - 337 * x * y + 144 * y ^ 2 = 0 := by
    linarith [h9]
  have h11 : (x / y - 9 / 16) * (x / y - 16 / 9) = 0 := by
    have eq1 : 144 * x ^ 2 - 337 * x * y + 144 * y ^ 2 = 0 := h10
    have eq2 : y ≠ 0 := by positivity
    have eq3 : (x / y - 9 / 16) * (x / y - 16 / 9) = 0 := by
      field_simp at *
      nlinarith
    assumption
  cases' (mul_eq_zero.mp h11) with h12 h13
  · left
    field_simp at h12 ⊢
    all_goals nlinarith
  · right
    field_simp at h13 ⊢
    all_goals nlinarith