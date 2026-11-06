import Mathlib

theorem algebra_225862 {a b c : ℝ} (ha : a * b * c = 1) (h : a + b + c = 1 / a + 1 / b + 1 / c) :
    ({a, b, c} : Set ℝ) ∩ ({1} : Set ℝ) ≠ ∅ := by
  have h1 : a ≠ 0 := by
    by_contra h1
    have h2 : a * b * c = 0 := by
      rw [h1]
      norm_num
    linarith
  have h2 : b ≠ 0 := by
    by_contra h2
    have h3 : a * b * c = 0 := by
      rw [h2]
      norm_num
    linarith
  have h3 : c ≠ 0 := by
    by_contra h3
    have h4 : a * b * c = 0 := by
      rw [h3]
      norm_num
    linarith
  -- Now also written h4 differently
  -- Let's clear reciprocal terms in h by mul with a,b,c
  have h4 : a + b + c = (b * c + a * c + a * b) / (a * b * c) := by
    rw [h]
    -- Simplify reciprocal expressions with a,b,c non zero.
    field_simp [h1, h2, h3]
    <;> nlinarith
  -- Now that h4 can use given
  have h5 : a + b + c = b * c + a * c + a * b := by
    rw [h4]
    -- Substituting h4 and h5
    rw [show a * b * c = 1 by linarith [ha]]
    field_simp [h1, h2, h3]
    <;> nlinarith
  have h6 : (a - 1) * (b - 1) * (c - 1) = 0 := by
    nlinarith [ha, h5]
  cases' (mul_eq_zero.mp h6) with h7 h8
  cases' (mul_eq_zero.mp h7) with h9 h10
  · -- h9: a - 1 = 0.
    have h11 : a = 1 := by linarith
    simp [h11]
  · -- h10: b - 1 = 0.
    have h12 : b = 1 := by linarith
    simp [h12]
  · -- h8: c - 1 = 0.
    have h13 : c = 1 := by linarith
    simp [h13]