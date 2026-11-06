import Mathlib

theorem algebra_9533 (x : ℚ) (hx : x > 0) (h : x = 7 + 120 / (7 + 120 / (7 + 120 / x))) : x = 15 := by
  have hx1 : x ≠ 0 := by linarith
  have hx3 : 7 + 120 / x ≠ 0 := by
    have hx7 : 7 + 120 / x > 0 := by
      have hx8 : x > 0 := hx
      have hx9 : 120 / x > 0 := by apply div_pos; norm_num; assumption
      linarith [hx9]
    nlinarith [hx7]
  have hx4 : 7 + 120 / (7 + 120 / x) ≠ 0 := by
    have hx7 : 7 + 120 / x > 0 := by
      have hx8 : x > 0 := hx
      have hx9 : 120 / x > 0 := by apply div_pos; norm_num; assumption
      linarith [hx9]
    have hx71 : 120 / (7 + 120 / x) > 0 := by
      apply div_pos
      norm_num
      linarith [hx7]
    have hx72 : 7 + 120 / (7 + 120 / x) > 0 := by
      linarith [hx71]
    linarith [hx72]
  field_simp [hx1, hx3, hx4] at h ⊢
  ring_nf at h ⊢
  have h_eq : (x - 15) * (169 * x + 13520) = 0 := by
    nlinarith [sq_nonneg (x - 15), sq_nonneg (169 * x + 13520), h]
  cases' (mul_eq_zero.mp h_eq) with h5 h6
  · -- Case x - 15 = 0, so x = 15
    linarith
  · -- Case 169 * x + 13520 = 0, so x = -13520 / 169
    nlinarith [show x > 0 from hx]