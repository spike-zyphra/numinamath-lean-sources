import Mathlib

theorem algebra_289884 (a r : ℚ) (ha : 0 < a) (hr : 0 < r) (h1 : a > a * r)
    (h2 : a + a * r = 15 / 2) (h3 : a ^ 2 + (a * r) ^ 2 = 153 / 4) :
    a * r ^ 4 = 3 / 128 := by

  have h4 : r < 1 := by
    have h5 : a > 0 := by exact_mod_cast ha
    have h6 : a * r < a := by nlinarith
    have h7 : r < 1 := by
      nlinarith [show a > 0 by linarith]
    linarith

  have h5 : a * (a * r) = 9 := by
    have h5 : a ^ 2 + (a * r) ^ 2 = 153 / 4 := h3
    have h6 : a + a * r = 15 / 2 := h2
    have h7 : (a + a * r) ^ 2 = 225 / 4 := by
      rw [h6]
      norm_num
    have h8 : a ^ 2 + (a * r) ^ 2 = (a + a * r) ^ 2 - 2 * (a * (a * r)) := by ring
    rw [h8] at h5
    nlinarith [h7, h5]

  have h7 : r = 1 / 4 := by
    have h8 : 4 * r ^ 2 - 17 * r + 4 = 0 := by
      nlinarith [sq_pos_of_pos ha, sq_nonneg (a - 6), sq_nonneg (r - 1 / 4), 
        h1, h4]
    have h9 : (r - 4) * (r - 1 / 4) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- r=4, which contradicts r<1
      have h12 : r = 4 := by linarith
      linarith [show r < (1 : ℚ) from by linarith, h12]
    · -- r=1/4
      linarith

  have ha2 : a = 6 := by
    rw [h7] at h2
    nlinarith

  rw [ha2, h7]
  norm_num