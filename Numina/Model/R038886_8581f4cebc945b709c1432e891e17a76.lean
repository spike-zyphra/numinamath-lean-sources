import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_244609 {a : ℝ} (ha : a ≠ 0) :
    (∃ x y, x > 0 ∧ y > 0 ∧ x ≠ y ∧ a * logb 5 x ^ 2 - (2 * a + 5) * logb 5 x + 10 = 0 ∧
      a * logb 5 y ^ 2 - (2 * a + 5) * logb 5 y + 10 = 0 ∧ x = 5 * y) ↔
    a = 5 / 3 ∨ a = 5 := by
  constructor
  · -- Assume the existence of x, y
    rintro ⟨x, y, hx, hy, hxy, h1, h2, h3⟩
    have h4 : logb 5 x = logb 5 (5 * y) := by
      rw [show logb 5 x = logb 5 (5 * y) by rw [h3]]
    have h5 : logb 5 x = 1 + logb 5 y := by
      rw [h4]
      simp [logb_mul, hy.ne.symm]
    have h6 : a * (logb 5 y) ^ 2 - (2 * a + 5) * (logb 5 y) + 10 = 0 := by 
      linarith [h2]
    have h7 : a * (logb 5 y) ^ 2 - 5 * (logb 5 y) - a + 5 = 0 := by 
      have h8 : a * (logb 5 x) ^ 2 - (2 * a + 5) * (logb 5 x) + 10 = 0 := h1
      have h9 : logb 5 x = 1 + logb 5 y := h5
      rw [h9] at h8
      linarith
    -- Solving the two equations:
    -- From h6: a * (logb 5 y) ^ 2 - (2 * a + 5) * (logb 5 y) + 10 = 0
    -- From h7: a * (logb 5 y) ^ 2 - 5 * (logb 5 y) - a + 5 = 0
    -- Subtracting h7 from h6: (-2a - 5) * logb 5 y + 10 + 5 * logb 5 y + a - 5 = 0 => -2a * logb 5 y + a + 5 = 0 => logb 5 y = (a + 5) / (2a)
    -- Substitute into h7: a * ((a + 5) / (2 * a)) ^ 2 - 5 * ((a + 5) / (2 * a)) - a + 5 = 0 => multiply by 2a: $\frac{(a + 5)^2}{2} - 5(a + 5) - 2a^2 + 10a = 0$ => $-3a^2 + 20a - 25 = 0$ => $3a^2 - 20a + 25 = 0$ gives a = 5 or a = 5/3
    have h8 : logb 5 y = (a + 5) / (2 * a) := by
      have eq1 := h7
      have eq2 := h6
      field_simp at eq1 eq2 ⊢
      ring_nf at eq1 eq2 ⊢
      nlinarith [sq_pos_of_ne_zero ha]
    rw [h8] at h7
    have : (a - 5) * (a - 5 / 3) = 0 := by
      field_simp at h7 ⊢
      ring_nf at h7 ⊢
      nlinarith [sq_pos_of_ne_zero ha, sq_nonneg (a * 3 - 5)]
    cases' (mul_eq_zero.mp this) with h10 h11
    · -- case a - 5 = 0
      right
      linarith
    · -- case a - 5 / 3 = 0
      left
      linarith
  · -- Assume a = 5/3 or a = 5
    rintro (ha | ha)
    · -- Case a = 5/3
      rw [ha]
      use 125, 25
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · -- Check equation for x = 125
        have h1 : logb 5 (125 : ℝ) = 3 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        rw [h1]
        norm_num
      constructor
      · -- Check equation for y = 25
        have h2 : logb 5 (25 : ℝ) = 2 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        rw [h2]
        norm_num
      · norm_num
    · -- Case a = 5
      rw [ha]
      use 25, 5
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · -- Check equation for x = 25
        have h1 : logb 5 (25 : ℝ) = 2 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        rw [h1]
        norm_num
      constructor
      · -- Check equation for y = 5
        have h2 : logb 5 (5 : ℝ) = 1 := by
          rw [logb_self_eq_one]
          all_goals norm_num
        rw [h2]
        norm_num
      · norm_num