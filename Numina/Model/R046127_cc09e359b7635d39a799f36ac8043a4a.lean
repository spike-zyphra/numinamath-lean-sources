import Mathlib


theorem inequalities_604442 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * b * c = 1) :
    (1 / (a^3 + b * c)) + (1 / (b^3 + c * a)) + (1 / (c^3 + a * b)) ≤ (a * b + b * c + c * a)^2 / 6 := by

  have h2 : a ^ 3 + b * c ≥ 2 * a := by
    have h3 : a ^ 3 + b * c - 2 * a ≥ 0 := by
      have h4 : b * c = 1 / a := by
        field_simp
        nlinarith [h]
      rw [h4]
      have h5 : a ^ 3 + 1 / a - 2 * a ≥ 0 := by
        have h6 : a ^ 3 + 1 / a - 2 * a = (a ^ 4 + 1 - 2 * a ^ 2) / (a) := by
          field_simp
          ring
        rw [h6]
        have h7 : a ^ 4 + 1 - 2 * a ^ 2 ≥ 0 := by
          have h8 : a ^ 4 + 1 - 2 * a ^ 2 = (a ^ 2 - 1) ^ 2 := by
            nlinarith
          rw [h8]
          nlinarith [sq_nonneg (a ^ 2 - 1)]
        have h8 : a > 0 := by linarith
        positivity
      linarith
    linarith

  have h3 : b ^ 3 + c * a ≥ 2 * b := by
    have h3 : b ^ 3 + c * a - 2 * b ≥ 0 := by
      have h4 : c * a = 1 / b := by
        field_simp
        nlinarith [h]
      rw [h4]
      have h5 : b ^ 3 + 1 / b - 2 * b ≥ 0 := by
        have h6 : b ^ 3 + 1 / b - 2 * b = (b ^ 4 + 1 - 2 * b ^ 2) / (b) := by
          field_simp
          ring
        rw [h6]
        have h7 : b ^ 4 + 1 - 2 * b ^ 2 ≥ 0 := by
          have h8 : b ^ 4 + 1 - 2 * b ^ 2 = (b ^ 2 - 1) ^ 2 := by
            nlinarith
          rw [h8]
          nlinarith [sq_nonneg (b ^ 2 - 1)]
        have h8 : b > 0 := by linarith
        positivity
      linarith
    linarith

  have h4 : c ^ 3 + a * b ≥ 2 * c := by
    have h3 : c ^ 3 + a * b - 2 * c ≥ 0 := by
      have h4 : a * b = 1 / c := by
        field_simp
        nlinarith [h]
      rw [h4]
      have h5 : c ^ 3 + 1 / c - 2 * c ≥ 0 := by
        have h6 : c ^ 3 + 1 / c - 2 * c = (c ^ 4 + 1 - 2 * c ^ 2) / (c) := by
          field_simp
          ring
        rw [h6]
        have h7 : c ^ 4 + 1 - 2 * c ^ 2 ≥ 0 := by
          have h8 : c ^ 4 + 1 - 2 * c ^ 2 = (c ^ 2 - 1) ^ 2 := by
            nlinarith
          rw [h8]
          nlinarith [sq_nonneg (c ^ 2 - 1)]
        have h8 : c > 0 := by linarith
        positivity
      linarith
    linarith

  have h5 : (1 / (a^3 + b * c)) ≤ 1 / (2 * a) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith [h2]

  have h6 : (1 / (b^3 + c * a)) ≤ 1 / (2 * b) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith [h3]

  have h7 : (1 / (c^3 + a * b)) ≤ 1 / (2 * c) := by
    apply one_div_le_one_div_of_le
    positivity
    linarith [h4]

  have h8 : (1 / (a^3 + b * c)) + (1 / (b^3 + c * a)) + (1 / (c^3 + a * b)) ≤ (1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c)) := by
    linarith [h5, h6, h7]

  have h9 : (1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c)) = (a * b + b * c + c * a) / 2 := by
    have h10 : a * b * c = 1 := h
    field_simp [show 0 < a from ha, show 0 < b from hb, show 0 < c from hc]
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, mul_pos (show 0 < a * b from mul_pos ha hb) hc, sq_nonneg (a * b * c - 1)]

  have h10 : a * b + b * c + c * a ≥ 3 := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      sq_nonneg (a * b * c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, mul_pos (show 0 < a * b from mul_pos ha hb) hc, h]

  have h11 : (a * b + b * c + c * a) / 2 ≤ (a * b + b * c + c * a)^2 / 6 := by
    nlinarith [sq_nonneg (a * b + b * c + c * a - 3), h10]

  have h12 : (1 / (a^3 + b * c)) + (1 / (b^3 + c * a)) + (1 / (c^3 + a * b)) ≤ (a * b + b * c + c * a)^2 / 6 := by
    nlinarith [h8, h9, h11]

  exact h12