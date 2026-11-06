import Mathlib

theorem algebra_313790 (a b : ℝ) (ha : a^2 + b^2 = 1) (hb : b ≠ 0)
    (h : ∃ x y, a * x + b * y = 2 ∧ x^2 / 6 + y^2 / 2 = 1) :
    a / b ≤ -1 ∨ a / b ≥ 1 := by

  rcases h with ⟨x, y, h1, h2⟩
  have eq1 : b * y = 2 - a * x := by
    have eq2 : a * x + b * y = 2 := h1
    linarith

  have eq3 : y ^ 2 = (2 - a * x) ^ 2 / b ^ 2 := by
    have eq4 : b * y = 2 - a * x := eq1
    have eq5 : y = (2 - a * x) / b := by
      field_simp [hb]
      <;> nlinarith
    rw [eq5]
    field_simp [hb]
    <;> nlinarith

  have eq6 : x ^ 2 / 6 + (2 - a * x) ^ 2 / (2 * b ^ 2) = 1 := by
    rw [eq3] at h2
    field_simp [hb] at h2 ⊢
    <;> nlinarith

  have eq7 : x ^ 2 * b ^ 2 + 3 * (2 - a * x) ^ 2 = 6 * b ^ 2 := by
    have eq8 : x ^ 2 / 6 + (2 - a * x) ^ 2 / (2 * b ^ 2) = 1 := eq6
    have eq9 : b ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 hb
    field_simp [hb, eq9] at eq8 ⊢
    <;> nlinarith [sq_pos_of_ne_zero hb]

  have h3 : 144 * a^2 - 4 * (3 * a^2 + b^2) * (12 - 6 * b^2) ≥ 0 := by
    have h4 : (3 * a^2 + b^2) * (x) ^ 2 - 12 * a * (x) + (12 - 6 * b^2) = 0 := by
      nlinarith [eq7]
    nlinarith [sq_nonneg ((3 * a^2 + b^2) * x - 6 * a), sq_nonneg (b)]

  have h4 : 3 * a^2 + b^2 - 2 ≥ 0 := by
    nlinarith [sq_nonneg (b), sq_nonneg (b - 0), sq_nonneg (a * b), sq_nonneg (x * b), sq_nonneg (x * a), sq_nonneg ((3 * a^2 + b^2) * x - 6 * a), sq_nonneg (b), sq_nonneg (x * b), sq_nonneg (x * a)]

  have h5 : 2 * a^2 - 1 ≥ 0 := by
    nlinarith [h4, ha]

  by_contra h
  push_neg at h
  have h6 : a / b > -1 := h.1
  have h7 : a / b < 1 := h.2

  by_cases h8 : b > 0
  · -- If b > 0, then from -1 < a/b < 1, we have -b < a < b.
    have h8' : a ^ 2 < b ^ 2 := by
      have hb1 : b > 0 := h8
      have h9 : a / b > -1 := h6
      have h10 : a / b < 1 := h7
      have h9' : a > -b := by
        have : a / b > -1 := h9
        apply (lt_div_iff₀ hb1).mp at this
        linarith
      have h10' : a < b := by
        have : a / b < 1 := h10
        apply (div_lt_iff₀ hb1).mp at this
        linarith
      nlinarith [sq_nonneg (a + b), sq_nonneg (b - a), sq_nonneg (a - b), sq_nonneg (a), sq_nonneg (b)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a), sq_nonneg (b), h8', h5, ha]
  · -- If b ≤ 0, then b < 0.
    have h9 : b < 0 := by
      by_contra h9
      push_neg at h9
      have h9' : b = 0 := by
        nlinarith
      contradiction

    have h10 : a ^ 2 < b ^ 2 := by
      have hb1 : b < 0 := h9
      have h9' : a / b > -1 := h6
      have h10' : a / b < 1 := h7
      have h9'' : a < -b := by
        have : a / b > -1 := h9'
        apply (lt_div_iff_of_neg' hb1).mp at this
        linarith
      have h10'' : a > b := by
        have : a / b < 1 := h10'
        apply (div_lt_iff_of_neg' hb1).mp at this
        linarith
      nlinarith [sq_nonneg (a + b), sq_nonneg (b - a), sq_nonneg (a - b), sq_nonneg (a), sq_nonneg (b)]
    nlinarith [mul_self_nonneg (a + b), mul_self_nonneg (a - b), mul_self_nonneg (b), h5, ha]