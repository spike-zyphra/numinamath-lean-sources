import Mathlib
/-The parabola y = 4 * a * x^2 + 4 * (a + 1) * x + a^2 + a + 3 + 1 / a (a≠ 0)  intersects the x-axis at two points. In which direction do the branches of this parabola point - upwards or downwards?-/
theorem algebra_289560 (a : ℝ) (ha : a ≠ 0) (h : ∃ x1 x2, x1 ≠ x2 ∧
    4 * a * x1^2 + 4 * (a + 1) * x1 + a^2 + a + 3 + 1 / a = 0 ∧
    4 * a * x2^2 + 4 * (a + 1) * x2 + a^2 + a + 3 + 1 / a = 0) :
    a < 0 := by
  rcases h with ⟨x1, x2, hx12, h1, h2⟩
 -- show the key relation --
  have h_eq : 4 * a * (x1 + x2) + 4 * (a + 1) = 0 := by
    have h1_eq : 4 * a * x1^2 + 4 * (a + 1) * x1 + a^2 + a + 3 + 1 / a = 0 := h1
    have h2_eq : 4 * a * x2^2 + 4 * (a + 1) * x2 + a^2 + a + 3 + 1 / a = 0 := h2
    have h_sub : 4 * a * (x1^2 - x2^2) + 4 * (a + 1) * (x1 - x2) = 0 := by
      have h : 4 * a * x1^2 + 4 * (a + 1) * x1 + a^2 + a + 3 + 1 / a - (4 * a * x2^2 + 4 * (a + 1) * x2 + a^2 + a + 3 + 1 / a) = 0 := by
        linarith
      field_simp at h
      nlinarith
    have h_ne : x1 - x2 ≠ 0 := by exact sub_ne_zero.mpr hx12
    have h_eq : 4 * a * (x1 + x2) + 4 * (a + 1) = 0 := by
      apply (mul_left_inj' h_ne).mp
      linarith [h_sub]
    linarith
  -- here we show the final result --
  have h3 : a < 0 := by
    have eq1 : 4 * a * x1^2 + 4 * (a + 1) * x1 + a^2 + a + 3 + 1 / a = 0 := h1
    have eq2 : 4 * a * x2^2 + 4 * (a + 1) * x2 + a^2 + a + 3 + 1 / a = 0 := h2
    have h_eq1 : a^3 + a < 0 := by
      have eq1' : 4 * a^2 * x1^2 + 4 * a * (a + 1) * x1 + a^3 + a^2 + 3 * a + 1 = 0 := by
        have h1_eq : 4 * a * x1^2 + 4 * (a + 1) * x1 + a^2 + a + 3 + 1 / a = 0 := h1
        have h1_mul : a ≠ 0 := ha
        field_simp at h1_eq
        nlinarith
      have eq2' : 4 * a^2 * x2^2 + 4 * a * (a + 1) * x2 + a^3 + a^2 + 3 * a + 1 = 0 := by
        have h2_eq : 4 * a * x2^2 + 4 * (a + 1) * x2 + a^2 + a + 3 + 1 / a = 0 := h2
        have h2_mul : a ≠ 0 := ha
        field_simp at h2_eq
        nlinarith
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by exact sub_ne_zero.mpr hx12),
        sq_nonneg (x1 + x2), sq_nonneg (x1 - x2),
        sq_nonneg (x1 + (a + 1) / (2 * a)), sq_nonneg (x2 + (a + 1) / (2 * a))]
    have h4 : a * (a^2 + 1) < 0 := by nlinarith
    have h5 : a < 0 := by
      have h6 : a^2 + 1 > 0 := by
        nlinarith [sq_nonneg a]
      have h7 : a < 0 := by
        apply mul_neg_iff.mp at h4
        cases h4 with
        | inl h8 =>
          nlinarith
        | inr h9 =>
          nlinarith
      exact h7
    linarith
  exact h3