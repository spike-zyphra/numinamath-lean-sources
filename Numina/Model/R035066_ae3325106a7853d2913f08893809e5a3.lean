import Mathlib

theorem algebra_11932 :
    IsLeast {x | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a^2 + 4 * b^2 + 9 * c^2 = 4 * b + 12 * c - 2 ∧ x = 1 / a + 2 / b + 3 / c} 6 := by
  constructor
  · -- Show 6 belongs to the set
    use 1, 1, 1
    norm_num
  · -- Show 6 is the minimum
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h_eq, hx⟩
    have h1 : a^2 + 4 * b^2 + 9 * c^2 = 4 * b + 12 * c - 2 := h_eq
    have h2 : 1 / a + 2 / b + 3 / c ≥ 6 := by
      have h3 : a * b * c > 0 := by positivity
      have h4 : 1 / a + 2 / b + 3 / c - 6 ≥ 0 := by
        have h9 : 1 / a + 2 / b + 3 / c - 6 = (b * c + 2 * (a * c) + 3 * (a * b) - 6 * (a * b * c)) / (a * b * c) := by
          field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm]
          ring
        rw [h9]
        have h7 : b * c + 2 * (a * c) + 3 * (a * b) - 6 * (a * b * c) ≥ 0 := by
          nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (c ^ 2 - 1),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
            h_eq]
        have h8 : a * b * c > 0 := by positivity
        exact div_nonneg h7 (by positivity)
      linarith
    have hx' : x = 1 / a + 2 / b + 3 / c := by linarith [hx]
    linarith [h2, hx']