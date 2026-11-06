import Mathlib

theorem algebra_15868 : IsLeast {x | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + 2 * b = 1 ∧ x = 1 / a + 2 / b} 9 := by
  constructor
  · -- Show 9 is in the set
    use 1 / 3, 1 / 3
    norm_num
  · -- Show no value less than 9 is in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h1, heq⟩
    have h2 : 1 / a + 2 / b ≥ 9 := by
      have h3 : a + 2 * b = 1 := h1
      have h4 : 0 < a * b := by
        nlinarith
      have h5 : b + 2 * a ≥ 9 * (a * b) := by
        nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), 
          sq_nonneg (a - b), h1, mul_pos ha hb, mul_pos ha (show 0 < 1 - a by nlinarith)]
      have h7 : 0 < a * b := h4
      have h8 : 1 / a + 2 / b - 9 ≥ 0 := by
        have h9 : 1 / a + 2 / b - 9 = (b + 2 * a - 9 * (a * b)) / (a * b) := by
          field_simp
          <;> ring
        rw [h9]
        have h10 : 0 < a * b := h4
        have h11 : b + 2 * a - 9 * (a * b) ≥ 0 := by linarith [h5]
        have h12 : (b + 2 * a - 9 * (a * b)) / (a * b) ≥ 0 := by
          apply div_nonneg 
          linarith
          all_goals nlinarith
        linarith
      linarith
    linarith [heq, h2]