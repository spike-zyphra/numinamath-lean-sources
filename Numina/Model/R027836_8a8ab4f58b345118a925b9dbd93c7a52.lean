import Mathlib

open Real Set

theorem algebra_17093 : IsLeast {x | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 ∧
    x = 1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a)} 3 := by
  constructor
  · -- Show 3 is in the set
    use 1 / 3, 1 / 3, 1 / 3
    all_goals norm_num
  · -- Show 3 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h0, hx⟩
    by_contra h
    push_neg at h
    have h1 : 0 < a + 2 * b := by
      nlinarith
    have h2 : 0 < b + 2 * c := by
      nlinarith
    have h3 : 0 < c + 2 * a := by
      nlinarith
    have h4 : 1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a) < 3 := by
      nlinarith [hx, h]
    have h6 : (1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a)) ≥ 3 := by
      have h7 : 0 < (a + 2 * b) * (b + 2 * c) * (c + 2 * a) := by
        positivity
      have h8 : 1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a) - 3 ≥ 0 := by
        have h9 : 1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a) - 3 =
            ((b + 2 * c) * (c + 2 * a) + (a + 2 * b) * (c + 2 * a) + (a + 2 * b) * (b + 2 * c) - 3 * (a + 2 * b) * (b + 2 * c) * (c + 2 * a)) / ((a + 2 * b) * (b + 2 * c) * (c + 2 * a)) := by 
          field_simp
          <;> ring
        rw [h9]
        apply div_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          sq_nonneg (a + b + c - 1), sq_nonneg (a + b + c - 1)]
        all_goals positivity
      linarith
    linarith [h4, h6]