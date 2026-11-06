import Mathlib

open Real

theorem algebra_14549 :
    IsLeast {x : ℝ | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = a / (2 * b) + b / (4 * c) + c / (8 * a)} (3 / 4) := by
  constructor
  · -- Show that 3/4 is in the set by choosing a = 1, b = 2, c = 2
    use 1, 2, 2
    norm_num
  · -- Prove that 3/4 is the least element in the set
    intro x h
    rcases h with ⟨a, b, c, ha, hb, hc, h_eq⟩
    have h1 : a / (2 * b) + b / (4 * c) + c / (8 * a) ≥ 3 / 4 := by
      have h2 : 0 < (2 * b) := by nlinarith
      have h3 : 0 < (4 * c) := by nlinarith
      have h4 : 0 < (8 * a) := by nlinarith
      have h5 : a / (2 * b) + b / (4 * c) + c / (8 * a) - 3 / 4 ≥ 0 := by
        have h6 : a / (2 * b) + b / (4 * c) + c / (8 * a) - 3 / 4 =
            (4 * a ^ 2 * c + 2 * b ^ 2 * a + c ^ 2 * b - 6 * a * b * c) / (8 * a * b * c) := by
          field_simp
          ring
        rw [h6] at *
        have h7 : 4 * a ^ 2 * c + 2 * b ^ 2 * a + c ^ 2 * b ≥ 6 * a * b * c := by
          nlinarith [sq_nonneg (2 * a * c - b * a), sq_nonneg (2 * a - b), sq_nonneg (b - 2 * a), sq_nonneg (c - 2 * a), sq_nonneg (c - b), sq_nonneg (2 * c - 4 * a), sq_nonneg (a * (2 * a - b)), sq_nonneg ((2 * c) - (2 * b)), sq_nonneg (c * (2 * a - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        have h8 : 4 * a ^ 2 * c + 2 * b ^ 2 * a + c ^ 2 * b - 6 * a * b * c ≥ 0 := by
          linarith [h7]
        have h9 : 8 * a * b * c > 0 := by
          positivity
        apply div_nonneg
        · linarith
        all_goals positivity
      linarith
    linarith [h_eq, h1]