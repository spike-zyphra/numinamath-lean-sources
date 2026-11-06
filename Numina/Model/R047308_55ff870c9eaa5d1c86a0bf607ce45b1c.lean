import Mathlib
open Real
theorem inequalities_171099 : {x : ℝ | (x ^ 3 + 3 * x ^ 2 - x - 3) / (x ^ 2 + 3 * x - 10) < 0} =
{x | x < -5 ∨ x ∈ Set.Ioo (-3) (-1) ∨ x ∈ Set.Ioo 1 2}:= by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo]
  constructor
  · -- Assume h : (x ^ 3 + 3 * x ^ 2 - x - 3) / (x ^ 2 + 3 * x - 10) < 0
    intro h
    have h1 : (x ^ 3 + 3 * x ^ 2 - x - 3) / (x ^ 2 + 3 * x - 10) < 0 := h
    have h2 : (x ^ 2 + 3 * x - 10) ≠ 0 := by 
      by_contra h2
      rw [h2] at h1
      norm_num at h1
    have h3 : ((x ^ 3 + 3 * x ^ 2 - x - 3) > 0 ∧ (x ^ 2 + 3 * x - 10) < 0) ∨ 
            ((x ^ 3 + 3 * x ^ 2 - x - 3) < 0 ∧ (x ^ 2 + 3 * x - 10) > 0) := by
      apply div_neg_iff.mp at h1 
      tauto
    rcases h3 with (h3 | h3)
    · -- Case N > 0 ∧ D < 0 
      -- so x ∈ ((-3, -1) ∪ (1, 2))
      have h4 : (x ^ 3 + 3 * x ^ 2 - x - 3) > 0 := h3.1
      have h5 : (x ^ 2 + 3 * x - 10) < 0 := h3.2
      have h6 : (1 < x ∧ x < 2) ∨ (-3 < x ∧ x < -1) := by
        have h7 : -5 < x ∧ x < 2 := by
          constructor
          · -- Show -5 < x
            nlinarith [h5]
          · -- Show x < 2
            nlinarith [h5]
        rcases h7 with ⟨h8, h9⟩
        by_cases h10 : x > 1
        · -- Assume 1 < x
          left
          constructor <;> nlinarith
        · -- Assume ¬(1 < x), so x ≤ 1
          have h11 : x ≤ 1 := by linarith
          have h6' : -3 < x ∧ x < -1 := by
            have h10 : x < -1 := by
              nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 3), sq_nonneg (x - 1), sq_nonneg (x^2), 
                sq_nonneg (x + 3), sq_nonneg (x^2 - 1)]
            have h8 : -3 < x := by
              nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 3), sq_nonneg (x - 1), sq_nonneg (x^2), 
                sq_nonneg (x + 3), sq_nonneg (x^2 - 1)]
            exact ⟨h8, h10⟩
          right
          exact h6'
      rcases h6 with (h6 | h6)
      · -- Case 1 < x ∧ x < 2
        right
        right
        exact h6
      · -- Case -3 < x ∧ x < -1
        right
        left
        exact h6
    · -- Case N < 0 ∧ D > 0 
      -- so x < -5 
      have h4 : (x ^ 3 + 3 * x ^ 2 - x - 3) < 0 := h3.1
      have h5 : (x ^ 2 + 3 * x - 10) > 0 := h3.2
      have h7 : x < -5 := by
        by_contra h
        push_neg at h
        have h8 : x ≥ -5 := by nlinarith
        -- contradiction
        have h6 : (x ^ 3 + 3 * x ^ 2 - x - 3) ≥ 0 := by
          nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 3), sq_nonneg (x + 5), 
            sq_nonneg (x - 2), sq_nonneg (x^2)]
        linarith
      left 
      linarith
  · -- Show the reverse direction 
    intro h
    rcases h with (h | h | h)
    · -- Case 1
      have h1 : x < -5 := h
      have h7 : (x ^ 3 + 3 * x ^ 2 - x - 3) < 0 := by
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 3), sq_nonneg (x + 5), 
          sq_nonneg (x - 2), sq_nonneg (x^2)]
      have h8 : (x ^ 2 + 3 * x - 10) > 0 := by 
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 3), sq_nonneg (x + 5), 
          sq_nonneg (x - 2), sq_nonneg (x^2)]
      apply div_neg_of_neg_of_pos
      all_goals linarith
    · -- Case 2
      rcases h with ⟨h1, h2⟩
      have h7 : (x ^ 3 + 3 * x ^ 2 - x - 3) > 0 := by
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 3), sq_nonneg (x + 5), 
          sq_nonneg (x - 2), sq_nonneg (x^2)]
      have h8 : (x ^ 2 + 3 * x - 10) < 0 := by 
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 3), sq_nonneg (x + 5), 
          sq_nonneg (x - 2), sq_nonneg (x^2)]
      apply div_neg_of_pos_of_neg 
      all_goals linarith
    · -- Case 3
      rcases h with ⟨h1, h2⟩
      have h7 : (x ^ 3 + 3 * x ^ 2 - x - 3) > 0 := by 
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 3), sq_nonneg (x + 5), 
          sq_nonneg (x - 2), sq_nonneg (x^2)]
      have h8 : (x ^ 2 + 3 * x - 10) < 0 := by 
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 3), sq_nonneg (x + 5), 
          sq_nonneg (x - 2), sq_nonneg (x^2)]
      apply div_neg_of_pos_of_neg 
      all_goals linarith