import Mathlib

theorem inequalities_170299 (x : ℤ) :
    x ≠ 13 ∧ |(2 / (x - 13 : ℝ))| > 8 / 9 ↔ x = 11 ∨ x = 12 ∨ x = 14 ∨ x = 15 := by
  constructor
  · -- (→) Assume the inequality holds, prove the disjunction
    intro h
    rcases h with ⟨hx13, hineq⟩
    have h1 : x - 13 ≠ 0 := by
      intro h2
      have : x = 13 := by linarith
      tauto
    have h2 : (x : ℝ) - 13 ≠ 0 := by
      exact_mod_cast h1
    have h3 : (2 / (x - 13 : ℝ)) > 8 / 9 ∨ (2 / (x - 13 : ℝ)) < -8 / 9 := by
      cases' abs_cases (2 / (x - 13 : ℝ)) with h1 h1
      · -- The case where abs (2/(x -13)) = 2/(x -13)
        left
        linarith
      · -- the case where abs (2/(x -13)) = - (2/(x -13))
        right
        linarith
    cases h3 with
    | inl h4 =>
      -- Now considering case where 2/(x - 13) > 8/9
      have h4' : (2 : ℝ) / (x - 13 : ℝ) > (8 / 9 : ℝ) := by
        linarith
      have h5 : (x : ℝ) - 13 > 0 ∨ (x : ℝ) - 13 < 0 := by
        by_contra h
        push_neg at h
        have : (x : ℝ) - 13 = 0 := by linarith
        have h2' : (x : ℝ) - 13 = 0 := by linarith
        have : (x : ℝ) - 13 ≠ 0 := h2
        contradiction
      cases h5 with
      | inl h6 =>
        -- So h6: (x - 13 : ℝ) > 0.
        have h7 : (2 : ℝ) > (8 / 9 : ℝ) * (x - 13 : ℝ) := by
          have pos1 : (x - 13 : ℝ) > 0 := h6
          have h8 : (2 : ℝ) / (x - 13) > (8 / 9 : ℝ) := by
            linarith
          have h9 : (2 : ℝ) > (8 / 9 : ℝ) * (x - 13 : ℝ) := by
            have pos1' : (x - 13 : ℝ) > 0 := h6
            apply (lt_div_iff₀ pos1').mp at h8
            linarith
          linarith
        have h10 : (x : ℝ) < (15.25 : ℝ) := by
          nlinarith
        have h11 : x > 13 := by
          by_contra h7
          push_neg at h7
          have : (x : ℝ) ≤ (13 : ℝ) := by exact_mod_cast h7
          nlinarith
        have h12 : x < 16 := by
          by_contra h
          push_neg at h
          have : (x : ℝ) ≥ (16 : ℝ) := by exact_mod_cast h
          nlinarith
        interval_cases x <;> norm_num at h4' h6 h7 h10 h11 h12 ⊢
        <;> norm_num [abs]
        <;> tauto
      | inr h6 =>
        -- So h6: (x - 13 : ℝ) < 0.
        have h7 : (2 : ℝ) < (8 / 9 : ℝ) * (x - 13 : ℝ) := by
          have pos1 : (x - 13 : ℝ) < 0 := h6
          have h8 : (2 : ℝ) / (x - 13) > (8 / 9 : ℝ) := by
            linarith
          have h9 : (2 : ℝ) < (8 / 9 : ℝ) * (x - 13 : ℝ) := by
            have pos1' : (x - 13 : ℝ) < 0 := h6
            apply (lt_div_iff_of_neg' (by linarith)).mp at h8
            linarith
          linarith
        nlinarith
    | inr h4 =>
      -- Now considering the case where 2/(x - 13) < -8/9
      have h4' : (2 : ℝ) / (x - 13 : ℝ) < (-8 / 9 : ℝ) := by
        linarith
      have h5 : (x : ℝ) - 13 > 0 ∨ (x : ℝ) - 13 < 0 := by
        by_contra h
        push_neg at h
        have : (x : ℝ) - 13 = 0 := by linarith
        have h2' : (x : ℝ) - 13 = 0 := by linarith
        have : (x : ℝ) - 13 ≠ 0 := h2
        contradiction
      cases h5 with
      | inl h6 =>
        -- h6: (x - 13 : ℝ) > 0.
        have h7 : (2 : ℝ) < (-8 / 9 : ℝ) * (x - 13 : ℝ) := by
          have pos1 : (x - 13 : ℝ) > 0 := h6
          have h8 : (2 : ℝ) / (x - 13) < (-8 / 9 : ℝ) := by
            linarith
          have h9 : (2 : ℝ) < (-8 / 9 : ℝ) * (x - 13 : ℝ) := by
            have pos1' : (x - 13 : ℝ) > 0 := h6
            apply (div_lt_iff₀ pos1').mp at h8
            linarith
          linarith
        nlinarith
      | inr h6 =>
        -- h6: (x - 13 : ℝ) < 0.
        have h7 : (2 : ℝ) > (-8 / 9 : ℝ) * (x - 13 : ℝ) := by
          have pos1 : (x - 13 : ℝ) < 0 := h6
          have h8 : (2 : ℝ) / (x - 13) < (-8 / 9 : ℝ) := by
            linarith
          have h9 : (2 : ℝ) > (-8 / 9 : ℝ) * (x - 13 : ℝ) := by
            have pos1' : (x - 13 : ℝ) < 0 := h6
            apply (div_lt_iff_of_neg' (by linarith)).mp at h8
            linarith
          linarith
        have h11 : x > 10 := by
          by_contra h11
          push_neg at h11
          have : (x : ℝ) ≤ (10 : ℝ) := by exact_mod_cast h11
          nlinarith
        have h12 : x < 13 := by
          by_contra h12
          push_neg at h12
  -- Lean's nlinarith is powerful to solve arithmetic goals.
          have : (x : ℝ) ≥ (13 : ℝ) := by exact_mod_cast h12
          nlinarith
        interval_cases x <;> norm_num at h4' h7 h6 h11 h12 ⊢
        <;> norm_num [abs]
        <;> tauto
  · -- (←) Assume the disjunction holds, prove the inequality
    rintro (h | h | h | h)
    · -- x = 11
      rw [h]
      norm_num
      all_goals norm_num [abs]
      <;> norm_num
    · -- x = 12
      rw [h]
      norm_num
      all_goals norm_num [abs]
      <;> norm_num
    · -- x = 14
      rw [h]
      norm_num
      all_goals norm_num [abs]
      <;> norm_num
    · -- x = 15
      rw [h]
      norm_num
      all_goals norm_num [abs]
      <;> norm_num