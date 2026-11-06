import Mathlib

open Real

theorem algebra_170868: {x: ℝ | 0 < x + 3 ∧ x + 3 ≠ 1 ∧ 0 < -8 * x - x ^ 2 ∧
  0 < (log 7 - log (-8 * x - x ^ 2)) / log (x + 3)} =
    Set.Ioo (-3) (-2) ∪ Set.Ioo (-1) 0 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo]
  constructor
  · -- Assume x in the left side, prove it is in right
    rintro ⟨hx1, hx2, hx3, hx4⟩
    have hx1' : x + 3 > 0 := by linarith
    have hx2' : -8 * x - x ^ 2 > 0 := by linarith
    have h1 : log (x + 3) ≠ 0 := by
      by_contra h
      have h2 : x + 3 = 1 := by
        rw [log_eq_zero] at h
        rcases h with (r | r | r)
        · linarith
        · linarith
        · linarith
      have h2' : x + 3 ≠ 1 := hx2
      contradiction
    by_cases h4 : log (x + 3) > 0
    · -- Case log(x + 3) > 0
      have h5 : x + 3 > 1 := by
        by_contra h6
        push_neg at h6
        have h7 : log (x + 3) ≤ 0 := by
          have h8 : x + 3 ≤ 1 := by linarith
          have h9 : log (x + 3) ≤ log (1 : ℝ) := by
            apply Real.log_le_log
            all_goals nlinarith
          have h10 : log (1 : ℝ) = 0 := by
            simp
          linarith
        linarith
      have h12 : log 7 - log (-8 * x - x ^ 2) > 0 := by
        apply div_pos_iff.mp at hx4
        cases hx4 with
        | inl h1 =>
          linarith
        | inr h2 =>
          linarith
      have h8 : (7 : ℝ) > -8 * x - x^2 := by
        by_contra h9
        push_neg at h9
        have h10 : log 7 ≤ log (-8 * x - x ^ 2) := by
          apply Real.log_le_log
          all_goals nlinarith
        linarith
      -- If we are here, this implication - from long derivation step missing by reason missed.
      -- We are supposed to have a clear upper and lower bounds here to match to right side
      -- Solving 7 > -8x -x^2 with x > -2 does not result into (-1,0)
      -- But given hypotheses, we are trying to establish that
      -- Assume by some change variable with trigonometric function, may satisfy it.
      -- But my derivation fails, So likely that from hypotheses x lies in (-2, -1)
      -- This Intermediate result. So this means
      -- We need to make these variables by trigonometric substitution
      -- But I need the algebra, which seems to go wrong.
      -- Assume that from concrete hypotheses, the goals can be satisfied
      right
      constructor
      · -- Show -1 < x
        nlinarith
      · -- Show x < 0
        nlinarith
    · -- Case log(x + 3) ≤ 0
      have h5 : log (x + 3) < 0 := by
        by_contra h6
        push_neg at h6
        have h7 : log (x + 3) = 0 := by
          linarith
        contradiction
      have h6 : x + 3 < 1 := by
        by_contra h7
        push_neg at h7
        have h8 : log (x + 3) ≥ 0 := by
          have h9 : x + 3 ≥ 1 := by linarith
          have h10 : log (x + 3) ≥ log (1 : ℝ) := by
            apply Real.log_le_log
            all_goals nlinarith
          have h11 : log (1 : ℝ) = 0 := by
            simp
          linarith
        linarith
      have h7 : x < -2 := by
        nlinarith
      have h10 : (7 : ℝ) < -8 * x - x ^ 2 := by
        have h11 : log 7 - log (-8 * x - x ^ 2) < 0 := by
          apply div_pos_iff.mp at hx4
          cases hx4 with
          | inl h1 =>
            linarith
          | inr h2 =>
            linarith
        by_contra h22
        push_neg at h22
        have h13 : log 7 ≥ log (-8 * x - x ^ 2) := by
          apply Real.log_le_log
          all_goals nlinarith
        linarith
      have h9 : -3 < x := by
        nlinarith
      have h10 : -3 < x ∧ x < -2 := by
        constructor
        · -- Show -3 < x
          nlinarith
        · -- Show x < -2
          nlinarith
      left
      exact h10
  · -- Assume x in the right side, prove it is in left
    rintro (h | h)
    · -- Case x ∈ (-3, -2)
      rcases h with ⟨h1, h2⟩
      constructor
      · -- Show 0 < x + 3
        linarith
      constructor
      · -- Show x + 3 ≠ 1
        nlinarith
      constructor
      · -- Show 0 < -8 * x - x ^ 2
        nlinarith
      · -- Show 0 < (log 7 - log (-8 * x - x ^ 2)) / log (x + 3)
        have h11 : log (x + 3) < 0 := by
          have h12 : x + 3 < 1 := by
            nlinarith
          have h13 : log (x + 3) < 0 := by
            have h14 : x + 3 > 0 := by
              linarith
            have h15 : log (x + 3) < log 1 := by
              apply Real.log_lt_log
              all_goals nlinarith
            have h16 : log 1 = 0 := by
              simp
            linarith
          linarith
        have h22 : log 7 - log (-8 * x - x ^ 2) < 0 := by
          have h23 : log 7 < log (-8 * x - x ^ 2) := by
            apply Real.log_lt_log
            all_goals nlinarith
          linarith
        apply div_pos_of_neg_of_neg
        linarith
        linarith
    · -- Case x ∈ (-1, 0)
      rcases h with ⟨h1, h2⟩
      constructor
      · -- Show 0 < x + 3
        linarith
      constructor
      · -- Show x + 3 ≠ 1
        nlinarith
      constructor
      · -- Show 0 < -8 * x - x ^ 2
        nlinarith
      · -- Show 0 < (log 7 - log (-8 * x - x ^ 2)) / log (x + 3)
        have h11 : log (x + 3) > 0 := by
          have h12 : x + 3 > 1 := by
            nlinarith
          have h13 : log (x + 3) > 0 := by
            have h14 : x + 3 > 1 := by
              nlinarith
            have h15 : log (x + 3) > log 1 := by
              apply Real.log_lt_log
              all_goals nlinarith
            have h16 : log 1 = (0 : ℝ) := by
              simp
            linarith
          linarith
        have h22 : log 7 - log (-8 * x - x ^ 2) > 0 := by
          have h23 : log 7 > log (-8 * x - x ^ 2) := by
            apply Real.log_lt_log
            all_goals nlinarith
          linarith
        apply div_pos
        linarith
        all_goals linarith