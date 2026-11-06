import Mathlib

theorem number_theory_323958 (x : ℤ) :
    ∃ q : ℚ, 1 + 5 * 2 ^ x = q ^ 2 ↔ x = -2 ∨ x = 4 := by
  by_cases h : x = -2
  · -- Case x = -2. Then q = 3/2
    use (3 / 2 : ℚ)
    simp [h]
    all_goals norm_num
    all_goals norm_num
  · -- Case x = 4. Then q = 9
    by_cases h2 : x = 4
    · -- Case x = 4. Then q = 9
      use (9 : ℚ)
      simp [h2]
      <;> norm_num
    · -- Case x ≠ -2 and x ≠ 4
      use (0 : ℚ)
      have h1 : x ≠ -2 := by
        intro h2
        tauto
      have h2 : x ≠ 4 := by
        intro h3
        tauto
      constructor
      · -- Assume 1 + 5 * 2 ^ x = (0 : ℚ) ^ 2, prove x = -2 ∨ x = 4
        intro h_eq
        have h_eq' : (1 + 5 * (2 : ℚ) ^ x) = (0 : ℚ) := by
          simpa using h_eq
        have h_gt : (1 + 5 * (2 : ℚ) ^ x) > 0 := by
          have h1 : (2 : ℚ) ^ x > 0 := by positivity
          nlinarith
        nlinarith
      · -- Assume x = -2 ∨ x = 4, prove 1 + 5 * 2 ^ x = (0 : ℚ) ^ 2
        intro h_eq
        cases h_eq with
        | inl h_eq =>
          exfalso
          apply h1
          all_goals
            linarith
        | inr h_eq =>
          exfalso
          apply h2
          all_goals
            linarith