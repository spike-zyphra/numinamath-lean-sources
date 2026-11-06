import Mathlib

theorem algebra_304676 {a : ℤ} (ha : a > 0) :
    ∃ x : ℤ, a * x ^ 2 + 2 * (2 * a - 1) * x + 4 * (a - 3) = 0 ↔ a = 1 ∨ a = 3 ∨ a = 6 ∨ a = 10 := by
  by_cases h1 : a = 1
  · -- Assume a = 1, pick x = 2.
    use 2
    rw [h1]
    norm_num
  · -- Assume a ≠ 1
    by_cases h2 : a = 3
    · -- Assume a = 3, pick x = 0.
      use 0
      rw [h2]
      norm_num
    · -- Assume a ≠ 1,3
      by_cases h3 : a = 6
      · -- Assume a = 6, pick x = -3.
        use -3
        rw [h3]
        norm_num
      · -- Assume a ≠ 1,3,6
        by_cases h4 : a = 10
        · -- Assume a = 10, pick x = -1.
          use -1
          rw [h4]
          norm_num
        · -- Assume a ≠ 1,3,6,10, pick x = 0.
          use 0
          constructor
          · -- Assume equation holds, prove right side
            intro h
            have h5 : a = 3 := by
              nlinarith
            have h6 : a ≠ 3 := by
              intro h7
              tauto
            contradiction
          · -- Assume right side holds, prove equation
            intro h
            cases h with
            | inl h1 =>
              exfalso
              tauto
            | inr h2 =>
              cases h2 with
              | inl h3 =>
                exfalso
                tauto
              | inr h4 =>
                cases h4 with
                | inl h5 =>
                  exfalso
                  tauto
                | inr h6 =>
                  exfalso
                  tauto