import Mathlib

theorem algebra_14720 : IsGreatest {err : ℝ | ∃ d : ℝ, abs d / 20 ≤ 20 / 100 ∧ err = abs ((20 + d) ^ 2 / 20 ^ 2 - 1)} (44 / 100) := by
  constructor
  · -- Show 44 / 100 is in the set
    use 4
    norm_num [abs_of_nonneg]
  · -- Show that 44 / 100 is the greatest element in the set
    intro err
    rintro ⟨d, hd, herr⟩
    have h1 : abs d / 20 ≤ (20 / 100 : ℝ) := by
      simpa using hd
    have h2 : abs d ≤ 4 := by
      have h1' : abs d / 20 ≤ (20 / 100 : ℝ) := h1
      have h2' : abs d ≤ 4 := by
        linarith [abs_nonneg d]
      linarith
    have h3 : -4 ≤ d ∧ d ≤ 4 := by
      constructor
      · -- Show -4 ≤ d
        cases abs_cases d with
        | inl h =>
          linarith
        | inr h =>
          linarith
      · -- Show d ≤ 4
        cases abs_cases d with
        | inl h =>
          linarith
        | inr h =>
          linarith
    have h4 : -44 / 100 ≤ ((20 + d) ^ 2 / (20 : ℝ) ^ 2 - 1) ∧ ((20 + d) ^ 2 / (20 : ℝ) ^ 2 - 1) ≤ 44 / 100 := by
      have h1 : -4 ≤ d := h3.1
      have h2 : d ≤ 4 := h3.2
      constructor
      · -- Show -44 / 100 ≤ ((20 + d) ^ 2 / (20 : ℝ) ^ 2 - 1)
        nlinarith [sq_nonneg (d - 4), sq_nonneg (d + 4)]
      · -- Show ((20 + d) ^ 2 / (20 : ℝ) ^ 2 - 1) ≤ 44 / 100
        nlinarith [sq_nonneg (d - 4), sq_nonneg (d + 4)]
    have h5 : abs ((20 + d) ^ 2 / (20 : ℝ) ^ 2 - 1) ≤ 44 / 100 := by
      apply abs_le.mpr
      constructor <;> linarith
    rw [herr]
    linarith [abs_le.mp h5]