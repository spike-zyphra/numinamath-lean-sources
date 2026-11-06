import Mathlib

theorem algebra_319201 :
    IsLeast {x : ℝ | ∃ a b : ℝ, x = max (max (|2 * a + b|) (|2 * a - b|)) (|1 - b|)} (1 / 2) := by
  constructor
  · -- Show that 1/2 is in the set
    use (0 : ℝ), (1 / 2 : ℝ)
    norm_num [abs_of_pos, abs_of_neg]
    <;> norm_num [abs_of_pos, abs_of_neg]
    <;> norm_num [abs_of_pos, abs_of_neg]
  · -- Show that for any x in the set, 1/2 ≤ x
    rintro x ⟨a, b, hx⟩
    by_contra h
    push_neg at h
    have h1 : max (max (|2 * a + b|) (|2 * a - b|)) (|1 - b|) < (1 / 2 : ℝ) := by
      linarith [h, hx]
    have h2 : |2 * a + b| < (1 / 2 : ℝ) := by
      have h3 : |2 * a + b| ≤ max (max (|2 * a + b|) (|2 * a - b|)) (|1 - b|) := by
        simp
      have h4 : max (max (|2 * a + b|) (|2 * a - b|)) (|1 - b|) < (1 / 2 : ℝ) := by
        linarith
      linarith
    have h3 : |2 * a - b| < (1 / 2 : ℝ) := by
      have h4 : |2 * a - b| ≤ max (max (|2 * a + b|) (|2 * a - b|)) (|1 - b|) := by
        simp
      have h5 : max (max (|2 * a + b|) (|2 * a - b|)) (|1 - b|) < (1 / 2 : ℝ) := by
        linarith
      linarith
    have h4 : |1 - b| < (1 / 2 : ℝ) := by
      have h5 : |1 - b| ≤ max (max (|2 * a + b|) (|2 * a - b|)) (|1 - b|) := by
        simp
      have h6 : max (max (|2 * a + b|) (|2 * a - b|)) (|1 - b|) < (1 / 2 : ℝ) := by
        linarith
      linarith
    have h5 : 1 / 2 < b := by
      linarith [abs_lt.mp h4]
    have h6 : b < 3 / 2 := by
      linarith [abs_lt.mp h4]
    have h7 : -1 / 2 < 2 * a + b := by
      linarith [abs_lt.mp h2]
    have h8 : 2 * a + b < 1 / 2 := by
      linarith [abs_lt.mp h2]
    have h9 : -1 / 2 < 2 * a - b := by
      linarith [abs_lt.mp h3]
    have h10 : 2 * a - b < 1 / 2 := by
      linarith [abs_lt.mp h3]
    linarith