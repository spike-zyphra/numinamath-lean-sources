import Mathlib

theorem algebra_157874 :
    IsLeast {x : ℝ | ∃ a b, x = max (max (|a + b|) (|a - b|)) (|1 - b|)} (1 / 2) := by
  constructor
  · -- Show that 1/2 is in the set
    use (0 : ℝ), (1 / 2 : ℝ)
    norm_num [abs_of_pos, abs_of_neg]
  · -- Show that 1/2 is the least in the set
    intro x hx
    rcases hx with ⟨a, b, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ (1 / 2 : ℝ) := by
      by_contra h2
      push_neg at h2
      have h3 : |a + b| < (1 / 2 : ℝ) := by
        have h4 : max (max (|a + b|) (|a - b|)) (|1 - b|) < (1 / 2 : ℝ) := by linarith
        have h5 : |a + b| ≤ max (max (|a + b|) (|a - b|)) (|1 - b|) := by
          simp [max_le_iff]
        linarith
      have h4 : |a - b| < (1 / 2 : ℝ) := by
        have h5 : max (max (|a + b|) (|a - b|)) (|1 - b|) < (1 / 2 : ℝ) := by linarith
        have h6 : |a - b| ≤ max (max (|a + b|) (|a - b|)) (|1 - b|) := by
          simp [max_le_iff]
        linarith
      have h5 : |1 - b| < (1 / 2 : ℝ) := by
        have h6 : max (max (|a + b|) (|a - b|)) (|1 - b|) < (1 / 2 : ℝ) := by linarith
        have h7 : |1 - b| ≤ max (max (|a + b|) (|a - b|)) (|1 - b|) := by
          simp [max_le_iff]
        linarith
      have h6 : 1 / 2 < b := by
        linarith [abs_lt.mp h5]
      have h7 : b < 3 / 2 := by
        linarith [abs_lt.mp h5]
      have h8 : -1 / 2 < a + b := by
        linarith [abs_lt.mp h3]
      have h9 : a + b < 1 / 2 := by
        linarith [abs_lt.mp h3]
      have h10 : -1 / 2 < a - b := by
        linarith [abs_lt.mp h4]
      have h11 : a - b < 1 / 2 := by
        linarith [abs_lt.mp h4]
      linarith
    linarith [h_eq, h1, h]