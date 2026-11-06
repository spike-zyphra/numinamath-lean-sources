import Mathlib

theorem algebra_160763 :
    IsLeast {x | ∃ a b : ℝ, x = max (max (|2 * a + b|) (|a - b|)) (|1 + b|)} (1 / 2) := by

  constructor
  · -- Show 1/2 is in the set
    use 0, -1 / 2
    norm_num [abs_of_nonneg, abs_of_nonpos, max_assoc, max_comm, max_left_comm]
    
  · -- Show no smaller element is in the set
    intro x hx
    rcases hx with ⟨a, b, hx⟩
    have h1 : max (max (|2 * a + b|) (|a - b|)) (|1 + b|) ≥ 1 / 2 := by
      by_contra h
      push_neg at h
      have h2 : |2 * a + b| < 1 / 2 := by
        have h3 : max (max (|2 * a + b|) (|a - b|)) (|1 + b|) < 1 / 2 := by linarith
        have h4 : |2 * a + b| ≤ max (max (|2 * a + b|) (|a - b|)) (|1 + b|) := by
          simp [max_le_iff]
        linarith
      have h3 : |a - b| < 1 / 2 := by
        have h4 : max (max (|2 * a + b|) (|a - b|)) (|1 + b|) < 1 / 2 := by linarith
        have h5 : |a - b| ≤ max (max (|2 * a + b|) (|a - b|)) (|1 + b|) := by
          simp [max_le_iff]
        linarith
      have h4 : |1 + b| < 1 / 2 := by
        have h5 : max (max (|2 * a + b|) (|a - b|)) (|1 + b|) < 1 / 2 := by linarith
        have h6 : |1 + b| ≤ max (max (|2 * a + b|) (|a - b|)) (|1 + b|) := by
          simp [max_le_iff]
        linarith
      have h5 : -1 / 2 < 2 * a + b := by linarith [abs_lt.mp h2]
      have h6 : 2 * a + b < 1 / 2 := by linarith [abs_lt.mp h2]
      have h7 : -1 / 2 < a - b := by linarith [abs_lt.mp h3]
      have h8 : a - b < 1 / 2 := by linarith [abs_lt.mp h3]
      have h9 : -1 / 2 < 1 + b := by linarith [abs_lt.mp h4]
      have h10 : 1 + b < 1 / 2 := by linarith [abs_lt.mp h4]
      linarith
    linarith [h1, hx]