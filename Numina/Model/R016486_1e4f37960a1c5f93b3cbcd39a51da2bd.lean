import Mathlib

open Real Set

theorem inequalities_108896 :
    IsLeast {t : ℝ | ∃ x y, t = max (max (|2 * x + y|) (|x - y|)) (|1 + y|)} (1 / 2) := by
  constructor
  · -- Show 1/2 is achievable, using x=0, y=-1/2
    use 0, -1 / 2
    norm_num [abs_of_nonneg, abs_of_nonpos, max_assoc, max_comm, max_left_comm]
  · -- Show 1/2 is minimal
    intro t ht
    rcases ht with ⟨x, y, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : max (max (|2 * x + y|) (|x - y|)) (|1 + y|) < (1 / 2 : ℝ) := by
      linarith [h_eq, h]
    have h2 : |2 * x + y| < (1 / 2 : ℝ) := by
      have h3 : max (max (|2 * x + y|) (|x - y|)) (|1 + y|) < (1 / 2 : ℝ) := h1
      have h4 : |2 * x + y| ≤ max (max (|2 * x + y|) (|x - y|)) (|1 + y|) := by
        simp
      linarith [h4, h1]
    have h3 : |x - y| < (1 / 2 : ℝ) := by
      have h3 : max (max (|2 * x + y|) (|x - y|)) (|1 + y|) < (1 / 2 : ℝ) := h1
      have h5 : |x - y| ≤ max (max (|2 * x + y|) (|x - y|)) (|1 + y|) := by
        simp
      linarith [h5, h1]
    have h4 : |1 + y| < (1 / 2 : ℝ) := by
      have h3 : max (max (|2 * x + y|) (|x - y|)) (|1 + y|) < (1 / 2 : ℝ) := h1
      have h6 : |1 + y| ≤ max (max (|2 * x + y|) (|x - y|)) (|1 + y|) := by
        simp
      linarith [h6, h1]
    have h5 : - (1 / 2 : ℝ) < 2 * x + y := by
      linarith [abs_lt.mp h2]
    have h6 : 2 * x + y < (1 / 2 : ℝ) := by
      linarith [abs_lt.mp h2]
    have h7 : - (1 / 2 : ℝ) < x - y := by
      linarith [abs_lt.mp h3]
    have h8 : x - y < (1 / 2 : ℝ) := by
      linarith [abs_lt.mp h3]
    have h9 : - (1 / 2 : ℝ) < 1 + y := by
      linarith [abs_lt.mp h4]
    have h10 : 1 + y < (1 / 2 : ℝ) := by
      linarith [abs_lt.mp h4]
    linarith