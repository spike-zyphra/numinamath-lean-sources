import Mathlib

open Real Set

theorem algebra_299184 :
    IsLeast {z : ℝ | ∃ x y, z = max (max (|x + y|) (|x - y|)) (max (|1 - x|) (|1 - y|))} (2 / 3) := by
  constructor
  · -- Show 2/3 is in the set
    use 1 / 3, 1 / 3
    norm_num [abs_of_nonneg, abs_of_nonpos, max_assoc, max_comm, max_left_comm]
  · -- Show there is no smaller element in the set
    intro z h
    rcases h with ⟨x, y, hz⟩
    by_contra h
    push_neg at h
    have h1 : max (max (|x + y|) (|x - y|)) (max (|1 - x|) (|1 - y|)) < 2 / 3 := by linarith [hz, h]
    have h2 : |x + y| < 2 / 3 := by
      have h3 : max (max (|x + y|) (|x - y|)) (max (|1 - x|) (|1 - y|)) < 2 / 3 := h1
      have h4 : |x + y| ≤ max (max (|x + y|) (|x - y|)) (max (|1 - x|) (|1 - y|)) := by
        simp
      linarith [h3, h4]
    have h3 : |x - y| < 2 / 3 := by
      have h4 : max (max (|x + y|) (|x - y|)) (max (|1 - x|) (|1 - y|)) < 2 / 3 := h1
      have h5 : |x - y| ≤ max (max (|x + y|) (|x - y|)) (max (|1 - x|) (|1 - y|)) := by
        simp
      linarith [h4, h5]
    have h4 : |1 - x| < 2 / 3 := by
      have h5 : max (max (|x + y|) (|x - y|)) (max (|1 - x|) (|1 - y|)) < 2 / 3 := h1
      have h6 : |1 - x| ≤ max (max (|x + y|) (|x - y|)) (max (|1 - x|) (|1 - y|)) := by
        simp
      linarith [h5, h6]
    have h5 : |1 - y| < 2 / 3 := by
      have h6 : max (max (|x + y|) (|x - y|)) (max (|1 - x|) (|1 - y|)) < 2 / 3 := h1
      have h7 : |1 - y| ≤ max (max (|x + y|) (|x - y|)) (max (|1 - x|) (|1 - y|)) := by
        simp
      linarith [h6, h7]
    have h6 : 1 / 3 < x := by
      linarith [abs_lt.mp h4]
    have h8 : 1 / 3 < y := by
      linarith [abs_lt.mp h5]
    have h10 : x + y < 2 / 3 := by
      linarith [abs_lt.mp h2]
    have h15 : x < 1 / 3 := by
      linarith [show y > 1 / 3 by linarith [abs_lt.mp h5], h10]
    linarith