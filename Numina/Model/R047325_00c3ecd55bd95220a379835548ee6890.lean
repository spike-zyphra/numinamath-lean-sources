import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21211:
    IsGreatest {m | ∃A B: ℝ × ℝ, A ∈ {p | p.1 ∈ Icc 0 2 ∧ p.2 ∈ Icc 0 2} ∧ B ∈ {p | p.1 ∈ Icc 4 5 ∧ p.2 ∈ Icc 2 3} ∧ m = (B.2 - A.2) / (B.1 - A.1)} (3 / (2 : ℝ)) := by
  constructor
  · -- Show that 3/2 is achievable by taking A = (2, 0) and B = (4, 3)
    use (2, (0 : ℝ))
    use (4, (3 : ℝ))
    constructor
    · -- Show that A is in the square [0, 2] × [0, 2]
      constructor
      · -- Show that the x-coordinate of A is in [0, 2]
        norm_num [mem_Icc]
      · -- Show that the y-coordinate of A is in [0, 2]
        norm_num [mem_Icc]
    constructor
    · -- Show that B is in the square [4, 5] × [2, 3]
      constructor
      · -- Show that the x-coordinate of B is in [4, 5]
        norm_num [mem_Icc]
      · -- Show that the y-coordinate of B is in [2, 3]
        norm_num [mem_Icc]
    · -- Show that the slope is 3/2
      norm_num
  · -- Show that 3/2 is the greatest such value
    intro m hm
    rcases hm with ⟨A, B, hA, hB, hm⟩
    rcases hA with ⟨hA1, hA2⟩
    rcases hB with ⟨hB1, hB2⟩
    rcases hA1 with ⟨hA1l, hA1r⟩
    rcases hA2 with ⟨hA2l, hA2r⟩
    rcases hB1 with ⟨hB1l, hB1r⟩
    rcases hB2 with ⟨hB2l, hB2r⟩
    by_cases h_denom : (B.1 - A.1) > 0
    · -- Case where denominator is positive
      have h1 : (B.2 - A.2) / (B.1 - A.1) ≤ (3 / (2 : ℝ)) := by
        apply (div_le_iff₀ h_denom).mpr
        have h4 : B.2 - A.2 ≤ 3 := by
          linarith
        have h5 : B.1 - A.1 ≥ 2 := by
          nlinarith
        linarith
      linarith [hm, h1]
    · -- Case where denominator is not positive
      have h_denom_nonpos : B.1 - A.1 ≤ 0 := by
        by_contra h
        push_neg at h
        linarith
      have h_denom_zero : B.1 - A.1 = 0 := by
        nlinarith
      rw [h_denom_zero] at hm
      field_simp at hm 
      all_goals linarith