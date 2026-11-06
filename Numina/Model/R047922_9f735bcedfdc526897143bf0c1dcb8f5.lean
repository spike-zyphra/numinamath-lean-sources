import Mathlib

theorem algebra_291538 :
  ∃! m : ℤ, m ≠ 0 ∧ {(x, y) : ℤ × ℤ | y = -3 * x + 2 ∧ x > 0} ∩ {(x, y) : ℤ × ℤ | y = m * (x ^ 2 - x + 1) ∧ x > 0} ≠ ∅ := by
  use -1
  constructor
  · -- Let's prove that m=-1 works
    constructor
    · norm_num
    · -- Show that the intersection is non-empty
      have h1 : ({(x, y) : ℤ × ℤ | y = -3 * x + 2 ∧ x > 0} ∩ {(x, y) : ℤ × ℤ | y = (-1) * (x ^ 2 - x + 1) ∧ x > 0}) ≠ ∅ := by
        have h4 : ((1 : ℤ), -1) ∈ ({(x, y) : ℤ × ℤ | y = -3 * x + 2 ∧ x > 0} ∩ {(x, y) : ℤ × ℤ | y = (-1) * (x ^ 2 - x + 1) ∧ x > 0}) := by
          constructor
          · -- Show that ((1), -1) is in the first set.
            simp
          · -- Show that ((1), -1) is in the second set.
            simp
        intro h
        rw [h] at h4
        all_goals simp at h4
      assumption
  · -- Now prove the uniqueness
    intro m hm
    rcases hm with ⟨hmne, hcap⟩
    have hne : {(x, y) : ℤ × ℤ | y = -3 * x + 2 ∧ x > 0} ∩ {(x, y) : ℤ × ℤ | y = m * (x ^ 2 - x + 1) ∧ x > 0} ≠ ∅ := hcap
    rcases Set.nonempty_iff_ne_empty.2 hne with ⟨p, hp⟩
    rcases p with ⟨x, y⟩
    rcases hp with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have heq : m * (x ^ 2 - x + 1) = -3 * x + 2 := by linarith
    have h5 : m = -1 := by
      have eq1 : m * (x ^ 2 - x + 1) = -3 * x + 2 := by linarith
      by_cases h6 : x = 1
      · -- Case x = 1
        rw [h6] at eq1
        nlinarith
      by_cases h7 : x = 3
      · -- Case x = 3
        rw [h7] at eq1
        nlinarith
      · -- Case x ≠ 1 and x ≠ 3
        have h8 : x ^ 2 - x + 1 ≠ 0 := by
          nlinarith
        nlinarith [sq_nonneg (m + 1), sq_nonneg (x - 1), sq_nonneg (x - 3), sq_pos_of_ne_zero (show m ≠ 0 by exact hmne), sq_pos_of_pos (show x > 0 by linarith), sq_nonneg (m * (x ^ 2 - x + 1)), sq_nonneg ((-3) * x), sq_nonneg (x ^ 2 - x + 1)]
    assumption