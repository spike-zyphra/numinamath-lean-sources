import Mathlib

open Real Set

theorem inequalities_46663 :
    ∑ᶠ x ∈ {x : ℝ | ∃ a b c d : ℝ, x = |a - d| ∧ |a - b| = 2 ∧ |b - c| = 3 ∧ |c - d| = 4}, x = 18 := by
  have h1 : {x : ℝ | ∃ a b c d : ℝ, x = |a - d| ∧ |a - b| = 2 ∧ |b - c| = 3 ∧ |c - d| = 4} = {1, 3, 5, 9} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- Assume x ∈ {x | ...}
      intro hx
      rcases hx with ⟨a, b, c, d, hx1, h1, h2, h3⟩
      have h4 : a - b = 2 ∨ a - b = -2 := by
        cases eq_or_eq_neg_of_abs_eq h1 with
        | inl h =>
          left
          linarith
        | inr h =>
          right
          linarith
      have h5 : b - c = 3 ∨ b - c = -3 := by
        cases eq_or_eq_neg_of_abs_eq h2 with
        | inl h =>
          left
          linarith
        | inr h =>
          right
          linarith
      have h6 : c - d = 4 ∨ c - d = -4 := by
        cases eq_or_eq_neg_of_abs_eq h3 with
        | inl h =>
          left
          linarith
        | inr h =>
          right
          linarith
      have h7 : a - d = (a - b) + (b - c) + (c - d) := by linarith
      have h8 : |a - d| = |(a - b) + (b - c) + (c - d)| := by
        rw [show a - d = (a - b) + (b - c) + (c - d) by linarith]
      rcases h4 with (h4 | h4)
      · -- If a - b = 2
        rcases h5 with (h5 | h5)
        · -- If b - c = 3
          rcases h6 with (h6 | h6)
          · -- If c - d = 4
            have h9 : |a - d| = 9 := by
              rw [h8]
              rw [show (a - b) + (b - c) + (c - d) = (9 : ℝ) by linarith [h4, h5, h6]]
              norm_num [abs_of_nonneg]
            rw [h9] at hx1
            rw [hx1]
            norm_num
          · -- If c - d = -4
            have h9 : |a - d| = 1 := by
              rw [h8]
              rw [show (a - b) + (b - c) + (c - d) = (1 : ℝ) by linarith [h4, h5, h6]]
              norm_num [abs_of_nonneg]
            rw [h9] at hx1
            rw [hx1]
            norm_num
        · -- If b - c = -3
          rcases h6 with (h6 | h6)
          · -- If c - d = 4
            have h9 : |a - d| = 3 := by
              rw [h8]
              rw [show (a - b) + (b - c) + (c - d) = (3 : ℝ) by linarith [h4, h5, h6]]
              norm_num [abs_of_nonneg]
            rw [h9] at hx1
            rw [hx1]
            norm_num
          · -- If c - d = -4
            have h9 : |a - d| = 5 := by
              rw [h8]
              rw [show (a - b) + (b - c) + (c - d) = (-5 : ℝ) by linarith [h4, h5, h6]]
              norm_num [abs_of_nonneg, abs_of_neg]
            rw [h9] at hx1
            rw [hx1]
            norm_num
      · -- If a - b = -2
        rcases h5 with (h5 | h5)
        · -- If b - c = 3
          rcases h6 with (h6 | h6)
          · -- If c - d = 4
            have h9 : |a - d| = 5 := by
              rw [h8]
              rw [show (a - b) + (b - c) + (c - d) = (5 : ℝ) by linarith [h4, h5, h6]]
              norm_num [abs_of_nonneg]
            rw [h9] at hx1
            rw [hx1]
            norm_num
          · -- If c - d = -4
            have h9 : |a - d| = 3 := by
              rw [h8]
              rw [show (a - b) + (b - c) + (c - d) = (-3 : ℝ) by linarith [h4, h5, h6]]
              norm_num [abs_of_nonneg, abs_of_neg]
            rw [h9] at hx1
            rw [hx1]
            norm_num
        · -- If b - c = -3
          rcases h6 with (h6 | h6)
          · -- If c - d = 4
            have h9 : |a - d| = 1 := by
              rw [h8]
              rw [show (a - b) + (b - c) + (c - d) = (-1 : ℝ) by linarith [h4, h5, h6]]
              norm_num [abs_of_nonneg, abs_of_neg]
            rw [h9] at hx1
            rw [hx1]
            norm_num
          · -- If c - d = -4
            have h9 : |a - d| = 9 := by
              rw [h8]
              rw [show (a - b) + (b - c) + (c - d) = (-9 : ℝ) by linarith [h4, h5, h6]]
              norm_num [abs_of_nonneg, abs_of_neg]
            rw [h9] at hx1
            rw [hx1]
            norm_num
    · -- Assume x ∈ {1, 3, 5, 9}
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 1
        use 3, 1, -2, 2
        norm_num [abs_of_nonneg, abs_of_neg]
      · -- x = 3
        use 3, 1, 4, 0
        norm_num [abs_of_nonneg, abs_of_neg]
      · -- x = 5
        use -5, -7, -4, 0
        norm_num [abs_of_nonneg, abs_of_neg]
      · -- x = 9
        use 9, 7, 4, 0
        norm_num [abs_of_nonneg, abs_of_neg]
  rw [h1]
  rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
  all_goals norm_num