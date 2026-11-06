import Mathlib

theorem algebra_15245 (s : Set ℝ) (hs : s = {x : ℝ | ∃ a b c d : ℝ, |a - b| = 2 ∧ |b - c| = 3 ∧|c - d| = 4 ∧ x = |a - d|}) : ∑ᶠ x ∈ s, x = 18 := by 
  rw [hs]
  have h3 : {x : ℝ | ∃ a b c d : ℝ, |a - b| = 2 ∧ |b - c| = 3 ∧ |c - d| = 4 ∧ x = |a - d|} = {1, 3, 5, 9} := by 
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor 
    · -- Let $a, b, c, d$ be real numbers as per assumption
      rintro ⟨a, b, c, d, h1, h2, h3, h4⟩
      have h41 : a - b = 2 ∨ a - b = -2 := by 
        cases' abs_cases (a - b) with h11 h11
        · left 
          linarith 
        · right 
          linarith 
      have h42 : b - c = 3 ∨ b - c = -3 := by 
        cases' abs_cases (b - c) with h22 h22
        · left 
          linarith 
        · right 
          linarith 
      have h43 : c - d = 4 ∨ c - d = -4 := by 
        cases' abs_cases (c - d) with h33 h33
        · left 
          linarith 
        · right 
          linarith 
      have h8 : a - d = (a - b) + (b - c) + (c - d) := by ring
      have h9 : |a - d| = |(a - b) + (b - c) + (c - d)| := by 
        rw [show (a - b) + (b - c) + (c - d) = a - d by ring]
      rw [h9] at h4 
      rcases h41 with (h41 | h41) <;> rcases h42 with (h42 | h42) <;> rcases h43 with (h43 | h43) <;> 
        norm_num [abs_of_nonneg, abs_of_nonpos, h41, h42, h43] at h4 ⊢ <;> 
          try { 
            norm_num at h4 ⊢ 
            <;> tauto 
          }
    · -- Show that if x is in {1,3,5,9}, then x is in {x : ℝ | ∃ a, b, c, d : ℝ, |a - b| = 2 ∧ |b - c| = 3 ∧|c - d| = 4 ∧ x = |a - d|} 
      rintro (rfl | rfl | rfl | rfl)
      · -- Case x=1
        use 0
        use 2
        use 5
        use 1
        norm_num [abs_of_nonneg, abs_of_pos]
      · -- Case x=3
        use 0
        use 2
        use -1
        use 3
        norm_num [abs_of_pos, abs_of_nonneg, abs_of_nonpos]
      · -- Case x=5
        use 0
        use -2
        use 1
        use 5
        norm_num [abs_of_nonneg, abs_of_nonpos, abs_of_neg]
      · -- Case x=9
        use 0
        use 2
        use 5
        use 9
        norm_num [abs_of_nonneg, abs_of_nonpos]
  rw [h3]
  rw [finsum_mem_eq_toFinset_sum]
  norm_num
  <;> try { linarith }