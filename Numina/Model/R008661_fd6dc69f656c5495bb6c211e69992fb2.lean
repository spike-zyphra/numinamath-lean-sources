import Mathlib

theorem algebra_10493 : ∏ᶠ y ∈ {y : ℝ| abs y = 2 * (abs y - 1)}, y = -4:= by
  have h1 : {y : ℝ | abs y = 2 * (abs y - 1)} = {2, -2} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume h_eq : abs y = 2 * (abs y - 1), prove y = 2 ∨ y = -2
      intro h_eq
      have h_eq1 : abs y = 2 := by
        linarith [abs_nonneg y]
      cases abs_cases y with
      | inl hy_pos =>
        left
        linarith
      | inr hy_neg =>
        right
        linarith
    · -- Assume y = 2 ∨ y = -2, prove abs y = 2 * (abs y - 1)
      rintro (h_eq | h_eq)
      · -- Case y = 2
        rw [h_eq]
        norm_num [abs_of_nonneg]
      · -- Case y = -2
        rw [h_eq]
        norm_num [abs_of_nonpos]
  rw [h1]
  rw [finprod_mem_pair]
  all_goals norm_num
  all_goals norm_num