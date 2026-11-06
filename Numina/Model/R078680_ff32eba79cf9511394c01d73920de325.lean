import Mathlib

theorem algebra_12244 : ∑ᶠ y ∈ {y : ℝ | ¬(y^2 - 5 * y + 4) ≠ 0}, y = 5 := by
  have h1 : {y : ℝ | ¬(y^2 - 5 * y + 4) ≠ 0} = {1, 4} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume y^2 - 5 * y + 4 = 0, prove y = 1 or y = 4
      intro h
      have h_eq : y^2 - 5 * y + 4 = 0 := by
        simpa using h
      have : (y - 1) * (y - 4) = 0 := by 
        linarith [h_eq]
      cases' (mul_eq_zero.1 this) with h1 h2
      · left
        linarith
      · right
        linarith
    · -- Assume y = 1 or y = 4, prove y^2 - 5 * y + 4 = 0
      rintro (h | h)
      · rw [h]
        norm_num
      · rw [h]
        norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num