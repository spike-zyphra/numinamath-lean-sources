import Mathlib
theorem algebra_20497 :
     { n |  n > (0 : ℤ) ∧ (-3)* n + 3 > -11} = {1,2,3,4} ∧  ∑ n in {1,2,3,4} , n = 10 := by
  constructor
  · -- Show the set of positive integers satisfying the inequality is {1, 2, 3, 4}
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is a positive integer satisfying -3n + 3 > -11
      rintro ⟨hn_pos, h⟩
      have h1 : n < 5 := by 
        omega
      omega
    · -- Show that if n is in {1, 2, 3, 4}, then it satisfies the inequality
      rintro (rfl | rfl | rfl | rfl)
      · -- Show that 1 satisfies the inequality
        constructor
        · norm_num
        · norm_num
      · -- Show that 2 satisfies the inequality
        constructor
        · norm_num
        · norm_num
      · -- Show that 3 satisfies the inequality
        constructor
        · norm_num
        · norm_num
      · -- Show that 4 satisfies the inequality
        constructor
        · norm_num
        · norm_num
  · -- Show that the sum is 10
    norm_num [Finset.sum_insert, Finset.sum_singleton]