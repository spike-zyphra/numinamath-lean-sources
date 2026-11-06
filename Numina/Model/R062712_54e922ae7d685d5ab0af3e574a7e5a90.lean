import Mathlib

theorem algebra_137513 : ∑ᶠ (x : ℝ) (h : |x - 2011| + |x - 2012| = 3), x = 4023 := by
  have h1 : {x : ℝ | |x - 2011| + |x - 2012| = 3} = {2010, 2013} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume |x - 2011| + |x - 2012| = 3, show x ∈ {2010, 2013}
      intro h
      by_cases h2 : x ≥ 2012
      · -- Case x ≥ 2012
        rw [abs_of_nonneg (by linarith : x - 2011 ≥ 0), abs_of_nonneg (by linarith : x - 2012 ≥ 0)] at h
        have : x = 2013 := by linarith
        tauto
      · -- Case 2011 ≤ x < 2012
        by_cases h3 : x ≥ 2011
        · -- Case 2011 ≤ x < 2012
          rw [abs_of_nonneg (by linarith : x - 2011 ≥ 0), abs_of_nonpos (by linarith : x - 2012 ≤ 0)] at h
          exfalso
          linarith
        · -- Case x < 2011
          rw [abs_of_nonpos (by linarith : x - 2011 ≤ 0), abs_of_nonpos (by linarith : x - 2012 ≤ 0)] at h
          have : x = 2010 := by linarith
          tauto
    · -- Assume x ∈ {2010, 2013}, show |x - 2011| + |x - 2012| = 3
      rintro (h | h)
      · -- Case x = 2010
        rw [h]
        norm_num [abs_of_nonpos]
      · -- Case x = 2013
        rw [h]
        norm_num [abs_of_nonneg]
  have h2 : ∑ᶠ (x : ℝ) (h : |x - 2011| + |x - 2012| = 3), x = ∑ᶠ (x : ℝ) (hx : x ∈ {x : ℝ | |x - 2011| + |x - 2012| = 3}), x := by
    congr
  rw [h2]
  rw [h1]
  rw [finsum_mem_pair]
  all_goals norm_num