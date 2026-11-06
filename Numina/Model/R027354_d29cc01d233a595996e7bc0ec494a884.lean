import Mathlib

theorem inequalities_13588 :
    Set.ncard {x : ℤ | 6 < (5 + x ^ 2 : ℝ) / 8 ∧ (5 + x ^ 2 : ℝ) / 8 < 9} = 4 := by
  have h1 : {x : ℤ | 6 < (5 + x ^ 2 : ℝ) / 8 ∧ (5 + x ^ 2 : ℝ) / 8 < 9} = {-8, -7, 7, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume 6 < (5 + x ^ 2) / 8 ∧ (5 + x ^ 2) / 8 < 9, prove x ∈ {-8, -7, 7, 8}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : (x : ℝ) ^ 2 > (43 : ℝ) := by
        nlinarith
      have h4 : (x : ℝ) ^ 2 < (67 : ℝ) := by
        nlinarith
      have h5 : x ^ 2 > 43 := by
        by_contra h
        push_neg at h
        have h6 : (x : ℝ) ^ 2 ≤ (43 : ℝ) := by
          exact_mod_cast h
        linarith
      have h6 : x ^ 2 < 67 := by
        by_contra h
        push_neg at h
        have h7 : (x : ℝ) ^ 2 ≥ (67 : ℝ) := by
          exact_mod_cast h
        linarith
      have h7 : x ≤ 8 := by
        nlinarith [show x ^ 2 < 67 by linarith]
      have h8 : x ≥ -8 := by
        nlinarith [show x ^ 2 < 67 by linarith]
      interval_cases x <;> norm_num at h1 h2 ⊢ <;> tauto
    · -- Assume x ∈ {-8, -7, 7, 8}, prove 6 < (5 + x ^ 2) / 8 ∧ (5 + x ^ 2) / 8 < 9
      rintro (h | h | h | h)
      · -- x = -8
        rw [h]
        norm_num
      · -- x = -7
        rw [h]
        norm_num
      · -- x = 7
        rw [h]
        norm_num
      · -- x = 8
        rw [h]
        norm_num
  rw [h1]
  norm_num