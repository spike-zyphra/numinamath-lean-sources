import Mathlib

theorem algebra_20449 : Set.ncard {x : ℤ |
    3 * Real.sqrt 5 < x ∧ x < 5 * Real.sqrt 3 ∨
    5 * Real.sqrt 3 < x ∧ x < 3 * Real.sqrt 5
  } = 2 := by
  have h1 : Real.sqrt 5 > 0 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have h2 : Real.sqrt 3 > 0 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have h3 : (3 * Real.sqrt 5 : ℝ) < (5 * Real.sqrt 3 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3,
      Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num),
      Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - Real.sqrt 3)]
  have h5 : {x : ℤ |
      3 * Real.sqrt 5 < x ∧ x < 5 * Real.sqrt 3 ∨
      5 * Real.sqrt 3 < x ∧ x < 3 * Real.sqrt 5
    } = {7, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume $3 * Real.sqrt 5 < x ∧ x < 5 * Real.sqrt 3 ∨ 5 * Real.sqrt 3 < x ∧ x < 3 * Real.sqrt 5$
      rintro (h | h)
      · -- Case $3 * Real.sqrt 5 < x ∧ x < 5 * Real.sqrt 3$
        rcases h with ⟨h1, h2⟩
        have h6 : (6 : ℝ) < 3 * Real.sqrt 5 := by
          nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        have h7 : (5 * Real.sqrt 3 : ℝ) < (9 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        have h8 : x > 6 := by
          by_contra h
          push_neg at h
          have : x ≤ 6 := by omega
          have h9 : (x : ℝ) ≤ (6 : ℝ) := by exact_mod_cast this
          nlinarith
        have h9 : x < 9 := by
          by_contra h
          push_neg at h
          have : x ≥ 9 := by omega
          have h10 : (x : ℝ) ≥ (9 : ℝ) := by exact_mod_cast this
          nlinarith
        have h10 : x = 7 ∨ x = 8 := by
          omega
        tauto
      · -- Case $5 * Real.sqrt 3 < x ∧ x < 3 * Real.sqrt 5$
        exfalso
        rcases h with ⟨h1, h2⟩
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - Real.sqrt 3)]
    · -- Show {7, 8} ⊆ {x : ℤ | ...}
      rintro (rfl | rfl)
      · -- Check x=7
        left
        constructor
        · -- Show $3 * Real.sqrt 5 < (7 : ℝ)$
          have h5 : (3 * Real.sqrt 5 : ℝ) < (7 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 2)]
          exact_mod_cast h5
        · -- Show $7 < 5 * Real.sqrt 3$
          have h5 : (7 : ℝ) < (5 * Real.sqrt 3 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - 2)]
          exact_mod_cast h5
      · -- Check x=8
        left
        constructor
        · -- Show $3 * Real.sqrt 5 < (8 : ℝ)$
          have h5 : (3 * Real.sqrt 5 : ℝ) < (8 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 2)]
          exact_mod_cast h5
        · -- Show $8 < 5 * Real.sqrt 3$
          have h5 : (8 : ℝ) < (5 * Real.sqrt 3 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - 2)]
          exact_mod_cast h5
  rw [h5]
  norm_num