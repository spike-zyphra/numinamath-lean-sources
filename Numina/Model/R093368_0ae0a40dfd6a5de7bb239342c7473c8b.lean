import Mathlib

theorem algebra_14400 : {x : ℤ | Real.sqrt 5 < x ∧ x < Real.sqrt 50}.encard = 5 := by 
  have h3 : {x : ℤ | Real.sqrt 5 < x ∧ x < Real.sqrt 50} = {3, 4, 5, 6, 7} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume Real.sqrt 5 < (x : ℝ) ∧ (x : ℝ) < Real.sqrt 50, prove x ∈ {3, 4, 5, 6, 7}
      intro h
      rcases h with ⟨h1, h2⟩
      have h4 : x > 2 := by 
        by_contra h4
        push_neg at h4
        have : x ≤ 2 := by omega
        have h5 : (x : ℝ) ≤ (2 : ℝ) := by exact_mod_cast this
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 50, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (50 : ℝ) by norm_num)]
      have h6 : x < 8 := by 
        have h7 : (x : ℝ) < (8 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 50, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (50 : ℝ) by norm_num)]
        exact_mod_cast h7
      interval_cases x <;> norm_num at *
      <;> try { tauto }
      <;> norm_num at h1 h2 <;> linarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 50]
    · -- Assume x ∈ {3, 4, 5, 6, 7}, prove Real.sqrt 5 < (x : ℝ) ∧ (x : ℝ) < Real.sqrt 50
      rintro (rfl | rfl | rfl | rfl | rfl)
      · constructor
        · -- Show that Real.sqrt 5 < (3 : ℝ)
          have h11 : Real.sqrt 5 < (3 : ℝ) := by
            rw [Real.sqrt_lt] <;> norm_num
          exact_mod_cast h11
        · -- Show that (3 : ℝ) < Real.sqrt 50
          have h3 : (3 : ℝ) < Real.sqrt 50 := by
            rw [Real.lt_sqrt] <;> norm_num
          exact_mod_cast h3
      · constructor
        · -- Show that Real.sqrt 5 < (4 : ℝ)
          have h11 : Real.sqrt 5 < (4 : ℝ) := by
            rw [Real.sqrt_lt] <;> norm_num
          exact_mod_cast h11
        · -- Show that (4 : ℝ) < Real.sqrt 50
          have h3 : (4 : ℝ) < Real.sqrt 50 := by
            rw [Real.lt_sqrt] <;> norm_num
          exact_mod_cast h3
      · constructor
        · -- Show that Real.sqrt 5 < (5 : ℝ)
          have h11 : Real.sqrt 5 < (5 : ℝ) := by
            rw [Real.sqrt_lt] <;> norm_num
          exact_mod_cast h11
        · -- Show that (5 : ℝ) < Real.sqrt 50
          have h3 : (5 : ℝ) < Real.sqrt 50 := by
            rw [Real.lt_sqrt] <;> norm_num
          exact_mod_cast h3
      · constructor
        · -- Show that Real.sqrt 5 < (6 : ℝ)
          have h11 : Real.sqrt 5 < (6 : ℝ) := by
            rw [Real.sqrt_lt] <;> norm_num
          exact_mod_cast h11
        · -- Show that (6 : ℝ) < Real.sqrt 50
          have h3 : (6 : ℝ) < Real.sqrt 50 := by
            rw [Real.lt_sqrt] <;> norm_num
          exact_mod_cast h3
      · constructor
        · -- Show that Real.sqrt 5 < (7 : ℝ)
          have h11 : Real.sqrt 5 < (7 : ℝ) := by
            rw [Real.sqrt_lt] <;> norm_num
          exact_mod_cast h11
        · -- Show that (7 : ℝ) < Real.sqrt 50
          have h3 : (7 : ℝ) < Real.sqrt 50 := by
            rw [Real.lt_sqrt] <;> norm_num
          exact_mod_cast h3
  rw [h3]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try linarith