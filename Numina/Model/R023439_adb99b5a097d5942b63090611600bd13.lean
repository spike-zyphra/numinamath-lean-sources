import Mathlib

theorem inequalities_305145 : {x : ℤ | abs (x - 1) + abs (x - 9) < Real.sqrt 98}.encard = 9 := by
  have h1 : Real.sqrt 98 = 7 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h2 : Real.sqrt 98 > 0 := by
    apply Real.sqrt_pos.2
    all_goals norm_num
  have h3 : (9 : ℝ) < Real.sqrt 98 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h4 : Real.sqrt 98 < (10 : ℝ) := by
    rw [Real.sqrt_lt] <;> norm_num
  have h5 : {x : ℤ | abs (x - 1) + abs (x - 9) < Real.sqrt 98} = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by 
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume abs (x - 1) + abs (x - 9) < Real.sqrt 98, prove x ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9}
      intro h
      have h6 : (abs (x - 1 : ℤ) + abs (x - 9 : ℤ) : ℝ) < Real.sqrt 98 := by
        exact_mod_cast h
      have h7 : abs (x - 1 : ℤ) + abs (x - 9 : ℤ) ≤ 9 := by
        by_contra h8
        push_neg at h8
        have h9 : abs (x - 1 : ℤ) + abs (x - 9 : ℤ) ≥ 10 := by
          omega
        have h10 : (abs (x - 1 : ℤ) + abs (x - 9 : ℤ) : ℝ) ≥ (10 : ℝ) := by
          exact_mod_cast h9
        nlinarith [h4, h6, h10, Real.sqrt_nonneg (98 : ℝ)]
      have h11 : x ≥ 1 := by
        by_contra h
        push_neg at h
        have : x ≤ 0 := by omega
        have h8 : abs (x - 1 : ℤ) + abs (x - 9 : ℤ) ≥ 10 := by
          cases' abs_cases (x - 1 : ℤ) with h11 h11 <;> 
              cases' abs_cases (x - 9 : ℤ) with h12 h12 <;> 
                omega
        omega
      have h12 : x ≤ 9 := by
        by_contra h
        push_neg at h
        have : x ≥ 10 := by omega
        have h8 : abs (x - 1 : ℤ) + abs (x - 9 : ℤ) ≥ 10 := by
          cases' abs_cases (x - 1 : ℤ) with h11 h11 <;> 
              cases' abs_cases (x - 9 : ℤ) with h12 h12 <;> 
                omega
        omega
      interval_cases x <;> norm_num [abs] at h7 ⊢ <;> tauto
    · -- Show that x ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9} implies abs (x - 1) + abs (x - 9) < Real.sqrt 98
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        norm_num [abs]
        all_goals
          norm_num at *
          all_goals
            linarith [h3, h4, Real.sqrt_nonneg 98]
  rw [h5]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { linarith }