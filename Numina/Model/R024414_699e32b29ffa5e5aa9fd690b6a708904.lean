import Mathlib

theorem algebra_284628 :
    ∑ᶠ a ∈ {x : ℤ | (x^2 - 3 * x - 3) % (x - 2) = 0}, a = 8 := by 
  have h1 : {x : ℤ | (x^2 - 3 * x - 3) % (x - 2) = 0} = {-3, 1, 3, 7} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor 
    · -- First, (x^2 - 3 * x - 3) % (x - 2) = 0 implies x ∈ {-3, 1, 3, 7}
      intro h
      have h2 : x - 2 ∣ x ^ 2 - 3 * x - 3 := by 
        have h3 : (x ^ 2 - 3 * x - 3) % (x - 2) = 0 := by 
          simpa using h 
        exact Int.dvd_of_emod_eq_zero h3 
      have h9 : (x - 2) ∣ 5 := by 
        have h10 : (x - 2) ∣ (x^2 - 3 * x - 3) := h2 
        have h11 : (x - 2) ∣ ((x - 1) * (x - 2) - (x^2 - 3 * x - 3)) := by 
          apply Dvd.dvd.sub 
          · -- Show (x-2) divides (x-1)(x-2) 
            use (x - 1)
            ring 
          · -- Show (x-2) divides (x^2 - 3 * x - 3)
            exact h10 
        have eq1 : ((x - 1) * (x - 2) - (x^2 - 3 * x - 3)) = 5 := by 
          nlinarith 
        rw [eq1] at h11 
        exact h11 
      have h9a : (x - 2) ≤ 5 := by 
        apply Int.le_of_dvd (show 0 < 5 by norm_num) h9 
      have h9b : (x - 2) ≥ -5 := by 
        have h3a : (- (x - 2)) ∣ 5 := by 
          exact Int.neg_dvd.2 h9 
        have h4a : - (x - 2) ≤ 5 := by 
          apply Int.le_of_dvd (show 0 < 5 by norm_num) h3a 
        omega 
      have h9b : (x - 2) ≥ -5 := h9b 
      have h9c : x ≤ 7 := by 
        omega 
      have h9d : x ≥ -3 := by 
        omega 
      interval_cases x <;> norm_num at h ⊢ 
    · -- Now the reverse direction
      rintro (rfl | rfl | rfl | rfl)
      · -- Case x = -3
        norm_num 
      · -- Case x = 1
        norm_num 
      · -- Case x = 3
        norm_num 
      · -- Case x = 7
        norm_num 
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  native_decide