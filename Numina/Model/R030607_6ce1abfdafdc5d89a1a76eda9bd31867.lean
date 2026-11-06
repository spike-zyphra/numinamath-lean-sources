import Mathlib

theorem number_theory_5465 :
    ∑ᶠ a ∈ {x : ℕ | ∃ y, x > 0 ∧ y > 0 ∧ Nat.lcm (x ^ 3) (y ^ 4) = 648}, a = 8 := by
  have h1 : {x : ℕ | ∃ y, x > 0 ∧ y > 0 ∧ Nat.lcm (x ^ 3) (y ^ 4) = 648} = {2, 6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x in the set.
      rintro ⟨y, hx1, hy1, h⟩
      have h2 : x ^ 3 ∣ 648 := by
        have h5 : x ^ 3 ∣ Nat.lcm (x ^ 3) (y ^ 4) := by
          exact Nat.dvd_lcm_left (x ^ 3) (y ^ 4)
        rw [h] at h5
        exact h5
      have h3 : y ^ 4 ∣ 648 := by
        have h4 : y ^ 4 ∣ Nat.lcm (x ^ 3) (y ^ 4) := by
          exact Nat.dvd_lcm_right (x ^ 3) (y ^ 4)
        rw [h] at h4
        exact h4
      -- Since $x^3 | 648$, we can determine an upper bound for x.
      have h4 : x ≤ 18 := by
        have h5 : x ^ 3 ∣ 648 := h2
        have : x ^ 3 ≤ 648 := by 
          exact Nat.le_of_dvd (by norm_num) h5
        have : x ≤ 18 := by
          by_contra h19
          push_neg at h19
          have h10 : x > 18 := h19
          have h11 : x ≥ 19 := by omega
          have h12 : x ^ 3 ≥ 19 ^ 3 := by
            have h14 : x ≥ 19 := h11
            have h15 : x ^ 3 ≥ 19 ^ 3 := by
              apply Nat.pow_le_pow_of_le_left h14 3
            linarith
          nlinarith
        assumption
      -- Since $y^4 | 648$, we can determine an upper bound for y.
      have h5 : y ≤ 6 := by
        have h6 : y ^ 4 ∣ 648 := h3
        have : y ^ 4 ≤ 648 := by 
          exact Nat.le_of_dvd (by norm_num) h6
        have : y ≤ 6 := by
          by_contra h19
          push_neg at h19
          have h10 : y > 6 := h19
          have h11 : y ≥ 7 := by omega
          have h12 : y ^ 4 ≥ 7 ^ 4 := by
            have h14 : y ≥ 7 := h11
            have h15 : y ^ 4 ≥ 7 ^ 4 := by
              apply Nat.pow_le_pow_of_le_left h14 4
            linarith
          nlinarith
        assumption
      interval_cases x <;> try { 
        omega 
      } <;> try { 
        interval_cases y 
        <;> norm_num [Nat.lcm] at h 
        <;> omega 
      }
    · -- Assume x = 2 or 6.
      rintro (rfl | rfl)
      · -- Let x = 2.
        use 3
        all_goals
        norm_num [Nat.lcm]
      · -- Let x = 6.
        use 3
        all_goals
        norm_num [Nat.lcm]
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals
  norm_num