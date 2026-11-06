import Mathlib


theorem number_theory_254415 :
    {x : ℚ | x > 7 + 1 / 3 ∧ x < 7 + 1 / 2 ∧ x.num ∈ Finset.Icc 10 99 ∧ x.den ∈ Finset.Icc 10 99 ∧ (x.num).gcd (x.den) = 1} =
    {81 / 11, 82 / 11, 89 / 12, 96 / 13, 97 / 13} := by
  ext x
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- First direction: if x is in the left side, it's in the right side
    rintro ⟨h1, h2, ⟨hn1, hn2⟩, ⟨hd1, hd2⟩, hgcd⟩
    have h3 : x > (22 / 3 : ℚ) := by
      norm_num at h1 ⊢
      linarith
    have h4 : x < (15 / 2 : ℚ) := by
      norm_num at h2 ⊢
      linarith
    have h5 : x.num ≥ 10 := by
      omega
    have h6 : x.num ≤ 99 := by
      omega
    have h7 : x.den ≥ 10 := by
      omega
    have h8 : x.den ≤ 99 := by
      omega
    -- Convert x to a rational number explicitly.
    have h9 : (x.num : ℚ) / (x.den : ℚ) = x := by
      field_simp
    -- Check cross multiplies for upper bound
    have h10 : x.num * 2 < 15 * x.den := by
      have h11 : (x.num : ℚ) / (x.den : ℚ) < (15 / 2 : ℚ) := by
        linarith [h4, h9]
      have h12 : x.num * 2 < 15 * x.den := by
        by_contra h
        push_neg at h
        have h13 : (x.num : ℚ) * 2 ≥ (15 * x.den : ℚ) := by exact_mod_cast show (x.num * 2 : ℤ) ≥ (15 * x.den : ℤ) by omega
        have h14 : (x.num : ℚ) / (x.den : ℚ) ≥ (15 / 2 : ℚ) := by
          have h15 : x.den > 0 := by
            have : x.den ≥ 1 := by
              omega
            omega
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          linarith
        linarith
      exact_mod_cast h12
    -- Check cross multiplies for lower bound
    have h13 : x.num * 3 > 22 * x.den := by
      have h14 : (x.num : ℚ) / (x.den : ℚ) > (22 / 3 : ℚ) := by
        linarith [h3, h9]
      have h17 : x.num * 3 > 22 * x.den := by
        by_contra h
        push_neg at h
        have h18 : (x.num * 3 : ℚ) ≤ (22 * x.den : ℚ) := by exact_mod_cast show (x.num * 3 : ℤ) ≤ (22 * x.den : ℤ) by omega
        have h19 : (x.num : ℚ) / (x.den : ℚ) ≤ (22 / 3 : ℚ) := by
          have h15 : x.den > 0 := by
            have : x.den ≥ 1 := by
              omega
            omega
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          linarith
        linarith
      exact_mod_cast h17
    interval_cases h : x.num <;> try { 
      omega
    } <;> try { 
      interval_cases k : x.den <;> norm_num at h3 h4 h10 h13 hgcd h5 h6 h7 h8 ⊢ <;> tauto
    }
  · -- Second direction: if x is in the right side, it's in the left side
    rintro (rfl | rfl | rfl | rfl | rfl)
    · -- Check 81/11
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check 82/11
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check 89/12
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check 96/13
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check 97/13
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num