import Mathlib

theorem number_theory_99805 :
    Set.ncard {x : ℚ | x > 1 / 16 ∧ x < 1 / 15 ∧ x.num = 15 ∧ IsCoprime x.num x.den} = 8 := by
  have h1 : {x : ℚ | x > 1 / 16 ∧ x < 1 / 15 ∧ x.num = 15 ∧ IsCoprime x.num x.den} = 
    {15 / 226, 15 / 227, 15 / 229, 15 / 232, 15 / 233, 15 / 236, 15 / 238, 15 / 239} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, 
      Set.union_singleton]
    constructor
    · -- First direction: the set condition implies the membership
      rintro ⟨h1, h2, h3, h4⟩
      have h5 : x > 0 := by linarith
      have h9 : x = (15 : ℚ) / (x.den : ℚ) := by
        have h9' : x = (x.num : ℚ) / (x.den : ℚ) := by
          field_simp
        rw [show x.num = 15 by exact h3] at h9'
        exact h9'
      have h30 : x.den > 0 := by
        have h9' : x = (15 : ℚ) / (x.den : ℚ) := h9
        have h40' : x > (0 : ℚ) := h5
        have h90 : (x.den : ℚ) > 0 := by
          by_contra h
          push_neg at h
          have h31 : (x.den : ℚ) ≤ 0 := by
            nlinarith
          have h6 : x ≤ 0 := by
            rw [h9']
            apply div_nonpos_of_nonneg_of_nonpos
            · -- First part: 15 ≥ 0
              norm_num
            · -- Second part: (x.den : ℚ) ≤ 0
              nlinarith
          linarith
        exact_mod_cast h90
      have h31 : x.den < (240 : ℤ) := by
        have h14 : (x : ℚ) > (1 / 16 : ℚ) := by linarith
        have h102 : (x : ℚ) > (1 / 16 : ℚ) := h14
        rw [h9] at h102
        have h16' : (15 : ℚ) * (16 : ℚ) > (1 : ℚ) * (x.den : ℚ) := by
          have h30' : (x.den : ℚ) > 0 := by
            exact_mod_cast h30
          apply (div_lt_div_iff (by positivity) (by positivity)).mp at h102 
          nlinarith
        have h110 : (x.den : ℚ) < (240 : ℚ) := by
          nlinarith
        exact_mod_cast h110
      have h17 : x.den > (225 : ℤ) := by
        have h15 : (x : ℚ) < (1 / 15 : ℚ) := by linarith
        have h13 : (x : ℚ) < (1 / 15 : ℚ) := h15
        rw [h9] at h13
        have h18' : (15 : ℚ) * (15 : ℚ) < (1 : ℚ) * (x.den : ℚ) := by 
          have h30' : (x.den : ℚ) > 0 := by
            exact_mod_cast h30
          apply (div_lt_div_iff (by positivity) (by positivity)).mp at h13 
          nlinarith
        have h110 : (x.den : ℚ) > (225 : ℚ) := by
          nlinarith
        exact_mod_cast h110
      have h37 : x = (15 : ℚ) / (x.den : ℚ) := h9
      have h43 : x.den ≥ 226 := by
        have h43 : x.den > 225 := by
          exact_mod_cast h17
        omega
      have h45 : x.den ≤ 239 := by
        have h44 : x.den < 240 := by
          exact_mod_cast h31
        omega
      interval_cases h : x.den <;> norm_num [h37] at *
    · -- Second direction: membership implies the set condition
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- First element: 15/226
        constructor
        · -- Show 15/226 > 1/16
          norm_num
        constructor
        · -- Show 15/226 < 1/15
          norm_num
        constructor
        · -- Show numerator = 15
          norm_num
        · -- Show IsCoprime 15 226
          norm_num
      · -- Second element: 15/227
        constructor
        · -- Show 15/227 > 1/16
          norm_num
        constructor
        · -- Show 15/227 < 1/15
          norm_num
        constructor
        · -- Show numerator = 15
          norm_num
        · -- Show IsCoprime 15 227
          norm_num
      · -- Third element: 15/229
        constructor
        · -- Show 15/229 > 1/16
          norm_num
        constructor
        · -- Show 15/229 < 1/15
          norm_num
        constructor
        · -- Show numerator = 15
          norm_num
        · -- Show IsCoprime 15 229
          norm_num
      · -- Fourth element: 15/232
        constructor
        · -- Show 15/232 > 1/16
          norm_num
        constructor
        · -- Show 15/232 < 1/15
          norm_num
        constructor
        · -- Show numerator = 15
          norm_num
        · -- Show IsCoprime 15 232
          norm_num
      · -- Fifth element: 15/233
        constructor
        · -- Show 15/233 > 1/16
          norm_num
        constructor
        · -- Show 15/233 < 1/15
          norm_num
        constructor
        · -- Show numerator = 15
          norm_num
        · -- Show IsCoprime 15 233
          norm_num
      · -- Sixth element: 15/236
        constructor
        · -- Show 15/236 > 1/16
          norm_num
        constructor
        · -- Show 15/236 < 1/15
          norm_num
        constructor
        · -- Show numerator = 15
          norm_num
        · -- Show IsCoprime 15 236
          norm_num
      · -- Seventh element: 15/238
        constructor
        · -- Show 15/238 > 1/16
          norm_num
        constructor
        · -- Show 15/238 < 1/15
          norm_num
        constructor
        · -- Show numerator = 15
          norm_num
        · -- Show IsCoprime 15 238
          norm_num
      · -- Eighth element: 15/239
        constructor
        · -- Show 15/239 > 1/16
          norm_num
        constructor
        · -- Show 15/239 < 1/15
          norm_num
        constructor
        · -- Show numerator = 15
          norm_num
        · -- Show IsCoprime 15 239
          norm_num
  rw [h1]
  rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals
    norm_num