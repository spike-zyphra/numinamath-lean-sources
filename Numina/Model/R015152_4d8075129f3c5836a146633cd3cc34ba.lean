import Mathlib

theorem number_theory_3382 : Set.encard {x : ℝ | ∃ a b c : ℤ, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x = abs a / a + abs b / b + abs c / c} ≤ 4 := by
  have h1 : {x : ℝ | ∃ a b c : ℤ, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x = abs a / a + abs b / b + abs c / c} = {3, 1, -1, -3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: if x in the set, then x must be in {3, 1, -1, -3}
      rintro ⟨a, b, c, hab, hbc, hca, ha, hb, hc, hx⟩
      have h1 : (abs a : ℝ) / (a : ℝ) = 1 ∨ (abs a : ℝ) / (a : ℝ) = -1 := by
        have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
        have h2 : a > 0 ∨ a < 0 := by 
          cases' (ne_iff_lt_or_gt.mp ha) with hlt hgt
          all_goals tauto
        rcases h2 with h2 | h2
        · -- Case where a > 0
          have h3 : abs a = a := by
            rw [abs_of_pos h2]
          have h4 : (abs a : ℝ) / (a : ℝ) = 1 := by
            rw [show (abs a : ℝ) = (a : ℝ) by exact_mod_cast h3]
            field_simp [show (a : ℝ) ≠ 0 by exact_mod_cast ha]
          tauto
        · -- Case where a < 0
          have h3 : abs a = -a := by
            rw [abs_of_neg h2]
          have h4 : (abs a : ℝ) / (a : ℝ) = -1 := by
            rw [show (abs a : ℝ) = (-a : ℝ) by exact_mod_cast h3]
            field_simp [show (a : ℝ) ≠ 0 by exact_mod_cast ha]
          tauto
      have h2 : (abs b : ℝ) / (b : ℝ) = 1 ∨ (abs b : ℝ) / (b : ℝ) = -1 := by
        have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
        have h2 : b > 0 ∨ b < 0 := by 
          cases' (ne_iff_lt_or_gt.mp hb) with hlt hgt
          all_goals tauto
        rcases h2 with h2 | h2
        · -- Case where b > 0
          have h3 : abs b = b := by
            rw [abs_of_pos h2]
          have h4 : (abs b : ℝ) / (b : ℝ) = 1 := by
            rw [show (abs b : ℝ) = (b : ℝ) by exact_mod_cast h3]
            field_simp [show (b : ℝ) ≠ 0 by exact_mod_cast hb]
          tauto
        · -- Case where b < 0
          have h3 : abs b = -b := by
            rw [abs_of_neg h2]
          have h4 : (abs b : ℝ) / (b : ℝ) = -1 := by
            rw [show (abs b : ℝ) = (-b : ℝ) by exact_mod_cast h3]
            field_simp [show (b : ℝ) ≠ 0 by exact_mod_cast hb]
          tauto
      have h3 : (abs c : ℝ) / (c : ℝ) = 1 ∨ (abs c : ℝ) / (c : ℝ) = -1 := by
        have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
        have h2 : c > 0 ∨ c < 0 := by 
          cases' (ne_iff_lt_or_gt.mp hc) with hlt hgt
          all_goals tauto
        rcases h2 with h2 | h2
        · -- Case where c > 0
          have h3 : abs c = c := by
            rw [abs_of_pos h2]
          have h4 : (abs c : ℝ) / (c : ℝ) = 1 := by
            rw [show (abs c : ℝ) = (c : ℝ) by exact_mod_cast h3]
            field_simp [show (c : ℝ) ≠ 0 by exact_mod_cast hc]
          tauto
        · -- Case where c < 0
          have h3 : abs c = -c := by
            rw [abs_of_neg h2]
          have h4 : (abs c : ℝ) / (c : ℝ) = -1 := by
            rw [show (abs c : ℝ) = (-c : ℝ) by exact_mod_cast h3]
            field_simp [show (c : ℝ) ≠ 0 by exact_mod_cast hc]
          tauto
      rw [hx] at *
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> 
        norm_num [h1, h2, h3] at *
    · -- Second direction: each of {3,1,-1,-3} can be obtained
      rintro (rfl | rfl | rfl | rfl)
      · -- Case where x = 3 
        use 1, 2, 3 
        norm_num [abs_of_pos]
      · -- Case where x = 1 
        use 1, -2, 3 
        norm_num [abs_of_pos, abs_of_neg]
      · -- Case where x = -1 
        use 1, -2, -3 
        norm_num [abs_of_pos, abs_of_neg]
      · -- Case where x = -3 
        use -1, -2, -3 
        norm_num [abs_of_neg]
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals norm_num