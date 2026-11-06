import Mathlib

theorem number_theory_34130 :
    {(a, b, c) : ℤ × ℤ × ℤ | a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a + b + c = a * b * c ∧ ∃ d, b = a + d ∧ c = b + d}.ncard = 4 := by 
  have : {(a, b, c) : ℤ × ℤ × ℤ | a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a + b + c = a * b * c ∧ ∃ d, b = a + d ∧ c = b + d} = {(-3, -2, -1), (-1, -2, -3), (1, 2, 3), (3, 2, 1)} := by
    ext ⟨a, b, c⟩
    simp 
    constructor
    · -- Assume the conditions hold
      rintro ⟨ha, hb, hc, heq, ⟨d, h1, h2⟩⟩ 
      have h3 : c = a + 2 * d := by
        linarith [h2, h1]
      have h4 : a + b + c = 3 * a + 3 * d := by
        rw [show b = a + d by linarith [h1], show c = a + 2 * d by linarith [h3]]
        all_goals ring
      have h5 : a * b * c = a * (a + d) * (a + 2 * d) := by
        rw [show b = a + d by linarith [h1], show c = a + 2 * d by linarith [h3]]
        all_goals ring
      rw [h4, h5] at heq
      have h6 : a * (a + 2 * d) = 3 := by
        have hne : a + d ≠ 0 := by
          by_contra h
          have : b = 0 := by
            nlinarith [h1, h]
          contradiction 
        have h7 : 3 = a * (a + 2 * d) := by
          apply (mul_left_inj' hne).mp 
          linarith 
        linarith 
      have h7 : a * (a + 2 * d) = 3 := h6 
      have h8 : a ∣ 3 := by
        use a + 2 * d 
        all_goals linarith 
      have h9 : a + 2 * d ∣ 3 := by
        use a
        all_goals linarith 
      have h10 : a ≤ 3 := by
        apply Int.le_of_dvd (by norm_num) h8 
      have h11 : a ≥ -3 := by
        have h12 : (-a) ∣ 3 := by 
          exact Int.neg_dvd.2 h8 
        have h13 : -a ≤ 3 := by
          apply Int.le_of_dvd (by norm_num) h12 
        omega 
      interval_cases a <;> omega 
    · -- Show that the elements in the right side satisfy the conditions
      rintro (h | h | h | h)
      · -- First element: (-3, -2, -1)
        rcases h with ⟨rfl, rfl, rfl⟩ 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · refine ⟨1, by norm_num, by norm_num⟩ 
      · -- Second element: (-1, -2, -3)
        rcases h with ⟨rfl, rfl, rfl⟩ 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · refine ⟨-1, by norm_num, by norm_num⟩ 
      · -- Third element: (1, 2, 3)
        rcases h with ⟨rfl, rfl, rfl⟩ 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · refine ⟨1, by norm_num, by norm_num⟩ 
      · -- Fourth element: (3, 2, 1)
        rcases h with ⟨rfl, rfl, rfl⟩ 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · refine ⟨-1, by norm_num, by norm_num⟩ 
  rw [this] 
  rw [Set.ncard_eq_toFinset_card']
  simp 
  <;> try { native_decide }