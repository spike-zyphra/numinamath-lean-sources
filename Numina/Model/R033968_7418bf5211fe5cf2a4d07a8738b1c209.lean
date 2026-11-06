import Mathlib

theorem number_theory_94407 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 100 ∧ a < b ∧ b < c}.ncard = 4 := by

  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 100 ∧ a < b ∧ b < c} =
      {(1, 2, 50), (1, 4, 25), (1, 5, 20), (2, 5, 10)} := by
    ext ⟨a, b, c⟩
    simp
    constructor
    ·
      rintro ⟨ha, hb, hc, h1, h2, h3⟩
      have h4 : a < c := by 
        nlinarith
      have h5 : a ≤ 4 := by
        by_contra h
        push_neg at h 
        have h6 : a * b * c > 100 := by
          have h7 : a ≥ 5 := by linarith
          have h8 : b ≥ a + 1 := by linarith
          have h9 : c ≥ b + 1 := by linarith
          have h10 : b ≥ 6 := by 
            nlinarith 
          have h11 : c ≥ 7 := by 
            nlinarith 
          have h12 : c ≥ 7 := by linarith
          have h13 : a * b ≥ 30 := by 
            nlinarith 
          nlinarith 
        nlinarith 
      interval_cases a <;> try { 
        norm_num at h1 
        have h8 : b ≤ 50 := by 
          nlinarith
        interval_cases b <;> omega 
      }

    · 
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      all_goals
        constructor
        all_goals 
          norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide