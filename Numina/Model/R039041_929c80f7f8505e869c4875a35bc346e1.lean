import Mathlib

theorem number_theory_1040 :
    Set.ncard {p : ℕ × ℕ | p.1 ≤ 15 ∧ p.2 ≤ 15 ∧ (1 / 4 : ℚ) < (p.2 / p.1 : ℚ) ∧ (p.2 / p.1 : ℚ) < (1 / 3 : ℚ)} = 6 := by

  have h2 : {p : ℕ × ℕ | p.1 ≤ 15 ∧ p.2 ≤ 15 ∧ (1 / 4 : ℚ) < (p.2 / p.1 : ℚ) ∧ (p.2 / p.1 : ℚ) < (1 / 3 : ℚ)} = 
          { (7, 2), (10, 3), (11, 3), (13, 4), (14, 4), (15, 4) } := by

    ext ⟨a, b⟩ 
    simp 
    constructor
    · rintro ⟨ha1, hb1, h1, h2⟩
      have h3 : a ≠ 0 := by
        by_contra h
        rw [h] at h1 h2
        norm_num at h1 h2
      have h4 : a ≤ 15 := ha1
      have h5 : b ≤ 15 := hb1
      --  turn rational numbers into integer inequality
      have h12 : (1 / 4 : ℚ) < (b / a : ℚ) := by linarith
      have h13 : (b / a : ℚ) < (1 / 3 : ℚ) := by
        linarith
      have h6 : 3 * b < a := by 
        have h61 : (3 * (b : ℚ) < (a : ℚ)) := by
          have h8 : 0 < (a : ℚ) := by
            exact_mod_cast (show 0 < a by omega)
          apply (div_lt_div_iff (by linarith) (by linarith)).mp at h13
          linarith
        exact_mod_cast h61 
      have h7 : a < 4 * b := by
        have h71 : (a : ℚ) < 4 * (b : ℚ) := by 
          have h8 : 0 < (a : ℚ) := by 
            exact_mod_cast (show 0 < a by omega)
          apply (div_lt_div_iff (by linarith) (by linarith)).mp at h12 
          linarith
        exact_mod_cast h71 
      have h8 : b < 5 := by
        nlinarith 
      interval_cases b <;> try { 
        omega 
      }
    · -- Show that (7, 2), (10, 3), (11, 3), (13, 4), (14, 4), (15, 4) satisfy the constraints 
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals 
      norm_num 
  rw [h2]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]