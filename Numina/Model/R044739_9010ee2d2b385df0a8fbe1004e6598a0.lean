import Mathlib

theorem algebra_301067 (f : ℤ → ℤ) (hf : f = fun x => x ^ 2 - 196 * x + 9612) :
    Set.ncard {x | ∃ m n, x = m ∧ f x = n ^ 2} = 2 := by
  have h1 : {x | ∃ m n, x = m ∧ f x = n ^ 2} = {97, 99} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume h_eq : ∃ m n, x = m ∧ f x = n ^ 2, prove x = 97 ∨ x = 99
      rintro ⟨m, n, rfl, hn⟩
      rw [hf] at hn
      simp at hn
      have h_eq : (x - 98 : ℤ) ^ 2 - (n : ℤ) ^ 2 = -8 := by
        nlinarith
      have h_eq2 : (x - 98 - n) * (x - 98 + n) = -8 := by
        ring_nf at h_eq ⊢
        nlinarith
      have h2 : x = 97 ∨ x = 99 := by
        have h3 : (x - 98 - n) ∣ -8 := by
          use (x - 98 + n)
          all_goals nlinarith
        have h4 : (x - 98 - n) ∣ (8 : ℤ) := by
          have h5 : (x - 98 - n) ∣ (-8 : ℤ) := h3
          have h6 : (x - 98 - n) ∣ (8 : ℤ) := by
            exact Int.dvd_neg.mp h5
          assumption
        have h5 : (x - 98 - n) ≤ 8 := by
          exact Int.le_of_dvd (show (8 : ℤ) > 0 by norm_num) h4
        have h6 : (x - 98 - n) ≥ -8 := by
          have h7 : (- (x - 98 - n) ) ∣ (8 : ℤ) := by 
            exact Int.neg_dvd.2 h4
          have h8 : - (x - 98 - n) ≤ 8 := by
            apply Int.le_of_dvd (show (8 : ℤ) > 0 by norm_num) h7
          omega
        interval_cases h : (x - 98 - n) <;> try { 
          omega
        } <;> try { 
          norm_num at h_eq2 h_eq 
          all_goals try { 
            have : n = 3 := by nlinarith 
            rw [this] at h_eq 
            have : x = 97 := by nlinarith 
            simp at this 
            tauto 
          } <;> try { 
            have : n = -3 := by nlinarith 
            rw [this] at h_eq 
            have : x = 99 := by nlinarith 
            simp at this 
            tauto 
          }
        }
      tauto
    · -- Assume h_eq2 : x = 97 ∨ x = 99, prove ∃ m n, x = m ∧ f x = n ^ 2
      rintro (h_eq2 | h_eq2)
      · -- h_eq2 : x = 97
        rw [h_eq2]
        use 97, 3
        all_goals norm_num [hf] 
      · -- h_eq2 : x = 99
        rw [h_eq2]
        use 99, 3
        all_goals norm_num [hf] 
  rw [h1]
  rw [Set.ncard_pair]
  all_goals norm_num 
  all_goals linarith 
  all_goals linarith 
  all_goals norm_num 
  all_goals linarith