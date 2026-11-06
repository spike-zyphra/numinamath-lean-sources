import Mathlib

theorem number_theory_196078 (a b c : ℕ) : 
    0 ≤ a ∧ a < 10 ∧ 10 ≤ b ∧ b < 100 ∧ 100 ≤ c ∧ c < 1000 ∧ 
    Even b ∧ Odd a ∧ Odd c ∧ 
    a * b * c = (a + b + c) * 100 + 68 ∧ 
    IsSquare (a + b + c) ∧ IsSquare (b + c / 100 * 100) ∧ IsSquare (c % 100) ↔
    a = 3 ∧ b = 44 ∧ c = 149 := by
  constructor
  · -- Forward: if conditions hold, then a = 3, b = 44, c = 149
    rintro ⟨ha0, ha1, hb0, hb1, hc0, hc1, hevenb, hoda, hoax, heq, hs, hsq1, hsq2⟩
    have h1 : a < 10 := by linarith
    have h2 : b < 100 := by linarith
    have h3 : c < 1000 := by linarith
    interval_cases a <;> interval_cases b <;> 
      try { 
        omega 
      } <;> norm_num [Nat.odd_iff, Nat.even_iff] at hevenb hoda hoax 
      <;> 
        try { 
          omega 
        } <;> 
          try { 
            all_goals 
            try { 
              { 
                have hc' : c = 271 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            } 
            <;> try { 
              { 
                have hc' : c = 59 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 271 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 71 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 155 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 31 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 87 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 91 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 19 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 131 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 163 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 199 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> try { 
              { 
                have hc' : c = 271 := by nlinarith 
                rw [hc'] at hs 
                contrapose! hs 
                all_goals native_decide 
              }
            }
            <;> tauto 
          }
  · -- Backward
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num 
    constructor
    · norm_num 
    constructor
    · norm_num 
    constructor
    · norm_num 
    constructor
    · norm_num 
    constructor
    · norm_num 
    constructor
    · -- Even b
      norm_num [Nat.even_iff]
    constructor
    · -- Odd a
      norm_num [Nat.odd_iff]
    constructor
    · -- Odd c
      norm_num [Nat.odd_iff]
    constructor
    · -- a * b * c = (a + b + c) * 100 + 68
      norm_num 
    constructor
    · -- IsSquare (a + b + c)
      native_decide 
    constructor
    · -- IsSquare (b + c / 100 * 100)
      native_decide 
    · -- IsSquare (c % 100)
      native_decide