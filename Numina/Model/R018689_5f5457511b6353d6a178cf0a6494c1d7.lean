import Mathlib

theorem number_theory_1015 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (h1 : a < b) (h2 : b < c) (h3 : a + b + c = 44) (h4 : a * b + 3 = c) : a * b + c = 55 := by
  have h8 : a * b + a + b = 41 := by
    nlinarith [h3, h4]

  have h9 : a ≤ 41 := by
    nlinarith
  have h10 : b ≤ 41 := by
    nlinarith
  interval_cases a <;> try { 
    omega 
  } <;> try { 
    interval_cases b <;> norm_num at h8 ha hb h1 h2 ⊢ <;> try { 
      omega 
    } <;> try { 
        interval_cases c <;> norm_num at h3 h4 ha hb hc h1 h2 ⊢ <;> try { 
          all_goals tauto 
        }
      }
  }