import Mathlib

theorem number_theory_28369 (p q r: ℤ) (hp: Prime p) (hq: Prime q) (hr: Prime r)
    (l1: 5 ≤ p) (l2: p < q) (l3: q < r) (h1: 2 * p ^ 2 - r ^ 2 ≥ 49)
    (h2: 2 * q ^ 2 - r ^ 2 ≤ 193): p = 17 ∧ q = 19 ∧ r = 23 := by
  have h3 : q ≤ p + 7 := by
    nlinarith [h1, h2, sq_nonneg (q - p), sq_nonneg (r - q)]
  have h5 : p ≤ 35 := by
    nlinarith [h1, h3, sq_nonneg (r - p), sq_nonneg (q - p), sq_nonneg (r), sq_nonneg (q ^ 2 - p ^ 2)]
  interval_cases p <;> try { 
    norm_num at hp l1 
    <;> 
    try { 
      have h6 : q ≤ 42 := by 
        nlinarith [h3, h5] 
      interval_cases q <;> norm_num at hq l2 l3 h1 h2 <;> 
        try { 
          have h7 : r ≤ 62 := by 
            nlinarith [h1, h2] 
          interval_cases r <;> norm_num at h1 h2 <;> 
            try { 
              tauto 
            } 
        }
    }
  }