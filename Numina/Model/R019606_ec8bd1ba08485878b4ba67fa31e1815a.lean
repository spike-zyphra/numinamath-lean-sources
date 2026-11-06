import Mathlib

theorem algebra_243814 (m n p q : ℤ) (h₀ : m > 0) (h₁ : n > 0) (h₂ : p > 0)
    (h₃ : q > 0) (h₄ : m ≠ n) (h₅ : m ≠ p) (h₆ : m ≠ q) (h₇ : n ≠ p) (h₈ : n ≠ q)
    (h₉ : p ≠ q) (h₁₀ : (7 - m) * (7 - n) * (7 - p) * (7 - q) = 4) :
    m + n + p + q = 28 := by
  have h1 : (7 - m) * (7 - n) * (7 - p) * (7 - q) = 4 := h₁₀
  have h2 : (7 - m) ∣ 4 := by
    use ( (7 - n) * (7 - p) * (7 - q) )
    all_goals linarith
  have h3 : (7 - n) ∣ 4 := by
    use ( (7 - m) * (7 - p) * (7 - q) )
    all_goals linarith
  have h4 : (7 - p) ∣ 4 := by
    use ( (7 - m) * (7 - n) * (7 - q) )
    all_goals linarith
  have h5 : (7 - q) ∣ 4 := by
    use ( (7 - m) * (7 - n) * (7 - p) )
    all_goals linarith
  have h6 : (7 - m) ≤ 4 := by
    apply Int.le_of_dvd (by norm_num) h2
  have h7 : (7 - m) ≥ -4 := by
    have h8 : (- (7 - m) ) ∣ 4 := by
      exact Int.neg_dvd.2 h2
    have h9 : - (7 - m) ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h8
    omega
  have h8 : (7 - n) ≤ 4 := by
    apply Int.le_of_dvd (by norm_num) h3
  have h9 : (7 - n) ≥ -4 := by
    have h10 : (- (7 - n) ) ∣ 4 := by
      exact Int.neg_dvd.2 h3
    have h11 : - (7 - n) ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h10
    omega
  have h10 : (7 - p) ≤ 4 := by
    apply Int.le_of_dvd (by norm_num) h4
  have h11 : (7 - p) ≥ -4 := by
    have h12 : (- (7 - p) ) ∣ 4 := by
      exact Int.neg_dvd.2 h4
    have h13 : - (7 - p) ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h12
    omega
  have h12 : (7 - q) ≤ 4 := by
    apply Int.le_of_dvd (by norm_num) h5
  have h13 : (7 - q) ≥ -4 := by
    have h14 : (- (7 - q) ) ∣ 4 := by
      exact Int.neg_dvd.2 h5
    have h15 : - (7 - q) ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h14
    omega
  interval_cases h : (7 - m) <;> 
    try { 
      omega
    } <;> 
    try { 
      interval_cases k : (7 - n) <;> 
        try { 
          omega
        } <;> 
        try { 
          interval_cases l : (7 - p) <;> 
            try { 
              omega
            } <;> 
            try { 
              interval_cases s : (7 - q) <;> 
                norm_num at h₁₀ ⊢ <;> 
                  try { 
                    omega 
                  }
            }
        }
    }