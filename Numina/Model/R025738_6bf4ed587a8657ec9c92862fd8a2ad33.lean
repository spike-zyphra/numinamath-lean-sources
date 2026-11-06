import Mathlib

theorem number_theory_210246 (a b c d : ℤ) (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h : (a - 2024) * (b - 2024) * (c - 2024) * (d - 2024) = 9) :
    a + b + c + d = 8096 := by

  have h1 : (a - 2024) * (b - 2024) * (c - 2024) * (d - 2024) = 9 := h
  have h2 : (a - 2024) ∣ 9 := by 
    use (b - 2024) * (c - 2024) * (d - 2024)
    all_goals linarith
  have h3 : (b - 2024) ∣ 9 := by 
    use (a - 2024) * (c - 2024) * (d - 2024)
    all_goals linarith

  have h4 : (c - 2024) ∣ 9 := by 
    use (a - 2024) * (b - 2024) * (d - 2024)
    all_goals linarith

  have h5 : (d - 2024) ∣ 9 := by 
    use (a - 2024) * (b - 2024) * (c - 2024)
    all_goals linarith

  have h61 : (a - 2024) ≤ 9 := by 
    apply Int.le_of_dvd (by norm_num) h2

  have h62 : (a - 2024) ≥ -9 := by 
    have h8 : (- (a - 2024)) ∣ 9 := by 
      exact Int.neg_dvd.2 h2 
    have h9 : - (a - 2024) ≤ 9 := by 
      apply Int.le_of_dvd (by norm_num) h8 
    omega

  have h71 : (b - 2024) ≤ 9 := by 
    apply Int.le_of_dvd (by norm_num) h3

  have h72 : (b - 2024) ≥ -9 := by 
    have h8 : (- (b - 2024)) ∣ 9 := by 
      exact Int.neg_dvd.2 h3 
    have h9 : - (b - 2024) ≤ 9 := by 
      apply Int.le_of_dvd (by norm_num) h8 
    omega

  have h81 : (c - 2024) ≤ 9 := by 
    apply Int.le_of_dvd (by norm_num) h4

  have h82 : (c - 2024) ≥ -9 := by 
    have h8 : (- (c - 2024)) ∣ 9 := by 
      exact Int.neg_dvd.2 h4 
    have h9 : - (c - 2024) ≤ 9 := by 
      apply Int.le_of_dvd (by norm_num) h8 
    omega

  have h91 : (d - 2024) ≤ 9 := by 
    apply Int.le_of_dvd (by norm_num) h5

  have h92 : (d - 2024) ≥ -9 := by 
    have h8 : (- (d - 2024)) ∣ 9 := by 
      exact Int.neg_dvd.2 h5 
    have h9 : - (d - 2024) ≤ 9 := by 
      apply Int.le_of_dvd (by norm_num) h8 
    omega

  interval_cases h88 : (d - 2024) <;> 
    try { 
      omega 
    } 
    <;> 
      interval_cases h87 : (c - 2024) <;> 
        try { 
          omega 
        } 
        <;> 
          interval_cases h86 : (b - 2024) <;> 
            try { 
              omega 
            } 
            <;> 
              interval_cases h85 : (a - 2024) <;> 
                omega