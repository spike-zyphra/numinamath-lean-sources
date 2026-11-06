import Mathlib

theorem number_theory_237075 {a b c d e: ℤ} (l1: a < b) (l2: b < c) (l3: c < d) (l4: d < e)
  (h: a * b * c * d * e = 12) : e = 3 := by
  have h2 : a ∣ 12 := by
    use (b * c * d * e)
    all_goals linarith
  have h3 : b ∣ 12 := by
    use (a * c * d * e)
    all_goals linarith
  have h4 : c ∣ 12 := by
    use (a * b * d * e)
    all_goals linarith
  have h5 : d ∣ 12 := by
    use (a * b * c * e)
    all_goals linarith
  have h6 : e ∣ 12 := by
    use (a * b * c * d)
    all_goals linarith
  have h7 : a ≤ 12 := by
    apply Int.le_of_dvd (show 0 < (12 : ℤ) by norm_num) h2
  have h8 : b ≤ 12 := by
    apply Int.le_of_dvd (show 0 < (12 : ℤ) by norm_num) h3
  have h9 : c ≤ 12 := by
    apply Int.le_of_dvd (show 0 < (12 : ℤ) by norm_num) h4
  have h10 : d ≤ 12 := by
    apply Int.le_of_dvd (show 0 < (12 : ℤ) by norm_num) h5
  have h11 : e ≤ 12 := by
    apply Int.le_of_dvd (show 0 < (12 : ℤ) by norm_num) h6
  have h12 : -12 ≤ a := by 
    have h12 : -a ∣ 12 := by 
      exact Int.neg_dvd.2 h2
    have h13 : -a ≤ 12 := by
      apply Int.le_of_dvd (show 0 < (12 : ℤ) by norm_num) h12
    linarith
  have h13 : -12 ≤ b := by 
    have h14 : -b ∣ 12 := by 
      exact Int.neg_dvd.2 h3
    have h15 : -b ≤ 12 := by
      apply Int.le_of_dvd (show 0 < (12 : ℤ) by norm_num) h14
    linarith
  have h14 : -12 ≤ c := by 
    have h15 : -c ∣ 12 := by 
      exact Int.neg_dvd.2 h4
    have h16 : -c ≤ 12 := by
      apply Int.le_of_dvd (show 0 < (12 : ℤ) by norm_num) h15
    linarith
  have h15 : -12 ≤ d := by 
    have h16 : -d ∣ 12 := by 
      exact Int.neg_dvd.2 h5
    have h17 : -d ≤ 12 := by
      apply Int.le_of_dvd (show 0 < (12 : ℤ) by norm_num) h16
    linarith
  have h16 : -12 ≤ e := by 
    have h17 : -e ∣ 12 := by 
      exact Int.neg_dvd.2 h6
    have h18 : -e ≤ 12 := by
      apply Int.le_of_dvd (show 0 < (12 : ℤ) by norm_num) h17
    linarith
  interval_cases e <;> try { 
    omega
  } <;> try { 
    interval_cases d <;> try { 
      omega
    } <;> try { 
      interval_cases c <;> try { 
        omega
      } <;> try { 
        interval_cases b <;> try { 
          omega
        } <;> try { 
          interval_cases a <;> try { 
            omega
          }
        }
      }
    }
  }