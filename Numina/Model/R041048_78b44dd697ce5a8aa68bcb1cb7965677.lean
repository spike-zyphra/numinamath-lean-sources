import Mathlib

theorem algebra_2484 {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + b = c + d) (h2 : a * b + 1 = c * d) : c = d := by
  have h3 : b = c + d - a := by
    omega
  rw [h3] at h2
  have h4 : c = d := by
    have eq1 : (c - a) * (a - d) = -1 := by 
      nlinarith [sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (c - d), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
        ]
    have eq2 : (c - a) = 1 ∨ (c - a) = -1 := by
      have h6 : (c - a) * (a - d) = -1 := eq1
      have h7 : (c - a) ∣ -1 := by
        use (a - d)
        all_goals linarith
      have h8 : (c - a) ∣ 1 := by 
        exact Int.dvd_neg.mp h7
      have h9 : (c - a) = 1 ∨ (c - a) = -1 := by
        have h4 : (c - a) ∣ 1 := h8
        have h5 : (c - a) ≤ 1 := by 
          exact Int.le_of_dvd (by norm_num) h4
        have h6 : (c - a) ≥ -1 := by
          have h7 : (- (c - a)) ∣ 1 := by
            exact Int.neg_dvd.2 h4
          have h8 : - (c - a) ≤ 1 := by 
            exact Int.le_of_dvd (by norm_num) h7
          omega
        interval_cases (c - a) <;> tauto
      assumption
    cases eq2 with
    | inl h10 =>
      -- (c - a) = 1 
      have h11 : a - d = -1 := by 
        nlinarith
      -- So, solving we get c = d
      -- c = a + 1 and a = d - 1, so c = (d - 1) + 1 = d
      have h12 : c = a + 1 := by 
        omega
      have h13 : a = d - 1 := by 
        omega
      omega
    | inr h11 =>
      -- (c - a) = -1 
      have h12 : a - d = 1 := by 
        nlinarith
      -- So, solving we get c = d
      -- c = a - 1 and a = d + 1, so c = (d + 1) - 1 = d
      have h13 : c = a - 1 := by 
        omega
      have h14 : a = d + 1 := by 
        omega
      omega
  assumption