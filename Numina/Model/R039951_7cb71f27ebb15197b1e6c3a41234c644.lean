import Mathlib

theorem inequalities_207387 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a * b * c = 1) (hinv : a + b + c > 1 / a + 1 / b + 1 / c) :
    a > 1 ∧ b ≤ 1 ∧ c ≤ 1 ∨ b > 1 ∧ a ≤ 1 ∧ c ≤ 1 ∨ c > 1 ∧ a ≤ 1 ∧ b ≤ 1 := by

  have h1 : 1 / a = b * c := by
    field_simp [ha.ne.symm]
    nlinarith [hsum]
  have h2 : 1 / b = a * c := by
    field_simp [hb.ne.symm]
    nlinarith [hsum]
  have h3 : 1 / c = a * b := by
    field_simp [hc.ne.symm]
    nlinarith [hsum]
  have h4 : a + b + c > b * c + a * c + a * b := by
    have h5 : 1 / a + 1 / b + 1 / c = b * c + a * c + a * b := by
      rw [h1, h2, h3]
    linarith [h5, hinv]
  
  by_cases ha1 : a > 1
  · -- Assume a > 1, need to prove b ≤ 1 ∧ c ≤ 1
    have h5 : b ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                  hsum, h4]
    have h6 : c ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                  hsum, h4]
    left
    exact ⟨ha1, h5, h6⟩
  · -- Assume not (a > 1)
    by_cases hb1 : b > 1
    · -- Assume b > 1
      have h7 : c ≤ 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                    hsum, h4]
      right
      left
      exact ⟨hb1, by nlinarith, h7⟩
    · -- Assume not (b > 1)
      have hc1 : c > 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                    hsum, h4]
      right
      right
      exact ⟨hc1, by nlinarith, by nlinarith⟩