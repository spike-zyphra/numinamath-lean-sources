import Mathlib

theorem inequalities_37676 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a * b * c = 1) (hinv : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by
  have h2 : 1 / a = b * c := by 
    have ha' : a ≠ 0 := by linarith
    field_simp
    nlinarith [hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h3 : 1 / b = a * c := by 
    have hb' : b ≠ 0 := by linarith
    field_simp
    nlinarith [hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h4 : 1 / c = a * b := by 
    have hc' : c ≠ 0 := by linarith
    field_simp
    nlinarith [hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h5 : a + b + c > b * c + a * c + a * b := by
    rw [h2, h3, h4] at hinv
    nlinarith
  by_cases ha1 : a > 1
  · -- Assume a > 1, need to prove b ≤ 1 and c ≤ 1
    by_cases hb1 : b > 1
    · -- Assume b > 1, derive contradiction
      have hb1 : b > 1 := by assumption
      have hc1 : c < 1 := by
        nlinarith [hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, ha1, hb1]
      nlinarith [h5, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    · -- Assume ¬(b > 1), so b ≤ 1
      have hb1 : b ≤ 1 := by linarith
      by_cases hc1 : c > 1
      · -- Assume c > 1, derive contradiction
        have hc1 : c > 1 := by assumption
        have hb1 : b < 1 := by
          nlinarith [hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, ha1, hc1]
        nlinarith [h5, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
      · -- Assume ¬(c > 1), so c ≤ 1
        have hc1 : c ≤ 1 := by linarith
        left
        constructor
        · exact ha1
        constructor
        · exact hb1
        · exact hc1
  · -- Assume ¬(a > 1), so a ≤ 1
    have ha1 : a ≤ 1 := by linarith
    by_cases hb1 : b > 1
    · -- Assume b > 1, need to prove a ≤ 1 and c ≤ 1
      have hb1 : b > 1 := by assumption
      by_cases hc1 : c > 1
      · -- Assume c > 1, contradiction
        have hc1 : c > 1 := by assumption
        nlinarith [h5, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
      · -- Assume ¬(c > 1), so c ≤ 1
        have hc1 : c ≤ 1 := by linarith
        right
        left
        constructor
        · exact hb1
        constructor
        · exact ha1
        · exact hc1
    · -- Assume ¬(b > 1), so b ≤ 1
      have hb1 : b ≤ 1 := by linarith
      by_cases hc1 : c > 1
      · -- Assume c > 1, prove it
        have hc1 : c > 1 := by assumption
        right
        right
        constructor
        · exact hc1
        constructor
        · exact ha1
        · exact hb1
      · -- Assume ¬(c > 1), so c ≤ 1
        have hc1 : c ≤ 1 := by linarith
        nlinarith [h5, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]