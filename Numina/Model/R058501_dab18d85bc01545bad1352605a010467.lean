import Mathlib

theorem inequalities_186311 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a * b * c = 1) (hrec : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by
  have h1 : 1 / a = b * c := by
    field_simp [ha.ne.symm]
    nlinarith [hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h2 : 1 / b = a * c := by
    field_simp [hb.ne.symm]
    nlinarith [hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h3 : 1 / c = a * b := by
    field_simp [hc.ne.symm]
    nlinarith [hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  rw [h1, h2, h3] at hrec
  -- Now the inequality is $a + b + c > b \cdot c + a \cdot c + a \cdot b$
  have h2 : a + b + c > a * b + b * c + c * a := by nlinarith
  -- Now, establish the theorem by case analysis
  by_cases ha1 : a > 1
  · -- Assume a > 1, need to show b, c <= 1
    have h3 : b * c < 1 := by
      nlinarith [hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have hb1 : b ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        hsum, h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have hc1 : c ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        hsum, h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    left
    exact ⟨ha1, hb1, hc1⟩
  · -- Assume a ≤ 1, need to determine either b or c exceeds 1
    have ha1 : a ≤ 1 := by linarith
    by_cases hb1 : b > 1
    · -- Assume b > 1, need to show c <= 1
      have h3 : a * c < 1 := by
        nlinarith [hsum, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have hc1 : c ≤ 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          hsum, h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      exact Or.inr (Or.inl ⟨hb1, by nlinarith, hc1⟩)
    · -- Assume b ≤ 1, need to determine c exceeds 1
      have hb1 : b ≤ 1 := by linarith
      have hc1 : c > 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          hsum, h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      exact Or.inr (Or.inr ⟨hc1, by nlinarith, by nlinarith⟩)