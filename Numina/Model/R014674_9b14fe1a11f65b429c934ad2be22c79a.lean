import Mathlib

theorem inequalities_227184 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a * b * c = 1) (hrec : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by
  have eq1 : 1 / a = b * c := by
    field_simp
    nlinarith [hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have eq2 : 1 / b = a * c := by
    field_simp
    nlinarith [hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have eq3 : 1 / c = a * b := by
    field_simp
    nlinarith [hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  rw [eq1, eq2, eq3] at hrec
  have h1 : (a - 1) * (b - 1) * (c - 1) > 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  by_cases ha1 : a > 1
  · -- Assume a > 1
    -- We need to prove the first disjunction
    have h21 : b ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1, ha1]
    have h22 : c ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1, ha1]
    left
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  by_cases hb1 : b > 1
  · -- Assume b > 1
    -- We need to prove the second disjunction
    have h21 : a ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1, hb1]
    have h22 : c ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1, hb1]
    right
    left
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  · -- Assume not a > 1 and not b > 1
    -- We need to prove the third disjunction
    have h21 : a ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1, ha1, hb1]
    have h22 : b ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1, ha1, hb1]
    have hc1 : c > 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1, ha1, hb1]
    right
    right
    constructor
    · linarith
    constructor
    · linarith
    · linarith