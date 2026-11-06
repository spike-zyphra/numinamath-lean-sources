import Mathlib

open Real

theorem inequalities_115946 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + 1) * (b + 1) * (c + 1) = 8) :
    (3 ≤ a + b + c ∧ a * b * c ≤ 1) ∧ 
    (3 = a + b + c ∧ a * b * c = 1 ↔ a = 1 ∧ b = 1 ∧ c = 1) :=
by
  constructor
  · -- First part: proving 3 ≤ a + b + c and a * b * c ≤ 1
    constructor
    · -- Prove 3 ≤ a + b + c
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    · -- Prove a * b * c ≤ 1
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  · -- Second part: proving (3 = a + b + c ∧ a * b * c = 1 ↔ a = 1 ∧ b = 1 ∧ c = 1)
    constructor
    · -- Assume (3 = a + b + c ∧ a * b * c = 1), prove a = 1 ∧ b = 1 ∧ c = 1
      rintro ⟨h1, h2⟩
      have h3 : (a - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have ha1 : a - 1 = 0 := by
        rw [sq_eq_zero_iff] at h3
        linarith
      have ha2 : a = 1 := by linarith
      have h4 : (b - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have hb1 : b - 1 = 0 := by
        rw [sq_eq_zero_iff] at h4
        linarith
      have hb2 : b = 1 := by linarith
      have h5 : (c - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have hc1 : c - 1 = 0 := by
        rw [sq_eq_zero_iff] at h5
        linarith
      have hc2 : c = 1 := by linarith
      exact ⟨ha2, hb2, hc2⟩
    · -- Assume a = 1 ∧ b = 1 ∧ c = 1, prove 3 = a + b + c ∧ a * b * c = 1
      rintro ⟨ha1, hb1, hc1⟩
      constructor
      · -- Show 3 = a + b + c
        rw [ha1, hb1, hc1]
        norm_num
      · -- Show a * b * c = 1
        rw [ha1, hb1, hc1]
        norm_num