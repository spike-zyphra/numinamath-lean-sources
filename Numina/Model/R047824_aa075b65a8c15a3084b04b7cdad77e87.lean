import Mathlib

theorem algebra_302039 {a b c : ℝ} (ha : a^2 + 3 * a + 1 = (b + c) / 2)
    (hb : b^2 + 3 * b + 1 = (a + c) / 2) (hc : c^2 + 3 * c + 1 = (a + b) / 2) :
    a = -1 ∧ b = -1 ∧ c = -1 := by
  have h1 : (a + 1)^2 + (b + 1)^2 + (c + 1)^2 = 0 := by
    nlinarith
  have ha1 : (a + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
  have hb1 : (b + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
  have hc1 : (c + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
  have ha2 : a + 1 = 0 := by
    rwa [sq_eq_zero_iff] at ha1
  have hb2 : b + 1 = 0 := by
    rwa [sq_eq_zero_iff] at hb1
  have hc2 : c + 1 = 0 := by
    rwa [sq_eq_zero_iff] at hc1
  constructor
  · -- Prove a = -1
    linarith
  constructor
  · -- Prove b = -1
    linarith
  · -- Prove c = -1
    linarith