import Mathlib

open Real

theorem inequalities_178105 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a * b = 1) :
    (a + 1) * (b + 1) ≥ 4 ∧
    ((a + 1) * (b + 1) = 4 ↔ a = b) := by
  constructor
  · -- Expanding (a + 1) * (b + 1) using the fact that ab = 1, we get a * b + a + b + 1 = 1 + a + b + 1 = a + b + 2.
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1)]
  · -- For the equality condition, we need to prove it goes both ways
    constructor
    · -- First direction: assuming (a + 1) * (b + 1) = 4, prove a = b
      intro h_eq
      have h1 : a + b = 2 := by
        nlinarith [hab, h_eq]
      have h2 : (a - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1)]
      have ha1 : a - 1 = 0 := by
        nlinarith
      have ha2 : a = 1 := by linarith
      have hb2 : b = 1 := by linarith [h1, ha2]
      linarith
    · -- Second direction: assuming a = b, prove (a + 1) * (b + 1) = 4
      intro h_eq
      have ha1 : a = 1 := by
        have ha2 : a = b := h_eq
        have hb2 : b = a := by linarith
        rw [hb2] at hab
        have ha3 : a ^ 2 = 1 := by nlinarith
        have ha4 : a = 1 := by
          nlinarith
        exact ha4
      have hb1 : b = 1 := by
        linarith [ha1, h_eq]
      rw [ha1, hb1]
      norm_num