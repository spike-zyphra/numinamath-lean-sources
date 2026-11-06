import Mathlib

theorem algebra_283572 (a b c : ℝ) (ha : a < b) (hb : b < c) (h1 : a + b + c = 6)
    (h2 : a * b + b * c + a * c = 9) :
    0 < a ∧ a < 1 ∧ 1 < b ∧ b < 3 ∧ 3 < c ∧ c < 4 := by
  have hc : c = 6 - a - b := by linarith
  rw [hc] at h2
  constructor
  · -- Prove 0 < a
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (a - b), sq_nonneg ((6 - a - b) - a), sq_nonneg ((6 - a - b) - b)]
  constructor
  · -- Prove a < 1
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - b), sq_nonneg ((6 - a - b) - a), sq_nonneg ((6 - a - b) - b)]
  constructor
  · -- Prove 1 < b
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - b), sq_nonneg ((6 - a - b) - a), sq_nonneg ((6 - a - b) - b)]
  constructor
  · -- Prove b < 3
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - b), sq_nonneg ((6 - a - b) - a), sq_nonneg ((6 - a - b) - b)]
  constructor
  · -- Prove 3 < c
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - b), sq_nonneg ((6 - a - b) - a), sq_nonneg ((6 - a - b) - b)]
  · -- Prove c < 4
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 3), sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - b), sq_nonneg ((6 - a - b) - a), sq_nonneg ((6 - a - b) - b)]