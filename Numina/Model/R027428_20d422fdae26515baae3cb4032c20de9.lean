import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_218023 (a : ℝ) :
  (∀ x : ℝ, |x| ≤ 1 → x^2 - (a + 1) * x + a + 1 > 0) ↔ a > -1 := by
  constructor
  · -- Assume that for all x, |x| ≤ 1 → x^2 - (a + 1) * x + a + 1 > 0, prove a > -1
    intro h
    by_contra ha
    push_neg at ha
    have h1 := h 0 (by
      norm_num
    )
    nlinarith
  · -- Assume a > -1 prove ∀ x : ℝ, |x| ≤ 1 → x^2 - (a + 1) * x + a + 1 > 0
    intro ha x hx
    have h1 : -1 ≤ x ∧ x ≤ 1 := by
      constructor
      · -- Prove -1 ≤ x
        linarith [abs_le.mp hx]
      · -- Prove x ≤ 1
        linarith [abs_le.mp hx]
    have h2 : x^2 - (a + 1) * x + a + 1 > 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x - (a + 1) / 2), sq_nonneg (a + 1), 
          mul_nonneg (show 0 ≤ (1 - x) by linarith) (show 0 ≤ (x + 1) by linarith),
          mul_nonneg (show 0 ≤ (x - (-1)) by linarith) (show 0 ≤ (1 - x) by linarith)]
    linarith