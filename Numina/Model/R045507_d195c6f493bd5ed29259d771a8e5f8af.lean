import Mathlib

open Real Set

theorem algebra_265669 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a + b = 2) :
    (a ^ 2 + b ^ 2) / (a * b + 1) ∈ Icc 1 14 := by
  have h1 : b = 2 - a := by linarith
  have h2 : 0 ≤ b := by linarith [show 0 ≤ 2 - a by nlinarith [h, ha], h1]

  constructor
  · -- Show that 1 ≤ (a ^ 2 + b ^ 2) / (a * b + 1)
    apply (le_div_iff₀ (by nlinarith)).mpr
    have h4 : a * b ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), h1, h]
    nlinarith [sq_nonneg (a - b), h1, h4]
  · -- Show that (a ^ 2 + b ^ 2) / (a * b + 1) ≤ 14
    apply (div_le_iff₀ (by nlinarith)).mpr
    have h5 : a ^ 2 + b ^ 2 ≤ 14 * (a * b + 1) := by
      rw [show b = 2 - a by linarith]
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a - (2 - a)), sq_nonneg (a * (2 - a) - 1)]
    linarith