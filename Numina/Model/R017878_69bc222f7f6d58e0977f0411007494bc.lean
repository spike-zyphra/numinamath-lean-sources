import Mathlib

open Real

theorem inequalities_293909 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≤ b + c) (h2 : b ≤ a + c) (h3 : b + c ≤ 2 * a) (h4 : a + c ≤ 2 * b) :
    2 / 3 ≤ b / a ∧ b / a ≤ 3 / 2 := by

  have h7 : 2 * a ≤ 3 * b := by
    nlinarith
  have h8 : 2 * b ≤ 3 * a := by
    nlinarith

  constructor
  · -- proving the left side
    have h9 : 2 / 3 ≤ b / a := by
      have h10 : 0 < (a : ℝ) := ha
      apply (le_div_iff₀ (by linarith)).mpr
      nlinarith
    exact h9
  · -- proving the right side
    have h10 : b / a ≤ 3 / 2 := by
      have h11 : 0 < (a : ℝ) := ha
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    exact h10