import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_320621 {x : ℝ} (hx : x ≠ 3) :
    ¬|x + 1| > 2 → ¬(1 / (3 - x)) > 1 := by
  intro h
  by_contra h2
  have h1 : |x + 1| ≤ 2 := by
    simpa using h
  have h3 : -3 ≤ x := by
    linarith [abs_le.mp h1]
  have h4 : x ≤ 1 := by
    linarith [abs_le.mp h1]
  have h5 : 1 / (3 - x) > 1 := by
    simpa using h2
  by_cases h6 : 3 - x > 0
  · -- Case where 3 - x > 0, so x < 3
    have h15 : (1 - (3 - x)) / (3 - x) > 0 := by
      have h13 : 1 / (3 - x) - (1 : ℝ) > 0 := by linarith
      have h16 : 1 / (3 - x) - (1 : ℝ) = (1 - (3 - x)) / (3 - x) := by
        field_simp [(show (3 - x) ≠ 0 by intro h17; apply hx; linarith)]
        <;> linarith
      linarith [h16, h13]
    have h17 : 1 - (3 - x) > 0 := by
      apply div_pos_iff.mp at h15
      cases h15 with
      | inl h18 =>
        linarith
      | inr h19 =>
        linarith
    have h18 : x > 2 := by linarith
    linarith
  · -- Case where 3 - x ≤ 0, so x ≥ 3
    push_neg at h6
    have h7 : 3 - x < 0 := by
      by_contra h8
      push_neg at h8
      have h9 : 3 - x = 0 := by linarith
      have h10 : x = 3 := by linarith
      contradiction
    have h8 : 1 / (3 - x) < 0 := by
      apply div_neg_of_pos_of_neg
      · -- 1 > 0
        linarith
      · -- 3 - x < 0
        linarith
    linarith