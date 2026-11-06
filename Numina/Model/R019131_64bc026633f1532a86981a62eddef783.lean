import Mathlib

theorem algebra_253653 (x : ℝ) (hx : x > 5) :
    (5 / (x + 1)) < (5 / x) ∧ (5 / (x + 1)) < (5 / (x - 1)) ∧
    (5 / (x + 1)) < (x / 5) ∧ (5 / (x + 1)) < ((x + 1) / 5) := by

  have h1 : 0 < x := by linarith
  have h2 : 0 < x + 1 := by linarith
  have h3 : 0 < x - 1 := by linarith

  constructor
  · -- Prove 5 / (x + 1) < 5 / x
    have h4 : 5 / (x + 1) < 5 / x := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h4
  constructor
  · -- Prove 5 / (x + 1) < 5 / (x - 1)
    have h5 : 5 / (x + 1) < 5 / (x - 1) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h5
  constructor
  · -- Prove 5 / (x + 1) < x / 5
    have h6 : 5 / (x + 1) < x / 5 := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith [sq_pos_of_pos (show 0 < x - 5 by linarith)]
    exact h6
  · -- Prove 5 / (x + 1) < (x + 1) / 5
    have h7 : 5 / (x + 1) < (x + 1) / 5 := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith [sq_pos_of_pos (show 0 < x - 5 by linarith)]
    exact h7