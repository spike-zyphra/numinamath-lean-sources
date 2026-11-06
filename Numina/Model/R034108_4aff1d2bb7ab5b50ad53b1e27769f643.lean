import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_263092 (x : ℝ) (hx : x ≥ 0) :
    (sqrt x + 2^x) / (sqrt x + 2^(x + 1)) + (sqrt x + 3^x) / (sqrt x + 3^(x + 1)) +
    (sqrt x + 6^x) / (sqrt x + 6^(x + 1)) = 1 ↔ x = 0 := by
  constructor
  · -- Assume the equation holds, prove x = 0
    intro h_eq
    by_cases h : x > 0
    · -- Assume x > 0, derive a contradiction
      have h1 : sqrt x > 0 := by
        apply Real.sqrt_pos.2
        linarith
      have eq1 : (sqrt x + (2 : ℝ) ^ x) / (sqrt x + (2 : ℝ) ^ (x + 1)) > 1 / 2 := by
        have h2 : (2 : ℝ) ^ (x + 1) = 2 * (2 : ℝ) ^ x := by
          rw [Real.rpow_add]
          ring_nf
          all_goals linarith
        rw [h2]
        apply (lt_div_iff' (by positivity)).mpr
        nlinarith [Real.rpow_pos_of_pos (show 0 < (2 : ℝ) by norm_num) x]
      have eq2 : (sqrt x + (3 : ℝ) ^ x) / (sqrt x + (3 : ℝ) ^ (x + 1)) > 1 / 3 := by
        have h3 : (3 : ℝ) ^ (x + 1) = 3 * (3 : ℝ) ^ x := by
          rw [Real.rpow_add]
          ring_nf
          all_goals linarith
        rw [h3]
        apply (lt_div_iff' (by positivity)).mpr
        nlinarith [Real.rpow_pos_of_pos (show 0 < (3 : ℝ) by norm_num) x]
      have eq3 : (sqrt x + (6 : ℝ) ^ x) / (sqrt x + (6 : ℝ) ^ (x + 1)) > 1 / 6 := by
        have h4 : (6 : ℝ) ^ (x + 1) = 6 * (6 : ℝ) ^ x := by
          rw [Real.rpow_add]
          ring_nf
          all_goals linarith
        rw [h4]
        apply (lt_div_iff' (by positivity)).mpr
        nlinarith [Real.rpow_pos_of_pos (show 0 < (6 : ℝ) by norm_num) x]
      have h2 : (sqrt x + (2 : ℝ) ^ x) / (sqrt x + (2 : ℝ) ^ (x + 1)) + (sqrt x + (3 : ℝ) ^ x) / (sqrt x + (3 : ℝ) ^ (x + 1)) + (sqrt x + (6 : ℝ) ^ x) / (sqrt x + (6 : ℝ) ^ (x + 1)) > 1 := by
        linarith [eq1, eq2, eq3]
      linarith [h_eq, h2]
    · -- Assume x ≤ 0, then x = 0
      have h3 : x = 0 := by linarith
      assumption
  · -- Assume x = 0, prove the equation
    intro h_eq
    rw [h_eq]
    norm_num