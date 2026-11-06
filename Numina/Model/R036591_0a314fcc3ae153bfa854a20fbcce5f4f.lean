import Mathlib

open Real

theorem inequalities_197809 (a : ℝ) :
    (∀ x : ℝ, x ^ 2 - 2 ^ (a + 2) * x - 2 ^ (a + 3) + 12 > 0) ↔ a < 0 := by
  constructor
  · -- Assume $\forall x, x^2 - 2^{a+2} \cdot x - 2^{a+3} + 12 > 0$ then $a < 0$.
    intro h
    by_contra ha
    push_neg at ha
    -- If $a \geq 0$, then $2^a \geq 1$.
    have ha1 : (2 : ℝ) ^ a ≥ 1 := by
      have h1 : (2 : ℝ) ^ a ≥ (2 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals
          linarith
      have h2 : (2 : ℝ) ^ (0 : ℝ) = 1 := by
        norm_num
      linarith
    -- Take $x = 2^{a+1}$.
    have h1 := h ( (2 : ℝ) ^ (a + 1 : ℝ) )
    -- Simplify expressions.
    have ha2 : (2 : ℝ) ^ (a + 2 : ℝ) = (2 : ℝ) ^ a * (2 ^ (2 : ℝ)) := by
      rw [← Real.rpow_add]
      ring_nf
      all_goals
        linarith
    have ha3 : (2 : ℝ) ^ (a + 3 : ℝ) = (2 : ℝ) ^ a * (2 ^ (3 : ℝ)) := by
      rw [← Real.rpow_add]
      ring_nf
      all_goals
        linarith
    have ha4 : (2 : ℝ) ^ (a + 1 : ℝ) = (2 : ℝ) ^ a * (2 ^ (1 : ℝ)) := by
      rw [← Real.rpow_add]
      ring_nf
      all_goals
        linarith
    have h2n : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by norm_num
    have h4n : (2 : ℝ) ^ (3 : ℝ) = (8 : ℝ) := by norm_num
    have h1n : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by norm_num
    rw [ha4, ha2, ha3, h2n, h4n, h1n] at h1
    -- Compute the value at $x = 2^{a+1}$.
    have ha6 : ((2 : ℝ) ^ a * (2 : ℝ)) ^ 2 - ((2 : ℝ) ^ a * (4 : ℝ)) * ((2 : ℝ) ^ a * (2 : ℝ)) - ((2 : ℝ) ^ a * (8 : ℝ)) + 12 ≤ 0 := by
      nlinarith [Real.rpow_nonneg (show 0 ≤ (2 : ℝ) by linarith) a, sq_nonneg ((2 : ℝ) ^ a - 1)]
    linarith
  · -- Assume $a < 0$, show $\forall x, x^2 - 2^{a+2} \cdot x - 2^{a+3} + 12 > 0$.
    intro ha x
    have ha1 : (2 : ℝ) ^ a < (1 : ℝ) := by
      have h10 : (2 : ℝ) ^ a < (2 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals
          linarith
      have h02 : (2 : ℝ) ^ (0 : ℝ) = 1 := by norm_num
      linarith
    have ha2 : (2 : ℝ) ^ a > 0 := by
      positivity
    -- Simplify expressions.
    have ha3 : (2 : ℝ) ^ (a + 2 : ℝ) = (2 : ℝ) ^ a * (2 ^ (2 : ℝ)) := by
      rw [← Real.rpow_add]
      ring_nf
      all_goals
        linarith
    have ha4 : (2 : ℝ) ^ (a + 3 : ℝ) = (2 : ℝ) ^ a * (2 ^ (3 : ℝ)) := by
      rw [← Real.rpow_add]
      ring_nf
      all_goals
        linarith
    have h2n : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by norm_num
    have h4n : (2 : ℝ) ^ (3 : ℝ) = (8 : ℝ) := by norm_num
    rw [ha3, ha4, h2n, h4n]
    -- Show the quadratic is positive.
    have ha6 : ((2 : ℝ) ^ a) ^ 2 < (1 : ℝ) := by
      nlinarith [Real.rpow_nonneg (show 0 ≤ (2 : ℝ) by norm_num) a]
    nlinarith [sq_nonneg (x - ((2 : ℝ) ^ a * (4 : ℝ)) / 2), Real.rpow_nonneg (show 0 ≤ (2 : ℝ) by norm_num) a, sq_nonneg ((2 : ℝ) ^ a - 1), mul_pos (show 0 < (2 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num)]