import Mathlib

/- For arbitrary pairwise distinct positive real numbers $a, b, c$, prove the inequality
$$\frac{(a^2- b^2)^3 + (b^2-c^2)^3+(c^2-a^2)^3}{(a- b)^3 + (b-c)^3+(c-a)^3}> 8abc$$ -/
theorem inequalities_25678 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hdist : a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    ((a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3) /
    ((a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3) > 8 * a * b * c := by
  -- Simplify the numerator using algebraic manipulation
  -- The sum of cubes can be factored into a product
  have hnum : (a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3 =
    3 * ((a ^ 2 - b ^ 2) * (b ^ 2 - c ^ 2) * (c ^ 2 - a ^ 2)) := by
    ring_nf
  -- Simplify the denominator using similar algebraic manipulation
  have hdenom : (a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3 = 3 * ((a - b) * (b - c) * (c - a)) := by
    ring_nf
  -- Simplify the entire fraction by substituting the numerator and denominator
  -- and showing it equals (a+b)*(b+c)*(c+a)
  have h4 : ((a ^ 2 - b ^ 2) ^ 3 + (b ^ 2 - c ^ 2) ^ 3 + (c ^ 2 - a ^ 2) ^ 3) /
    ((a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3) = ((a + b) * (b + c) * (c + a)) := by
    rw [hnum, hdenom]
    -- Further simplify the fraction after substitution
    have h6 : (3 * ((a ^ 2 - b ^ 2) * (b ^ 2 - c ^ 2) * (c ^ 2 - a ^ 2))) /
      (3 * ((a - b) * (b - c) * (c - a))) =
      ((a + b) * (b + c) * (c + a)) := by
      -- Prove that the denominator is non-zero to allow division
      have h7 : (a - b) * (b - c) * (c - a) ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        · exact sub_ne_zero_of_ne hdist.1
        · exact sub_ne_zero_of_ne hdist.2.1
        · exact sub_ne_zero_of_ne (by
            intro h
            apply hdist.2.2
            linarith)
      -- Prove that the scaled denominator is also non-zero
      have h9 : 3 * ((a - b) * (b - c) * (c - a)) ≠ 0 := by
        intro h
        have h10 : (a - b) * (b - c) * (c - a) = 0 := by
          nlinarith
        contradiction
      -- Simplify the fraction using field operations
      field_simp [h9]
      linarith
    linarith [h6]
  -- Rewrite the inequality using the simplified form
  rw [h4]
  -- Prove that the simplified expression is greater than 8abc
  -- by showing their difference is positive
  have h5 : (a + b) * (b + c) * (c + a) - 8 * a * b * c > 0 := by
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by linarith), sq_pos_of_ne_zero (show b ≠ 0 by linarith),
      sq_pos_of_ne_zero (show c ≠ 0 by linarith),
      sq_pos_of_ne_zero (show a - b ≠ 0 by exact sub_ne_zero_of_ne hdist.1),
      sq_pos_of_ne_zero (show b - c ≠ 0 by exact sub_ne_zero_of_ne hdist.2.1),
      sq_pos_of_ne_zero (show a - c ≠ 0 by exact sub_ne_zero_of_ne hdist.2.2),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  -- Complete the proof using non-linear arithmetic
  nlinarith
