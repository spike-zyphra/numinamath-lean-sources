import Mathlib

/- Let $a, b, c > 0$. Prove that:
$ \frac{ab}{a+3b+2c} + \frac{bc}{b+3c+2a} + \frac{ca}{c+3a+2b} \le \frac{a+b+c}{6} $ -/
theorem inequalities_620629 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a * b / (a + 3 * b + 2 * c) + b * c / (b + 3 * c + 2 * a) +
  c * a / (c + 3 * a + 2 * b) ≤ (a + b + c) / 6 := by
  -- Restating the inequality to be proven
  have h : a * b / (a + 3 * b + 2 * c) + b * c / (b + 3 * c + 2 * a) + c * a / (c + 3 * a + 2 * b) ≤ (a + b + c) / 6 := by
    -- Rearranging the inequality to show that the difference is non-positive
    have h4 : (a * b) / (a + 3 * b + 2 * c) + (b * c) / (b + 3 * c + 2 * a) + (c * a) / (c + 3 * a + 2 * b) - (a + b + c) / 6 ≤ 0 := by
      -- Proving that the product of denominators is positive
      have h5 : (a + 3 * b + 2 * c) * (b + 3 * c + 2 * a) * (c + 3 * a + 2 * b) > 0 := by
        apply mul_pos
        apply mul_pos
        all_goals nlinarith
      -- Key inequality: comparing the numerators after finding a common denominator
      have h6 : 6 * (a * b * (b + 3 * c + 2 * a) * (c + 3 * a + 2 * b) + b * c * (c + 3 * a + 2 * b) * (a + 3 * b + 2 * c) + c * a * (a + 3 * b + 2 * c) * (b + 3 * c + 2 * a))
        ≤ (a + b + c) * (a + 3 * b + 2 * c) * (b + 3 * c + 2 * a) * (c + 3 * a + 2 * b) := by
        -- Using square non-negativity of various expressions to prove the inequality
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 2 * b + c), sq_nonneg (b - 2 * c + a),
          sq_nonneg (c - 2 * a + b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      -- Proving that the difference is non-positive
      have h7 : (a * b) / (a + 3 * b + 2 * c) + (b * c) / (b + 3 * c + 2 * a) + (c * a) / (c + 3 * a + 2 * b) - (a + b + c) / 6 ≤ 0 := by
        -- Rewriting the difference as a single fraction
        have h8 : (a * b) / (a + 3 * b + 2 * c) + (b * c) / (b + 3 * c + 2 * a) + (c * a) / (c + 3 * a + 2 * b) - (a + b + c) / 6 =
          (6 * (a * b * (b + 3 * c + 2 * a) * (c + 3 * a + 2 * b) + b * c * (c + 3 * a + 2 * b) * (a + 3 * b + 2 * c) + c * a * (a + 3 * b + 2 * c) * (b + 3 * c + 2 * a))
            - (a + b + c) * (a + 3 * b + 2 * c) * (b + 3 * c + 2 * a) * (c + 3 * a + 2 * b)) / (6 * ((a + 3 * b + 2 * c) * (b + 3 * c + 2 * a) * (c + 3 * a + 2 * b))) := by
          field_simp
          ring
        -- Using the rewritten form and previous results to complete the proof
        rw [h8]
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith
        · nlinarith
      linarith
    linarith
  linarith
