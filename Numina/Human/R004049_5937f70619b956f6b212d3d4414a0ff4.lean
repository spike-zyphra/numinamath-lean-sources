import Mathlib
open Real

/- Theorem: If a, b, c > 0 and a + b + c + 2 = abc,
 then the inequality 2 ≤ a/(b+1) + b/(c+1) + c/(a+1) holds-/
theorem inequalities_233539 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c + 2 = a * b * c) :
    2 ≤ a / (b + 1) + b / (c + 1) + c / (a + 1) := by
  -- First, we prove that pairwise products are positive, which will be useful later
  have h5 : 0 < a * b := by nlinarith
  have h6 : 0 < b * c := by nlinarith
  have h7 : 0 < c * a := by nlinarith
  -- Now, we aim to prove the main inequality
  have key_ineq : a / (b + 1) + b / (c + 1) + c / (a + 1) ≥ 2 := by
    -- We show that the difference of the left-hand side and 2 is ≥ 0
    have h8 : a / (b + 1) + b / (c + 1) + c / (a + 1) - 2 ≥ 0 := by
      -- Step: Convert the expression to a common denominator and simplify the numerator
      have h9 : (a / (b + 1) + b / (c + 1) + c / (a + 1) - 2) = 
        (a * (c + 1) * (a + 1) + b * (a + 1) * (b + 1) + c * (b + 1) * (c + 1)
        - 2 * (b + 1) * (c + 1) * (a + 1)) / ((b + 1) * (c + 1) * (a + 1)) := by
        field_simp  -- Clear denominators
        ring         -- Simplify the resulting expression
      -- Rewrite the original expression using the simplified version
      rw [h9]
      -- Prove the numerator is ≥ 0 using positivity and square non-negativity
      have h10 : (a * (c + 1) * (a + 1) + b * (a + 1) * (b + 1) + c * (b + 1) * (c + 1)
        - 2 * (b + 1) * (c + 1) * (a + 1)) ≥ 0 := by
        -- Use the assumption a + b + c + 2 = abc and positive terms like (a - 2)^2 ≥ 0
        nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
                  h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
                  sq_nonneg (a * b - 2), sq_nonneg (b * c - 2), sq_nonneg (c * a - 2)]
      -- Since the numerator is ≥ 0 and the denominator > 0, the fraction is ≥ 0
      apply div_nonneg
      · linarith     -- Non-negativity of the numerator
      · positivity   -- Positivity of the denominator
    -- Now the inequality is shown to hold
    linarith
  -- Finally, deduce the result from the above key inequality
  linarith [key_ineq]
