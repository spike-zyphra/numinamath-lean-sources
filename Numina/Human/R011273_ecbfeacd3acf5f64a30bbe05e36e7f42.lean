import Mathlib
open Real
/- Prove that for every $x \geq 1$,
\[1 - \frac{1}{x} < \ln x < x - 1\] -/
theorem inequalities_614004 (x : ℝ) (hx : 1 < x) : 1 - 1 / x < log x ∧ log x < x - 1:= by
  -- First, we prove a helper lemma that log(x) < x - 1 for any positive x ≠ 1
  have h1 : ∀ x : ℝ, x > 0 → x ≠ 1 → log x < x - 1:= by
    intro x hx hx1
    -- We'll prove this by using the fact that exp is strictly increasing
    suffices rexp (log x) < rexp (x - 1) by exact log_lt_sub_one_of_pos hx hx1
    -- Since exp(log(x)) = x for positive x
    rw [show rexp (log x) = x by exact Real.exp_log hx]
    -- Ensure that x - 1 ≠ 0
    replace hx1 : x - 1 ≠ 0:= by exact sub_ne_zero_of_ne hx1
    -- Use the fact that exp(y) > 1 + y for y ≠ 0
    have h1:= Real.add_one_lt_exp hx1
    linarith

  -- Now we prove both parts of the inequality
  constructor
  -- First part: 1 - 1/x < log(x)
  .
    -- Rearranging to -log(x) < 1/x - 1
    suffices -log x < 1 / x - 1 by linarith
    -- Using the property that -log(x) = log(1/x)
    rw [show -log x = log (1 / x) by rw [Real.log_div (by linarith) (by linarith)] ; simp]
    -- Proving that 1/x ≠ 1
    have hx1 : 1 / x ≠ 1:= by
      by_contra H
      field_simp at H
      linarith
    -- Apply our helper lemma to 1/x
    exact h1 (1 / x) (by positivity) hx1
  -- Second part: log(x) < x - 1
  .
    -- Apply our helper lemma directly to x
    exact h1 x (by positivity) (by linarith)
