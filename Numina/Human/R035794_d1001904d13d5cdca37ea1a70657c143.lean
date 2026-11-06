import Mathlib
open Real Set

/- The monotonic increasing interval of the function $y=\log_{0.2}(x^{2}-6x+8)$ is ______. -/
theorem algebra_9267 {f : ℝ → ℝ} (hf : f = λ x => logb 0.2 (x^2 - 6 * x + 8)) :
    MonotoneOn f (Iio 2) ∧ AntitoneOn f (Ioi 4) := by
  -- Note on formulation of the problem: the domain of the function is (-∞, 2) ∪ (4, ∞), and it is increasing on (-∞, 2) and decreasing on (4, ∞). Thus the monotonic increasing interval is (-∞, 2).
  rw [hf]
  -- Split the goals and prove them simultaneously
  constructor
  all_goals
    -- Use the definition of monotone and antitone functions and simplify
    intro x hx y hy hxy
    simp at *
    -- Prove the expression inside the log is positive
    have hx1 : x ^ 2 - 6 * x + 8 > 0 := by nlinarith
    have hy1 : y ^ 2 - 6 * y + 8 > 0 := by nlinarith
    -- log0.2 is decreasing
    rw [Real.logb_le_logb_of_base_lt_one] <;> (try norm_num) <;> nlinarith
