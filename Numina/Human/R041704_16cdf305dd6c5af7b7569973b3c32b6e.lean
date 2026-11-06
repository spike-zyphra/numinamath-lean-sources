import Mathlib
open Real Set

/- The maximum value of the function $f(x)=\frac{lnx}{x}$ is ______. -/
theorem algebra_8985 {f : ℝ → ℝ} (hf : f = λ x => log x / x) :
    IsGreatest (image f (Ioi 0)) (1 / exp 1) := by
  -- We have two goals:
  -- 1. Show that 1 / exp 1 can be achieved
  -- 2. Show that 1 / exp 1 is an upper bound
  simp [IsGreatest, upperBounds, hf]
  constructor
  . -- Set x = exp 1
    use exp 1
    constructor
    . positivity
    . simp
  . intro x hx
    -- log x = log (x / e) + 1 ≤ x / e -- using log_le_sub_one_of_pos
    have h : log (x / exp 1) ≤ x / exp 1 - 1 := log_le_sub_one_of_pos (by positivity)
    rw [log_div (by positivity) (by positivity)] at h
    simp at h
    exact (div_le_iff₀' hx).2 h
