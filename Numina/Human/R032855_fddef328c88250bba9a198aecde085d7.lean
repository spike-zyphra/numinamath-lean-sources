import Mathlib
open Real

/- The maximum value of the function $f(x)= \frac {x}{e^{x}}$ (where $e$ is the base of the natural logarithm) is $\_\_\_\_\_\_$. -/
theorem algebra_9107 {f : ℝ → ℝ} (hf : f = fun x => x / exp x) :
    IsGreatest (Set.range f) (1 / exp 1) := by
  -- We have two goals:
  -- 1. Show that 1 / exp 1 can be achieved
  -- 2. Show that 1 / exp 1 is an upper bound
  simp [IsGreatest, upperBounds, hf]
  constructor
  . -- f(1) = 1 / exp 1
    use 1
    simp
  . intro x
    -- 1 + (x-1) ≤ exp (x-1)
    have h := add_one_le_exp (x - 1)
    simp at h
    rw [exp_sub] at h
    -- x / exp x ≤ (exp x / exp 1) / exp x = 1 / exp 1
    calc x / exp x ≤ (exp x / exp 1) / exp x := by rwa [div_le_div_right (exp_pos x)]
                 _ = 1 / exp 1 := by field_simp; ring
                 _ = (exp 1)⁻¹ := by simp
