import Mathlib
open Real Set

/- The maximum value of the function $$y=3 \sqrt {x-2}+4 \sqrt {6-x}$$ is \_\_\_\_\_\_. -/
theorem algebra_9346 (f : Icc (2 : ℝ) 6 → ℝ) (hf : f = λ ⟨x, _⟩ => 3 * sqrt (x - 2) + 4 * sqrt (6 - x)) :
    IsGreatest (range f) 10 := by

  -- Expand the definitions
  simp [IsGreatest, upperBounds, range, hf]
  clear f hf

  -- Now we need to prove that there exists some x_0 in [2, 6] such that f x_0 = 10 and that f x ≤ 10 for all x in [2, 6]
  constructor
  . -- Use x_0 = 86/25, and simplify the expression
    use 86/25
    constructor <;> norm_num
    simp [(by norm_num : (36 : ℝ) = 6^2), (by norm_num : (25 : ℝ) = 5^2), (by norm_num : (64 : ℝ) = 8^2)]
    norm_num
  . -- Simplify the goal
    intro a x h1 h2 ha
    rw [← ha]
    clear a ha

    -- Cauchy-Schwarz inequality
    have CS (a b x y : ℝ) : (a * x + b * y) ^ 2 ≤ (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
      have : 0 ≤ (a * y - b * x) ^ 2 := sq_nonneg _
      linarith

    -- Use C-S in the special case and simplify the expression
    specialize CS 3 4 (sqrt (x - 2)) (sqrt (6 - x))
    simp [(by linarith : x - 2 >= 0), (by linarith : 6 - x ≥ 0)] at CS
    exact le_of_max_le_left (abs_le_of_sq_le_sq (by linarith) (by simp))
