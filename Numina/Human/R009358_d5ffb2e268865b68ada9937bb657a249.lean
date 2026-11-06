import Mathlib
open Real Set

/- Find the maximum value of the function $f(x) = x(6-2x)^2$ for $x \in [0, 3]$. -/
theorem algebra_8982 (f : ℝ → ℝ) (hf : f = λ x => x * (6 - 2 * x) ^ 2) :
  IsGreatest (image f (Icc 0 3)) 16 := by
  simp [image, IsGreatest, upperBounds, hf]
  constructor
  -- We need to prove 16 can be achieved
  -- and 16 is an upper bound
  . use 1
    norm_num
  . -- (x - 1)^2 ≥ 0 is enough to prove the inequality using nlinarith
    intro a x h1 h2 ha
    subst a
    nlinarith [sq_nonneg (x - 1)]
