import Mathlib
/- If $x, y$, and $z$ are real numbers such that $2 x^{2}+y^{2}+z^{2}=2 x-4 y+2 x z-5$, find the maximum possible value of $x-y+z$. -/
theorem algebra_611170 : IsGreatest {a : ℝ | ∃ x y z : ℝ, 2 * x ^ 2 + y ^ 2 + z ^ 2 = 2 * x - 4 * y + 2 * x * z - 5 ∧ a = x - y + z} 4:= by
  constructor
  -- First part: Prove that 4 is in the set
  -- Using x=1, y=-2, z=1 as the solution
  .
    simp
    use 1, -2, 1
    norm_num
  -- Second part: Prove that 4 is an upper bound
  -- Transform the equation to sum of squares form
  .
    simp [upperBounds]
    intro a x y z h ha
    subst a
    -- Rewrite the equation as sum of perfect squares equal to 0
    replace h : (x - 1) ^ 2 + (y + 2) ^ 2 + (z - x) ^ 2 = 0:= by linarith
    -- Prove each square term is non-negative
    have h1 : (x - 1) ^ 2 ≥ 0:= by positivity
    have h2 : (y + 2) ^ 2 ≥ 0:= by positivity
    have h3 : (z - x) ^ 2 ≥ 0:= by positivity
    -- Since sum of non-negative terms is 0, each term must be 0
    replace h1 : (x - 1) ^ 2 = 0:= by linarith
    replace h2 : (y + 2) ^ 2 = 0:= by linarith
    replace h3 : (z - x) ^ 2 = 0:= by linarith
    -- Simplify the equations and complete the proof
    simp at h1 h2 h3
    linarith
