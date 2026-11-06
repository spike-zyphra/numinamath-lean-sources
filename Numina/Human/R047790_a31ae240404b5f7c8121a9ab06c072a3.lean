import Mathlib
open Real

/- Solve the equation $\lg x + \lg (x - 2) = \lg 3 + \lg (x + 2)$. -/
theorem algebra_9284 {x : ℝ} (hx : x > 2) :
    logb 10 x + logb 10 (x - 2) = logb 10 3 + logb 10 (x + 2) ↔ x = 6 := by

  -- Use the lemma lg a + lg b = lg (a * b) to rewrite the equation:
  -- lg (x * (x - 2)) = lg (3 * (x + 2))
  rw [← logb_mul (by linarith) (by linarith), ← logb_mul (by norm_num) (by linarith)]

  -- Solve the equation lg (x * (x - 2)) = lg (3 * (x + 2))
  constructor <;> intro h
  . -- Log is injective, so x * (x - 2) = 3 * (x + 2)
    apply Real.logb_injOn_pos at h
    . -- Simplify the equation to get x = 6
      nlinarith
    -- The following goals are produced because we need to prove 1 < 10, x * (x - 2) > 0 and 3 * (x + 2) > 0, which are trivial
    . norm_num
    . simp
      nlinarith
    . simp
      linarith
  . -- Plug in x = 6
    subst x
    norm_num
