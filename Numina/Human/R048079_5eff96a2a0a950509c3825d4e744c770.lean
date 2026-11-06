import Mathlib
open Real

/- Given that $f(x)$ is an odd function defined on $\mathbb{R}$, and when $x > 0$, $f(x)=\log_{2}x$, determine the solution set for $f(x) > 0$. -/
theorem algebra_9094 {f : ℝ → ℝ} (hf : ∀ x, f (-x) = - f x)
  (hpos : ∀ x > 0, f x = logb 2 x) :
  {x | f x > 0} = {x | 1 < x} ∪ {x | -1 < x ∧ x < 0} := by
  ext x
  simp
  -- Three cases: x > 0, x = 0, x < 0
  obtain h | h | h := lt_trichotomy x 0

  . -- When x < 0, f x = - f (-x) = - logb 2 (-x)
    -- After simplification, we have - logb 2 (-x) > 0 iff -x < 1
    rw [(by linarith [hf x] : f x = - f (-x)), hpos (-x) (by linarith), neg_pos, Real.logb_neg_iff (by norm_num) (by linarith)]
    -- Trivial case analysis
    constructor <;> intro h1
    . right
      constructor <;> linarith
    . obtain h1 | h1 := h1 <;> linarith

  . -- When x = 0, f x = 0 because f is an odd function
    have f0 : f 0 = 0 := by
      specialize hf 0
      simp at hf
      linarith
    rw [h, f0]
    norm_num

  . -- When x > 0, f x = logb 2 x
    -- After simplification, we have logb 2 x > 0 iff 1 < x
    rw [hpos x h, Real.logb_pos_iff (by norm_num) h]
    -- Trivial case analysis
    constructor <;> intro h1
    . left
      linarith
    . obtain h1 | h1 := h1 <;> linarith
