import Mathlib

/- If $a \clubsuit b = a^2 + 2ab + b^2$ and $2 \clubsuit x = 81$, find the sum of all possible values of $x$. -/
theorem algebra_19536 (f : ℝ → ℝ → ℝ) (fdef : ∀ a b, f a b = a ^ 2 + 2 * a * b + b ^ 2) :
    ∑ᶠ x ∈ {x : ℝ | f 2 x = 81}, x = -4 := by
  -- We find all the values of x that satisfy the condition
  suffices H : {x : ℝ | f 2 x = 81} = {-11, 7} by
    rw [H, finsum_mem_eq_toFinset_sum]
    simp [show (-11 : ℝ) ≠ 7 by norm_num]
    norm_num
  -- We prove the equivalence by double inclusion
  ext x
  -- Expand the definition of f
  simp [fdef]
  clear f fdef
  -- We prove the two implications
  constructor
  . -- Solve the quadratic equation
    intro h
    replace h : (x + 2) ^ 2 = 9 ^ 2 := by linear_combination h
    rw [sq_eq_sq_iff_eq_or_eq_neg] at h
    -- Case analysis
    rcases h with h | h
    . right
      linarith only [h]
    . left
      linarith only [h]
  . -- Check the two solutions
    rintro (rfl | rfl)
    all_goals
      norm_num
