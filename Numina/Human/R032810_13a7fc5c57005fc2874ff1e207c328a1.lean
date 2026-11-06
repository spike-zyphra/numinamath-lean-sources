import Mathlib

/- Write down the positive integer that is smaller than $\sqrt{2}$ ____. -/
theorem algebra_9166 : {x : ℤ | x > 0 ∧ x < √2} = {1} := by
  -- Note on formalization of the problem:
  -- We prove the only positive integer smaller than √2 is 1.

  ext x
  simp
  -- We have two goals to prove:
  -- 1. 1 is a positive integer smaller than √2
  -- 2. If x is a positive integer smaller than √2, then x = 1
  constructor <;> intro h
  . -- Goal 2
    obtain ⟨h1, h2⟩ := h
    -- x < (2 : ℝ) because x < √2 < 2
    replace h2 : x < (2 : ℝ) := by
      suffices _ : √2 < 2 by linarith
      rw [Real.sqrt_lt] <;> norm_num
    -- Cast back to ℤ
    replace h2 : x < 2 := by
      suffices t : (x : ℝ) < (2 : ℤ) by rwa [Int.cast_lt] at t
      simpa
    -- Linear integer arithmetic
    omega
  . -- Goal 1
    -- Substitute x with 1
    subst x
    simp
    rw [Real.lt_sqrt] <;> norm_num
