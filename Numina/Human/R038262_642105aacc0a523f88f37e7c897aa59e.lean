import Mathlib

/-What is the greatest integer less than 100 for which the greatest common divisor of that integer and 12 is 4?

The final answer is $ \boxed{92} $-/
theorem algebra_16640 : IsGreatest {n | n < 100 ∧ Nat.gcd n 12 = 4} 92 := by
  constructor
  · -- Verify that 92 satisfy the condition.
    simp
  · -- any number which greater than 92 and less than 100 can not meet the condition.
    -- Therefore, the answer is 92.
    intro a ⟨alt,ha⟩
    by_contra! agt
    interval_cases a <;> simp at ha
