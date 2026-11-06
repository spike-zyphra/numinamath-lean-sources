import Mathlib

/- What is the largest multiple of $9$ whose negation is greater than $-100$? -/
theorem algebra_13370 :
    IsGreatest {n | 9 ∣ n ∧ -n > -100} 99 := by
  refine' ⟨by decide, _⟩
  rintro n ⟨_, _⟩
  omega