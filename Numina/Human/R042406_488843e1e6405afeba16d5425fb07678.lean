import Mathlib

/- What is the greatest integer less than 100 for which the greatest common factor of that integer and 18 is 3? -/
theorem algebra_14241 :
    IsGreatest {x | x < 100 ∧ Nat.gcd x 18 = 3} 93 := by
  refine' ⟨by decide, _⟩
  rintro y ⟨h₁, h₂⟩
  norm_num at h₁ h₂
  revert y
  decide