import Mathlib

/- 156. Prove that $\sqrt{2}$ cannot be a rational number. -/
theorem number_theory_276246 : ¬ ∃ (x : ℚ), Real.sqrt 2 = x := by

  --We prove this by way of contradiction.
  --Assume ∃ (x : ℚ), Real.sqrt 2 = x
  by_contra h
  --Obtain x and hx
  rcases h with ⟨x, hx⟩
  --Since sqrt(2) is irrational, obtain...
  have h₁ : Irrational (Real.sqrt 2) := by
    exact irrational_sqrt_two
  --Since x is rational, x is not irrational.
  have h₂ : ¬ Irrational (x) := by
    exact Rat.not_irrational x
  --Re-writing...
  rw [←hx] at h₂
  --h₁ and h₂ give the contradiction.
  contradiction