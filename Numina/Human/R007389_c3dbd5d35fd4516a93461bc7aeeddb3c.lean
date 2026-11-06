import Mathlib

/- The sum of the squares of three consecutive positive integers is 7805. What is the sum of the cubes of the three original integers? -/
theorem algebra_10332 (n : ℕ) (h₀ : n > 0) (h₁ : n^2 + (n+1)^2 + (n+2)^2 = 7805) :
    n^3 + (n+1)^3 + (n+2)^3 = 398259 := by
  ring_nf at h₁ ⊢
  nlinarith