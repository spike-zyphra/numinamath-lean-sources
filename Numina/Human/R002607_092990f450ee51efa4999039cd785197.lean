import Mathlib

/- The ratio of Mary's age to Alice's age is 3:5. Alice is 30 years old. How old is Mary?
(A) 15(B) 18(C) 20(D) 24(E) 50 -/
theorem algebra_96249 (m a : ℕ) (h₀ : m * 5 = a * 3) (h₁ : a = 30) : m = 18 := by
    --substitute the age of Alice in the proportion
    rw[h₁] at h₀
    --solve for m to finde Mary's age
    linarith