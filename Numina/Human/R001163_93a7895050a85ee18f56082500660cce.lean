import Mathlib

/- The second and ninth terms of an arithmetic sequence are 2 and 30, respectively. What is the fiftieth term? -/
theorem algebra_20797 {a d : ℤ} (h₀ : a + d = 2) (h₁ : a + 8 * d = 30) :
    a + 49 * d = 194 := by 
  have h₂ : a = 2 - d := by linarith
  subst h₂
  linarith