import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_22072 {f k : ℝ → ℝ}
  (hf : ∀ x, x > 2 → f x = k x)
  (hf' : ∀ x, x ≤ 2 → f x = 2 + (x - 2)^2)
  (hk : ∀ x, f (f x) = x) :
  ∀ x > 2, k x = -sqrt (x - 2) + 2 := by
  intro x hx
  -- Apply f to y = 2 - sqrt(x - 2)
  have h1 := hk (2 - Real.sqrt (x - 2))
  -- Verify that y <= 2 so that we can use the second case of f
  have h2 : (2 - Real.sqrt (x - 2)) ≤ (2 : ℝ) := by
    have : Real.sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
    linarith
  -- Show that f(2 - sqrt(x-2)) = x
  have h3 : f (2 - Real.sqrt (x - 2)) = x := by
    rw [hf' (2 - Real.sqrt (x - 2)) h2]
    have h4 : ( (2 - Real.sqrt (x - 2) ) - 2 ) ^ 2 = (Real.sqrt (x - 2)) ^ 2 := by
      ring_nf
    have h5 : (Real.sqrt (x - 2)) ^ 2 = x - 2 := by
      apply Real.sq_sqrt
      linarith
    nlinarith
  -- Now apply f again to get f(f(y)) = y
  have h6 : f (f (2 - Real.sqrt (x - 2))) = (2 - Real.sqrt (x - 2) : ℝ) := by
    simpa using h1
  -- Substitute f(y) = x to get f(x) = y
  have h7 : f x = 2 - Real.sqrt (x - 2) := by
    rw [h3] at h6
    linarith
  -- Since x > 2, f(x) = k(x)
  have h8 : f x = k x := by
    apply hf x
    exact hx
  -- Thus k(x) = y = 2 - sqrt(x - 2)
  -- Rewrite what we just obtained to match the expected result.
  have h9 : k x = 2 - Real.sqrt (x - 2) := by
    linarith [h7, h8]
  have h10 : k x = - Real.sqrt (x - 2) + 2 := by
    linarith [h9]
  rw [h10]