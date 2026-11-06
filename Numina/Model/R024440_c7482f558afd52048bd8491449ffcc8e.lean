import Mathlib

theorem algebra_314194 (f : ℝ → ℝ) (hf : Monotone f)
    (hff : ∀ x, f (f (f x)) = x) : f 2009 = 2009 := by
  have h1 := hff 2009
  by_cases h2 : f (2009) < 2009
  · -- Assume $f(2009) < 2009$.
    have h6 : f (f 2009) ≤ f 2009 := by
      have h4 : f 2009 ≤ (2009 : ℝ) := by linarith
      have h7 : f (f 2009) ≤ f (2009) := by
        apply hf
        linarith
      linarith
    -- Then $f(f(f(2009))) \leq f(f(2009)) \leq f(2009) < 2009$, a contradiction.
    have h7 : f (f (f 2009)) ≤ f (f 2009) := by
      have h4 : f (f 2009) ≤ f 2009 := by linarith
      apply hf
      linarith
    linarith [h1, h6, h7, h2]
  by_cases h3 : f (2009) > 2009
  · -- Assume $f(2009) > 2009$.
    have h6 : f (f 2009) ≥ f 2009 := by
      have h4 : f 2009 ≥ (2009 : ℝ) := by linarith
      have h7 : f (f 2009) ≥ f (2009) := by
        apply hf
        linarith
      linarith
    -- Then $f(f(f(2009))) \geq f(f(2009)) \geq f(2009) > 2009$, a contradiction.
    have h7 : f (f (f 2009)) ≥ f (f 2009) := by
      have h4 : f (f 2009) ≥ f 2009 := by linarith
      apply hf
      linarith
    linarith [h1, h6, h7, h3]
  linarith