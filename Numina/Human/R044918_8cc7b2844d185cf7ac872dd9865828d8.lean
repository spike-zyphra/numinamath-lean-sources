import Mathlib
/-Define an operation:∀ x, x > 0 → f x = x ;∀ x, x ≤ 0 → f x = 0.
if x satisfies f (x - 10)) + abs (f x + 5) - 1999 = 2012, then x =2008
-/
theorem algebra_427 {f : ℝ → ℝ} (hf : ∀ x, x > 0 → f x = x) (hf' : ∀ x, x ≤ 0 → f x = 0)
  (x : ℝ)  : (f (x - 10)) + abs (f x + 5) - 1999 = 2012 ↔ x = 2008 := by 
  constructor
  · -- First, we prove that if the equation holds, then x = 2008
    intro h
    by_cases h1 : x > 10
    · -- Case 1: x > 10
      have h2 : f (x - 10) = x - 10 := by
        apply hf
        linarith
      have h3 : f x = x := by 
        apply hf
        linarith
      rw [h2, h3] at h
      have h4 : abs (x + 5) = x + 5 := by
        rw [abs_of_pos]
        linarith
      rw [h4] at h
      have h5 : x = 2008 := by linarith
      exact h5
    · -- Case 2: x ≤ 10
      by_cases h2 : x > 0
      · -- Subcase 2a: 0 < x ≤ 10
        have h3 : f (x - 10) = 0 := by
          apply hf'
          linarith
        have h4 : f x = x := by
          apply hf
          linarith
        rw [h3, h4] at h
        have h5 : abs (x + 5) = x + 5 := by
          rw [abs_of_pos]
          linarith
        rw [h5] at h
        linarith
      · -- Case 2b: x ≤ 0
        have h3 : f (x - 10) = 0 := by
          apply hf'
          linarith
        have h4 : f x = 0 := by
          apply hf'
          linarith
        rw [h3, h4] at h
        norm_num at h
  · -- Second, we prove that if x = 2008, then the equation holds
    intro h
    rw [h]
    norm_num [hf, hf']