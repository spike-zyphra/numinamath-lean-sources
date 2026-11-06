import Mathlib
theorem algebra_427 {f : ℝ → ℝ} (hf : ∀ x, x > 0 → f x = x) (hf' : ∀ x, x ≤ 0 → f x = 0)
  (x : ℝ)  : (f (x - 10)) + abs (f x + 5) - 1999 = 2012 ↔ x = 2008 := by
  constructor
  · -- If the equation holds, then x = 2008
    intro h
    by_cases h1 : x > 10
    · -- x > 10
      have h2 : f (x - 10) = x - 10 := by
        apply hf (x - 10) (by linarith)
      have h3 : f x = x := by
        apply hf x (by linarith)
      have h4 : abs (f x + 5) = x + 5 := by
        have h6 : f x + 5 = x + 5 := by
          rw [h3]
          <;> linarith
        rw [h6]
        have h5 : x + 5 > 0 := by linarith
        rw [abs_of_pos h5]
      have h_eq : f (x - 10) + abs (f x + 5) = 4011 := by
        linarith
      rw [h2, h4] at h_eq
      linarith
    by_cases h2 : x > 0
    · -- 0 < x ≤ 10
      have h1_ : x ≤ 10 := by
        by_contra h'
        push_neg at h'
        linarith [show x > 10 from by linarith]
      -- This defines f (x - 10) correctly for this case.
      have h2' : f (x - 10) = 0 := by
        have h5 : x - 10 ≤ (0 : ℝ) := by
          nlinarith
        specialize hf' (x - 10) h5
        linarith [hf']
      have h3' : f x = x := by
        apply hf x (by linarith)
      have h4' : abs (f x + (5 : ℝ)) = x + 5 := by
        have h5 : f x + (5 : ℝ) = x + 5 := by
          rw [h3']
          <;> linarith
        rw [h5]
        have h6 : x + 5 > (0 : ℝ) := by
          nlinarith
        rw [abs_of_pos h6]
      have h_eq : f (x - 10) + abs (f x + 5) = 4011 := by
        linarith
      have eq1 : x = 4006 := by
        rw [show f (x - 10) = (0 : ℝ) by linarith [h2']] at h_eq
        nlinarith [abs_nonneg (f x + (5 : ℝ))]
      nlinarith [sq_nonneg (x - 2008), sq_nonneg (x - 10)]
    · -- x ≤ 0
      have h1_ : x ≤ 0 := by
        by_contra h'
        push_neg at h'
        have : x > 0 := by linarith
        linarith [h2, this]
      have h3' : f (x - 10) = 0 := by
        have h5 : x - 10 ≤ (0 : ℝ) := by
          nlinarith
        specialize hf' (x - 10) h5
        linarith [hf']
      have h4' : f x = 0 := by
        have h5 : x ≤ (0 : ℝ) := by
          linarith [h1_]
        specialize hf' x h5
        linarith [hf']
      have h5' : abs (f x + (5 : ℝ)) = (5 : ℝ) := by
        have h6 : f x + (5 : ℝ) = (5 : ℝ) := by
          rw [h4']
          <;> linarith
        rw [h6]
        all_goals norm_num [abs_of_pos]
      have h_eq : f (x - 10) + abs (f x + 5) = 4011 := by
        linarith
      rw [h3', h5'] at h_eq
      all_goals nlinarith
  · -- If x = 2008 then the equation holds
    intro h_eq
    rw [h_eq]
    norm_num [hf, hf', abs_of_pos]