import Mathlib

theorem algebra_21759 {f : ℝ → ℝ} (hf : f = fun x => abs (3 * x - 1)) :
    {x | f (f x) = x} = {1/5, 1/4, 2/5, 1/2}:= by
  ext x 
  simp [hf]
  constructor
  · -- Assume f(f(x)) = x, prove x ∈ {1/5, 1/4, 2/5, 1/2}
    intro h
    have h1 : abs (3 * abs (3 * x - 1) - 1) = x := by
      simpa using h
    by_cases h3 : 3 * abs (3 * x - 1) - 1 ≥ 0
    · -- Case 1: 3 * abs (3 * x - 1) - 1 ≥ 0
      have eq1 : abs (3 * abs (3 * x - 1) - 1) = 3 * abs (3 * x - 1) - 1 := by 
        rw [abs_of_nonneg h3]
      rw [eq1] at h1
      by_cases h4 : 3 * x - 1 ≥ 0
      · -- Case 1.1: 3 * x - 1 ≥ 0
        have eq2 : abs (3 * x - 1) = 3 * x - 1 := by 
          rw [abs_of_nonneg h4]
        rw [eq2] at h1
        have hx : x = (1 : ℝ) / 2 := by linarith
        simp [hx]
      · -- Case 1.2: 3 * x - 1 < 0
        have eq2 : abs (3 * x - 1) = -(3 * x - 1) := by 
          rw [abs_of_neg (by linarith)]
        rw [eq2] at h1
        have hx : x = (1 : ℝ) / 5 := by linarith
        simp [hx]
    · -- Case 2: 3 * abs (3 * x - 1) - 1 < 0
      have eq1 : abs (3 * abs (3 * x - 1) - 1) = -(3 * abs (3 * x - 1) - 1) := by 
        rw [abs_of_neg (by linarith)]
      rw [eq1] at h1
      by_cases h4 : 3 * x - 1 ≥ 0
      · -- Case 2.1: 3 * x - 1 ≥ 0
        have eq2 : abs (3 * x - 1) = 3 * x - 1 := by 
          rw [abs_of_nonneg h4]
        rw [eq2] at h1
        have hx : x = (2 : ℝ) / 5 := by linarith
        simp [hx]
      · -- Case 2.2: 3 * x - 1 < 0
        have eq2 : abs (3 * x - 1) = -(3 * x - 1) := by 
          rw [abs_of_neg (by linarith)]
        rw [eq2] at h1
        have hx : x = (1 : ℝ) / 4 := by linarith
        simp [hx]
  · -- Show that if x = 1/5, 1/4, 2/5, or 1/2, then it is a solution.
    rintro (h | h | h | h)
    · -- x = 1/5
      rw [show x = (1 : ℝ) / 5 by linarith [h]]
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- x = 1/4
      rw [show x = (1 : ℝ) / 4 by linarith [h]]
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- x = 2/5
      rw [show x = (2 : ℝ) / 5 by linarith [h]]
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- x = 1/2
      rw [show x = (1 : ℝ) / 2 by linarith [h]]
      norm_num [abs_of_nonneg, abs_of_nonpos]