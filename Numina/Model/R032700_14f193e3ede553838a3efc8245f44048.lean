import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_311468 {f : ℝ → ℝ} (hf : f = λ x => logb (1/2) (x^2 - 2*x - 3)) :
    MonotoneOn f {x | x < -1} := by 
  intro x hx y hy hxy 
  have h1 : x < -1 := by
    simpa using hx
  have h2 : y < -1 := by 
    simpa using hy
  have h3 : x ≤ y := by linarith
  have h4 : x^2 - 2*x - 3 > 0 := by
    nlinarith 
  have h5 : y^2 - 2*y - 3 > 0 := by
    nlinarith
  have h6 : x^2 - 2*x - 3 ≥ y^2 - 2*y - 3 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), h3]
  rw [hf]
  -- Now we need to show that $\logb \ (1/2) \ (x^2 - 2 * x - 3) \leq \logb \ (1/2) \ (y^2 - 2 * y - 3)$
  -- Since $ \logb \ 1/2 \ u $ is a decreasing function of u, and x^2 - 2 * x - 3 \geq y^2 - 2 * y - 3
  have h7 : logb (1 / 2) (x ^ 2 - 2 * x - 3) ≤ logb (1 / 2) (y ^ 2 - 2 * y - 3) := by
    have h9 : logb (1 / 2) (x ^ 2 - 2 * x - 3) = log (x ^ 2 - 2 * x - 3) / log (1 / 2) := by
      field_simp [logb]
    have h10 : logb (1 / 2) (y ^ 2 - 2 * y - 3) = log (y ^ 2 - 2 * y - 3) / log (1 / 2) := by
      field_simp [logb]
    rw [h9, h10]
    have h11 : log (1 / 2) < 0 := by
      have : log (1 / 2) < log (1 : ℝ) := by
        apply Real.log_lt_log
        all_goals norm_num
      have h12 : log (1 : ℝ) = 0 := Real.log_one
      linarith [this, h12]
    have h13 : log (x^2 - 2 * x - 3) ≥ log (y^2 - 2 * y - 3) := by
      apply Real.log_le_log
      all_goals nlinarith 
    -- Now we can apply calculus with the fact that the numerator is large and denominator is negative.
    apply (div_le_div_right_of_neg (by linarith)).mpr 
    linarith 
  simpa using h7