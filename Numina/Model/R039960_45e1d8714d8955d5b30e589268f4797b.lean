import Mathlib

theorem inequalities_236385 (x : Fin 4 → ℝ) (h₀ : ∀ i j, i < j → x i ≥ x j)
    (h₁ : 2 ≤ x 3) (h₂ : x 1 + x 2 + x 3 ≥ x 0) :
    (x 0 + x 1 + x 2 + x 3)^2 ≤ 4 * x 0 * x 1 * x 2 * x 3 := by

  have h3 : x 0 ≥ x 1 := by
    apply h₀ 0 1
    all_goals 
      simp 
  have h4 : x 1 ≥ x 2 := by
    apply h₀ 1 2
    all_goals 
      simp 
  have h5 : x 2 ≥ x 3 := by
    apply h₀ 2 3
    all_goals 
      simp

  have h6 : x 3 ≥ 2 := by linarith

  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), 
      sq_nonneg (x 3 - 2), mul_nonneg (show 0 ≤ x 3 - 2 by linarith) (show 0 ≤ x 2 - 2 by nlinarith), 
      mul_nonneg (show 0 ≤ x 2 - 2 by nlinarith) (show 0 ≤ x 1 - 2 by nlinarith), 
      mul_nonneg (show 0 ≤ x 1 - 2 by nlinarith) (show 0 ≤ x 0 - 2 by nlinarith), 
      mul_nonneg (show 0 ≤ x 0 - x 1 by linarith) (show 0 ≤ x 1 - x 2 by linarith), 
      mul_nonneg (show 0 ≤ x 1 - x 2 by linarith) (show 0 ≤ x 2 - x 3 by linarith), 
      mul_nonneg (show 0 ≤ x 2 - x 3 by linarith) (show 0 ≤ x 3 - 2 by linarith)]