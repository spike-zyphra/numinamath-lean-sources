import Mathlib
open Real Set

theorem algebra_9267 {f : ℝ → ℝ} (hf : f = λ x => logb 0.2 (x^2 - 6 * x + 8)) :
    MonotoneOn f (Iio 2) ∧ AntitoneOn f (Ioi 4) := by 
  constructor
  · -- Prove that f is monotone on (-∞, 2)
    intros x hx y hy hxy
    rw [hf]
    simp at *
    have h1 : x < 2 := hx
    have h2 : y < 2 := hy
    have h3 : x ≤ y := hxy
    have h4 : x ^ 2 - 6 * x + 8 > 0 := by
      nlinarith 
    have h5 : y ^ 2 - 6 * y + 8 > 0 := by 
      nlinarith 
    have h14 : x ^ 2 - 6 * x + 8 ≥ y ^ 2 - 6 * y + 8 := by 
      have h30 : x ≤ y := hxy
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x - y), sq_nonneg ((x + y) - 4), mul_nonneg (show (0 : ℝ) ≤ 2 - x by nlinarith) (show (0 : ℝ) ≤ 2 - y by nlinarith)]
    have h7 : logb 0.2 (x^2 - 6 * x + 8) ≤ logb 0.2 (y^2 - 6 * y + 8) := by 
      have h8 : logb 0.2 (x^2 - 6 * x + 8) ≤ logb 0.2 (y^2 - 6 * y + 8) := by 
        have h9 : (0.2 : ℝ) < 1 := by norm_num
        have h10 : logb 0.2 (x^2 - 6 * x + 8) = (log (x^2 - 6 * x + 8)) / (log (0.2 : ℝ)) := by 
          field_simp [logb]
        have h11 : logb 0.2 (y^2 - 6 * y + 8) = (log (y^2 - 6 * y + 8)) / (log (0.2 : ℝ)) := by 
          field_simp [logb]
        have h12 : log (x^2 - 6 * x + 8) ≥ log (y^2 - 6 * y + 8) := by
          apply Real.log_le_log 
          all_goals nlinarith
        have h13 : log (0.2 : ℝ) < 0 := by
          have : log (0.2 : ℝ) < log (1 : ℝ) := by
            apply Real.log_lt_log
            all_goals norm_num
          have h2 : log (1 : ℝ) = 0 := by
            simp [log_one]
          linarith
        rw [h10, h11]
        apply (div_le_div_right_of_neg (by linarith)).mpr 
        linarith 
      linarith
    exact h7
  · -- Prove that f is antitone on (4, ∞)
    intros x hx y hy hxy
    rw [hf]
    simp at *
    have h1 : x > 4 := by
      simpa using hx
    have h2 : y > 4 := by
      simpa using hy
    have h3 : x ≤ y := hxy
    have h4 : x ^ 2 - 6 * x + 8 > 0 := by
      nlinarith 
    have h5 : y ^ 2 - 6 * y + 8 > 0 := by 
      nlinarith
    have h14 : x ^ 2 - 6 * x + 8 ≤ y ^ 2 - 6 * y + 8 := by 
      have h30 : x ≤ y := hxy
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x - y), sq_nonneg ((x + y) - 4), mul_nonneg (show (0 : ℝ) ≤ x - 4 by nlinarith) (show (0 : ℝ) ≤ y - 4 by nlinarith)]
    have h7 : logb 0.2 (x^2 - 6 * x + 8) ≥ logb 0.2 (y^2 - 6 * y + 8) := by 
      have h8 : logb 0.2 (x^2 - 6 * x + 8) ≥ logb 0.2 (y^2 - 6 * y + 8) := by 
        have h9 : (0.2 : ℝ) < 1 := by norm_num
        have h10 : logb 0.2 (x^2 - 6 * x + 8) = (log (x^2 - 6 * x + 8)) / (log (0.2 : ℝ)) := by
          field_simp [logb]
        have h11 : logb 0.2 (y^2 - 6 * y + 8) = (log (y^2 - 6 * y + 8)) / (log (0.2 : ℝ)) := by 
          field_simp [logb]
        have h12 : log (x^2 - 6 * x + 8) ≤ log (y^2 - 6 * y + 8) := by
          apply Real.log_le_log 
          all_goals nlinarith
        have h13 : log (0.2 : ℝ) < 0 := by
          have : log (0.2 : ℝ) < log (1 : ℝ) := by
            apply Real.log_lt_log
            all_goals norm_num
          have h2 : log (1 : ℝ) = 0 := by
            simp [log_one]
          linarith
        rw [h10, h11]
        apply (div_le_div_right_of_neg (by linarith)).mpr
        linarith 
      linarith
    exact h7