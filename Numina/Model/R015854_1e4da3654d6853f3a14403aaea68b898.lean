import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_4245 {f : ℝ → ℝ} (hf : f = λ x => logb (1/2) (x^2 - 2*x - 3)) :
    MonotoneOn f {x | x < -1} ∧ ∀ x, f x = logb (1/2) (x^2 - 2*x - 3) := by 
  have h1 : ∀ x, f x = logb (1 / 2) (x ^ 2 - 2 * x - 3) := by 
    intro x 
    rw [hf]
  
  constructor
  · -- Show that f is monotone on {x | x < -1}
    intro x hx y hy hxy
    have hx1 : x < -1 := hx
    have hy1 : y < -1 := hy
    have h2 : x ≤ y := hxy
    have hfx : f x = logb (1 / 2) (x ^ 2 - 2 * x - 3) := h1 x 
    have hfy : f y = logb (1 / 2) (y ^ 2 - 2 * y - 3) := h1 y 
    rw [hfx, hfy]
    
    have h3 : x ^ 2 - 2 * x - 3 > 0 := by 
      nlinarith 
    have h4 : y ^ 2 - 2 * y - 3 > 0 := by 
      nlinarith

    have h5 : x ^ 2 - 2 * x - 3 ≥ y ^ 2 - 2 * y - 3 := by
      nlinarith [show x + y < -2 by nlinarith]

    have h6 : logb (1 / 2) (x ^ 2 - 2 * x - 3) ≤ logb (1 / 2) (y ^ 2 - 2 * y - 3) := by

      have h7 : logb (1 / 2) (x ^ 2 - 2 * x - 3) = (log (x ^ 2 - 2 * x - 3) ) / (log (1 / 2)) := by 
        field_simp [logb]

      have h8 : logb (1 / 2) (y ^ 2 - 2 * y - 3) = (log (y ^ 2 - 2 * y - 3) ) / (log (1 / 2)) := by 
        field_simp [logb]

      rw [h7, h8]

      have h9 : log (1 / 2) < 0 := by 
        have h10 : log (1 / 2) = log 1 - log 2 := by 
          rw [log_div (by norm_num) (by norm_num)]
        have h11 : log 1 = 0 := by 
          rw [log_one]
        have h12 : log 2 > 0 := by 
          apply log_pos
          all_goals norm_num
        rw [h10, h11]
        linarith

      have h10 : log (x ^ 2 - 2 * x - 3) ≥ log (y ^ 2 - 2 * y - 3) := by
        apply Real.log_le_log
        all_goals nlinarith

      have h11 : (log (x ^ 2 - 2 * x - 3) ) / (log (1 / 2)) ≤ (log (y ^ 2 - 2 * y - 3) ) / (log (1 / 2)) := by 
        apply (div_le_div_right_of_neg (by linarith)).mpr
        linarith
  
      linarith

    exact h6
  · -- Show the definition of f
    intro x 
    specialize h1 x 
    simpa using h1