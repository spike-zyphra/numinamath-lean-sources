import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_322221 {f : ℝ → ℝ} (hf : f = λ x => abs (2 * x - 4) - 3 * x + 8) :
    ∃ g : ℝ → ℝ, Function.LeftInverse g f ∧
      ∀ x, g x = if x ≤ 2 then -x + 4 else -1 / 5 * x + 12 / 5 := by 
  use λ x => if x ≤ 2 then -x + 4 else -1 / 5 * x + 12 / 5
  constructor
  · -- Show that g is a left inverse of f, i.e., g(f(x)) = x for all x.
    intro x
    rw [hf]
    by_cases h : x ≥ 2
    · -- When x ≥ 2, |2x - 4| = 2x - 4
      have h1 : abs (2 * x - 4) = 2 * x - 4 := abs_of_nonneg (show 2 * x - 4 ≥ 0 by linarith)
      have hx1 : abs (2 * x - 4) - 3 * x + 8 = -x + 4 := by 
        rw [h1]
        linarith
      have h13 : abs (2 * x - 4) - 3 * x + 8 ≤ 2 := by 
        have h14 : abs (2 * x - 4) = 2 * x - 4 := abs_of_nonneg (show 2 * x - 4 ≥ 0 by linarith)
        linarith
      have eq1 : (fun y => if y ≤ 2 then -y + 4 else -1/5 * y + 12/5) (abs (2 * x - 4) - 3 * x + 8) =
          -(abs (2 * x - 4) - 3 * x + 8) + 4 := by
        have h19 : abs (2 * x - 4) - 3 * x + 8 ≤ (2 : ℝ) := by 
          linarith
        simp [show abs (2 * x - 4) - 3 * x + 8 ≤ (2 : ℝ) by linarith]
      rw [eq1]
      all_goals
        linarith
    · -- When x < 2, |2x - 4| = -(2x - 4) = -2x + 4
      have h1 : abs (2 * x - 4) = -(2 * x - 4) := abs_of_neg (show 2 * x - 4 < 0 by linarith)
      have hx1 : abs (2 * x - 4) - 3 * x + 8 = -5 * x + 12 := by 
        rw [h1]
        linarith
      have h13 : abs (2 * x - 4) - 3 * x + 8 > (2 : ℝ) := by 
        have h14 : abs (2 * x - 4) = -(2 * x - 4) := abs_of_neg (show 2 * x - 4 < 0 by linarith)
        linarith
      have eq1 : (fun y => if y ≤ 2 then -y + 4 else -1/5 * y + 12/5) (abs (2 * x - 4) - 3 * x + 8) =
         (-1/5) * (abs (2 * x - 4) - 3 * x + 8) + 12/5 := by 
        have h19 : ¬ (abs (2 * x - 4) - 3 * x + 8 ≤ (2 : ℝ)) := by 
          linarith 
        simp [show ¬ (abs (2 * x - 4) - 3 * x + 8 ≤ (2 : ℝ)) by linarith, h19]
      rw [eq1]
      all_goals 
        linarith
  · -- Show that g x = if x ≤ 2 then -x + 4 else -1 / 5 * x + 12 / 5
    intro x 
    rfl