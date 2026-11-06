import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_293089 {a : ℝ} (ha : a = 1) :
    MonotoneOn (λ x => abs (x - a)) (Ici 1) ∧ ¬(∀ a : ℝ, MonotoneOn (λ x => abs (x - a)) (Ici 1) → a = 1) := by 
  constructor 
  · -- Show when a = 1, f(x) = |x - 1| is monotone on [1, ∞).
    rw [ha]
    intro x hx y hy hxy
    simp at hx hy ⊢
    -- x, y ≥ 1, so x - 1 ≥ 0, y - 1 ≥ 0, therefore |x - 1| = x - 1, |y - 1| = y - 1.
    rw [abs_of_nonneg (show (x - (1 : ℝ)) ≥ 0 by linarith), abs_of_nonneg (show (y - (1 : ℝ)) ≥ 0 by linarith)]
    all_goals linarith
  · -- Show there's a ≠ 1, f(x) = |x - a| is monotone on [1, ∞).
    push_neg 
    -- Take a = 0, check the conditions.
    use 0 
    constructor 
    · -- Show f(x) = |x| is monotone on [1, ∞).
      intro x hx y hy hxy 
      simp at hx hy ⊢ 
      -- Both x and y are non-negative, so |x| = x, |y| = y. Therefore it's the same as identity function x ≤ y.
      have hx2 : x ≥ (0 : ℝ) := by linarith 
      have hy2 : y ≥ (0 : ℝ) := by linarith 
      have h1 : (abs (x - (0 : ℝ))) = x := by 
        simp [abs_of_nonneg] 
        all_goals linarith 
      have h2 : (abs (y - (0 : ℝ))) = y := by 
        simp [abs_of_nonneg] 
        all_goals linarith 
      have h3 : abs (x - (0 : ℝ)) ≤ abs (y - (0 : ℝ)) := by 
        rw [h1, h2] 
        all_goals linarith 
      simpa using h3
    · -- Show that 0 ≠ 1 
      norm_num 
      all_goals try { tauto } 
      all_goals try { linarith }
      all_goals try { norm_num }