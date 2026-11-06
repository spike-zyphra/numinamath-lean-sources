import Mathlib

/-
  Determine the solution set for the inequality $|x+3| - |x-2| \geq 3$.
-/
theorem algebra_9412 (x : ℝ) :
    abs (x + 3) - abs (x - 2) ≥ 3 ↔ x ∈ Set.Ici 1 := by

  constructor
  · -- solve the inequality
    intro hx
    -- case 1 : x ≤ -3
    by_cases h1 : x ≤ -3
    · have h1 : abs (x + 3) = - (x + 3) := by
        apply abs_eq_neg_self.mpr
        linarith
      have h2 : abs (x - 2) = - (x - 2) := by
        apply abs_eq_neg_self.mpr
        linarith
      simp [h1, h2] at hx
      linarith
    · -- case 2 : -3 < x ≤ 2
      have h1 : abs (x + 3) = (x + 3) := by
        apply abs_eq_self.mpr
        linarith
      by_cases h2 : x ≤ 2
      · have h2 : abs (x - 2) = - (x - 2) := by
          apply abs_eq_neg_self.mpr
          linarith
        simp [h1, h2] at hx
        simp
        linarith
      · -- case 3 : x > 2
        have h2 : abs (x - 2) = (x - 2) := by
          apply abs_eq_self.mpr
          linarith
        simp [h1, h2] at hx
        simp
        linarith
  · -- verify the answer
    intro hx
    simp at hx
    have h2 : abs (x + 3) = x + 3 := by
      refine abs_eq_self.mpr ?_
      linarith
    by_cases hx' : x ≤ 2
    · -- case 1 : 1 ≤ x ≤ 2
      have h4 : abs (x - 2) = - (x - 2) := by
        apply abs_eq_neg_self.mpr
        linarith
      rw [h2, h4]
      linarith
    · -- case 2 : x > 2
      have h4 : abs (x - 2) = (x - 2) := by
        apply abs_eq_self.mpr
        linarith
      rw [h2, h4]
      linarith
