import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_308141 {f : ℝ → ℝ} (hf : ∀ x y, x < y → f x > f y)
  (hA : f 0 = 3) (hB : f 3 = -1) :
  {x | abs (f (x + 1) - 1) < 2} = {x | -1 < x ∧ x < 2} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume |f(x+1) - 1| < 2, prove -1 < x ∧ x < 2
    intro h
    have h1 : -2 < f (x + 1) - 1 := by
      linarith [abs_lt.mp h]
    have h2 : f (x + 1) - 1 < 2 := by
      linarith [abs_lt.mp h]
    have h3 : -1 < f (x + 1) := by linarith
    have h4 : f (x + 1) < 3 := by linarith
    have h5 : x > -1 := by
      by_contra h
      push_neg at h
      have h6 : x + 1 ≤ (0 : ℝ) := by
        linarith
      have h7 : f (x + 1) ≥ f (0 : ℝ) := by 
        by_cases h8 : x + 1 < (0 : ℝ)
        · -- If x + 1 < 0, then by strict decreasing, f(x + 1) > f(0)
          have h9 : f (x + 1) > f (0 : ℝ) := by
            apply hf
            all_goals linarith
          linarith
        · -- x + 1 = 0
          have h10 : x + 1 = (0 : ℝ) := by
            linarith
          rw [h10]
      have h8 : f (0 : ℝ) = (3 : ℝ) := hA
      have h9 : f (x + 1) ≥ (3 : ℝ) := by
        nlinarith [h7, h8]
      nlinarith [h4, h9]
    have h6 : x < (2 : ℝ) := by
      by_contra h
      push_neg at h
      have h7 : x + 1 ≥ (3 : ℝ) := by
        linarith
      have h8 : f (x + 1) ≤ f (3 : ℝ) := by 
        by_cases h9 : x + 1 > (3 : ℝ)
        · -- If x + 1 > 3, then since f is strictly decreasing, f(3) > f(x+1)
          have h10 : f (3 : ℝ) > f (x + 1) := by
            apply hf
            all_goals linarith
          linarith
        · -- x +1 =3
          have h10 : x + 1 = (3 : ℝ) := by
            linarith
          rw [h10]
      have h9 : f (3 : ℝ) = -1 := hB
      have h10 : f (x + 1) ≤ (-1 : ℝ) := by
        nlinarith [h8, h9]
      nlinarith [h3, h10]
    constructor <;> linarith [h5, h6]
  · -- Assume -1 < x ∧ x < 2, prove |f(x+1) - 1| < 2
    rintro ⟨h1, h2⟩
    have h3 : -1 < f (x + 1) := by
      have h4 : x + 1 < (3 : ℝ) := by
        linarith
      have h5 : f (x + 1) > f (3 : ℝ) := by
        apply hf
        all_goals linarith
      have h6 : f (3 : ℝ) = -1 := hB
      linarith [h5, h6]
    have h4 : f (x + 1) < (3 : ℝ) := by
      have h5 : x + 1 > (0 : ℝ) := by
        linarith
      have h6 : f (x + 1) < f (0 : ℝ) := by
        apply hf
        all_goals linarith
      have h7 : f (0 : ℝ) = (3 : ℝ) := hA
      linarith [h6, h7]
    have h1' : -2 < f (x + 1) - 1 := by
      linarith
    have h2' : f (x + 1) - 1 < (2 : ℝ) := by
      linarith
    have h3' : abs (f (x + 1) - 1) < 2 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith [h3']