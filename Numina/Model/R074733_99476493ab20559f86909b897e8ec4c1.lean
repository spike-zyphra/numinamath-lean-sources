import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_283713 {f : ℝ → ℝ}
  (hf : ∀ x y, x < y → f x < f y)
  (hA : f 0 = -1) (hB : f 3 = 1) :
  {x | abs (f (x + 1)) < 1} = {x | -1 < x ∧ x < 2} := by
  ext x
  simp only [Set.mem_setOf_eq, abs_lt]
  constructor
  · -- First direction: If abs (f (x + 1)) < 1, then -1 < x ∧ x < 2
    intro h
    have h1 : -1 < f (x + 1) := h.1
    have h2 : f (x + 1) < 1 := h.2
    -- Prove x + 1 > 0
    have h3 : x + 1 > 0 := by
      by_contra h4
      push_neg at h4
      -- Case analysis: x + 1 = 0 or x + 1 < 0
      by_cases h4_eq : x + 1 = 0
      · -- If x + 1 = 0
        have hx1 : x + 1 = 0 := h4_eq
        have h5 : f (x + 1) = f 0 := by
          rw [show x + 1 = (0 : ℝ) by linarith [hx1]]
        rw [h5] at h1
        linarith [hA]
      · -- If x + 1 < 0
        have h4_lt : x + 1 < 0 := by
          apply lt_of_le_of_ne h4 (by 
            intro h
            apply h4_eq
            linarith
          )
        have h3' : f (x + 1) < f 0 := hf (x + 1) 0 (show (x + 1) < (0 : ℝ) by linarith)
        have h4 : f (x + 1) < -1 := by
          linarith [h3', hA]
        linarith
    -- Prove x + 1 < 3
    have h4 : x + 1 < 3 := by
      by_contra h5
      push_neg at h5
      -- Case analysis: x + 1 = 3 or x + 1 > 3
      by_cases h5_eq : x + 1 = 3
      · -- If x + 1 = 3
        have hx1 : x + 1 = 3 := h5_eq
        have h5' : f (x + 1) = f 3 := by
          rw [show x + 1 = (3 : ℝ) by linarith [hx1]]
        rw [h5'] at h2
        linarith [hB]
      · -- If x + 1 > 3
        have h5_gt : x + 1 > 3 := by
          apply lt_of_le_of_ne h5 (by
            intro h
            apply h5_eq
            linarith
          )
        have h3' : f 3 < f (x + 1) := hf 3 (x + 1) (show (3 : ℝ) < (x + 1) by linarith)
        have h4 : f (x + 1) ≥ 1 := by
          linarith [hB, h3']
        linarith
    -- Convert bounds on x + 1 to bounds on x
    constructor
    · -- Show -1 < x
      linarith
    · -- Show x < 2
      linarith
  · -- Second direction: If -1 < x ∧ x < 2, then abs (f (x + 1)) < 1
    rintro ⟨h1, h2⟩
    constructor
    · -- Show -1 < f (x + 1)
      have hx1 : x + 1 > (0 : ℝ) := by linarith
      have h3 : f 0 < f (x + 1) := hf 0 (x + 1) (show (0 : ℝ) < (x + 1) by linarith)
      have h4 : -1 < f (x + 1) := by
        linarith [hA, h3]
      linarith
    · -- Show f (x + 1) < 1
      have hx1 : x + 1 < (3 : ℝ) := by linarith
      have h3 : f (x + 1) < f 3 := hf (x + 1) 3 (show (x + 1) < (3 : ℝ) by linarith)
      have h4 : f (x + 1) < 1 := by
        linarith [hB, h3]
      linarith