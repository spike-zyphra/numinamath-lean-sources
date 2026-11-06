import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_189005 {f : ℝ → ℝ}
  (hf : ∀ x, x < 1 → f x = 0)
  (hf' : ∀ x, x ≥ 1 → f x = 2 * x - 2) :
  {x | f (f (f (f x))) = x}.encard = 2 := by
  have h1 : ∀ x, f (f (f (f x))) = x ↔ x = 0 ∨ x = 2 := by
    intro x
    constructor
    · -- Assume that $f(f(f(f(x)))) = x$.
      intro h
      have h2 : f (f (f (f x))) = x := h
      by_cases h21 : x < 1
      · -- Case 1: x < 1
        have hx1 : f x = 0 := hf x h21
        have hfx1 : f (f x) = 0 := by
          rw [hx1]
          apply hf
          linarith
        have hf2x1 : f (f (f x)) = 0 := by
          rw [hfx1]
          apply hf
          linarith
        have hf3x1 : f (f (f (f x))) = 0 := by
          rw [hf2x1]
          apply hf
          linarith
        rw [hf3x1] at h2
        left
        linarith
      · -- Case 2: x ≥ 1
        have hx1' : f x = 2 * x - 2 := hf' x (by linarith)
        by_cases h22 : x < 1.5
        · -- Case 2a: 1 ≤ x < 1.5
          have hfx2a : f (f x) = 0 := by
            rw [hx1']
            have h3 : (2 * x - 2 : ℝ) < 1 := by
              nlinarith
            rw [hf (2 * x - 2) h3]
            <;> nlinarith
          have hf2x2a : f (f (f x)) = 0 := by
            rw [hfx2a]
            apply hf
            linarith
          have hf3x2a : f (f (f (f x))) = 0 := by
            rw [hf2x2a]
            apply hf
            linarith
          rw [hf3x2a] at h2
          nlinarith
        · -- Case 2b: x ≥ 1.5
          have h22' : x ≥ 1.5 := by nlinarith
          have hfx2b : f (f x) = 4 * x - 6 := by
            rw [hx1']
            have h3 : (2 * x - 2 : ℝ) ≥ 1 := by
              nlinarith
            rw [hf' (2 * x - 2) h3]
            ring_nf
            <;> nlinarith
          by_cases h23 : x < 1.75
          · -- Case 2b1: 1.5 ≤ x < 1.75
            have hf2x2b1 : f (f (f x)) = 0 := by
              rw [hfx2b]
              have h4 : (4 * x - 6 : ℝ) < 1 := by
                nlinarith
              rw [hf (4 * x - 6) h4]
              <;> nlinarith
            have hf3x2b1 : f (f (f (f x))) = 0 := by
              rw [hf2x2b1]
              apply hf
              linarith
            rw [hf3x2b1] at h2
            nlinarith
          · -- Case 2b2: x ≥ 1.75
            have h23' : x ≥ 1.75 := by nlinarith
            have hf2x2b2 : f (f (f x)) = 8 * x - 14 := by
              rw [hfx2b]
              have h4 : (4 * x - 6 : ℝ) ≥ 1 := by
                nlinarith
              rw [hf' (4 * x - 6) h4]
              ring_nf
              <;> nlinarith
            by_cases h24 : x < 1.875
            · -- Case 2b2a: 1.75 ≤ x < 1.875
              have hf3x2b2a : f (f (f (f x))) = 0 := by
                rw [hf2x2b2]
                have h5 : (8 * x - 14 : ℝ) < 1 := by
                  nlinarith
                rw [hf (8 * x - 14) h5]
                <;> nlinarith
              rw [hf3x2b2a] at h2
              nlinarith
            · -- Case 2b2b: x ≥ 1.875
              have h24' : x ≥ 1.875 := by nlinarith
              have hf3x2b2b : f (f (f (f x))) = 16 * x - 30 := by
                rw [hf2x2b2]
                have h5 : (8 * x - 14 : ℝ) ≥ 1 := by
                  nlinarith
                rw [hf' (8 * x - 14) h5]
                ring_nf
                <;> nlinarith
              rw [hf3x2b2b] at h2
              right
              linarith
    · -- Show that if x = 0 or x = 2, then f(f(f(f(x)))) = x.
      intro h
      rcases h with (rfl | rfl)
      · -- Check x = 0
        norm_num [hf, hf']
      · -- Check x = 2
        norm_num [hf, hf']
  have h3 : {x | f (f (f (f x))) = x} = {0, 2} := by
    ext x
    simp [h1]
  rw [h3]
  rw [Set.encard_pair (by norm_num)]
  all_goals norm_num
  all_goals norm_num