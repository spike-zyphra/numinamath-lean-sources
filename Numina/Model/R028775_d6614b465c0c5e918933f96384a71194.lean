import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_200918 {f : ℝ → ℝ}
  (hf : ∀ x, x ≤ 1 → f x = abs x)
  (hf' : ∀ x, x > 1 → f x = 2 - x) :
  ∀ x, f x + f (2 - x) = 2 ↔ x = 1 := by
  intro x
  constructor
  · intro h
    by_cases h1 : x ≤ 1
    · -- case where x ≤ 1
      have hfx : f x = abs x := hf x h1
      have h1' : x ≤ 1 := h1
      by_cases h3 : (2 - x) ≤ 1
      · have h2fx : f (2 - x) = abs (2 - x) := hf (2 - x) h3
        rw [hfx, h2fx] at h
        cases' abs_cases x with hx hx
        · -- case where x ≥ 0
          cases' abs_cases (2 - x) with h2x h2x
          · -- case where 2 - x ≥ 0
            linarith
          · -- case where 2 - x < 0
            linarith
        · -- case where x < 0
          cases' abs_cases (2 - x) with h2x h2x
          · -- case where 2 - x ≥ 0
            linarith
          · -- case where 2 - x < 0
            linarith
      · -- case where 2 - x > 1 (so x < 1 is already false)
        have h2fx' : f (2 - x) = (2 - (2 - x)) := hf' (2 - x) (by linarith)
        rw [hfx, h2fx'] at h
        cases' abs_cases x with hx hx
        all_goals
        nlinarith
    · -- case where x > 1
      have h1' : x > 1 := by linarith
      have hfx : f x = 2 - x := hf' x h1'
      have h2fx : f (2 - x) = abs (2 - x) := hf (2 - x) (by linarith)
      rw [hfx, h2fx] at h
      cases' abs_cases (2 - x) with hx hx
      · -- case where 2 - x ≥ 0
        all_goals
          linarith
      · -- case where 2 - x < 0
        all_goals
          linarith
  · -- backwards direction (x = 1 → f x + f (2 - x) = 2)
    intro h
    rw [h]
    norm_num [hf, hf', abs]
    all_goals linarith [abs_nonneg (1 : ℝ)]