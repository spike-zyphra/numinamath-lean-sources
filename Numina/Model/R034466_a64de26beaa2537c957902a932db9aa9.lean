import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_301526 {f g : ℝ → ℝ}
  (hf : ∀ x, x ≤ 1 → f x = -x^2 + x)
  (hf' : ∀ x, x > 1 → f x = logb (1/3) x)
  (hg : ∀ x, g x = abs (x - k) + abs (x - 1)) :
  (∀ x1 x2, f x1 ≤ g x2) ↔ k ≤ 3/4 ∨ k ≥ 5/4 := by
  constructor
  · -- First direction: if ∀ x1 x2, f x1 ≤ g x2, then k ≤ 3/4 ∨ k ≥ 5/4
    intro h
    have h1 : f (1 / 2) ≤ g 1 := h (1 / 2) 1
    have h2 : f (1 / 2) = - (1 / 2) ^ 2 + (1 / 2) := by
      specialize hf (1 / 2) (by norm_num)
      simpa using hf
    have h3 : g 1 = abs (1 - k) + abs (1 - 1) := by
      specialize hg 1
      simpa using hg
    have h4 : abs (1 - 1 : ℝ) = 0 := by
      norm_num [abs_zero]
    rw [h2] at h1
    rw [h3] at h1
    rw [h4] at h1
    have h7 : abs (1 - k) ≥ 1 / 4 := by
      linarith
    cases' abs_cases (1 - k) with h8 h8
    · -- Case where 1 - k ≥ 0, so k ≤ 1
      left
      linarith
    · -- Case where 1 - k < 0, so k > 1
      right
      linarith
  · -- Second direction: if k ≤ 3/4 ∨ k ≥ 5/4, then ∀ x1 x2, f x1 ≤ g x2
    rintro (h | h)
    · -- Case where k ≤ 3/4
      intro x1 x2
      have h1 : f x1 ≤ 1 / 4 := by
        by_cases h2 : x1 ≤ 1
        · -- Case where x1 ≤ 1
          have h3 : f x1 = -x1^2 + x1 := by
            specialize hf x1 h2
            simpa using hf
          nlinarith [sq_nonneg (x1 - 1 / 2)]
        · -- Case where x1 > 1
          have h4 : x1 > 1 := by linarith
          have h5 : f x1 = logb (1 / 3) x1 := by
            specialize hf' x1 h4
            simpa using hf'
          have h6 : logb (1 / 3) x1 < 0 := by
            have h7 : logb (1 / 3) x1 < logb (1 / 3) 1 := by
              apply Real.logb_lt_logb_of_base_lt_one
              all_goals
                linarith
            have h8 : logb (1 / 3) 1 = 0 := by
              norm_num [logb_one]
            linarith
          linarith
      have h2 : g x2 ≥ 1 / 4 := by
        have h3 : g x2 = abs (x2 - k) + abs (x2 - 1) := by
          specialize hg x2
          simpa using hg
        have h4 : abs (x2 - k) + abs (x2 - 1) ≥ abs (k - 1) := by
          have h5 : abs (x2 - k) + abs (x2 - 1) ≥ abs ((x2 - k) - (x2 - 1)) := by
            apply abs_sub
          have h6 : (x2 - k) - (x2 - 1) = 1 - k := by
            linarith
          have h7 : abs ((x2 - k) - (x2 - 1)) = abs (1 - k) := by
            rw [h6]
          have h8 : abs (1 - k) = abs (k - 1) := by
            rw [show 1 - k = -(k - 1) by ring]
            rw [abs_neg]
          linarith [h5, h7, h8, abs_nonneg (x2 - k), abs_nonneg (x2 - 1)]
        have h5 : abs (k - 1) ≥ 1 / 4 := by
          have h6 : k ≤ 3 / 4 := h
          have h7 : k - 1 ≤ 3 / 4 - 1 := by linarith
          rw [abs_of_nonpos (by linarith : k - 1 ≤ 0)]
          linarith
        linarith [h3, h4, h5]
      linarith
    · -- Case where k ≥ 5/4
      intro x1 x2
      have h1 : f x1 ≤ 1 / 4 := by
        by_cases h2 : x1 ≤ 1
        · -- Case where x1 ≤ 1
          have h3 : f x1 = -x1^2 + x1 := by
            specialize hf x1 h2
            simpa using hf
          nlinarith [sq_nonneg (x1 - 1 / 2)]
        · -- Case where x1 > 1
          have h4 : x1 > 1 := by linarith
          have h5 : f x1 = logb (1 / 3) x1 := by
            specialize hf' x1 h4
            simpa using hf'
          have h6 : logb (1 / 3) x1 < 0 := by
            have h7 : logb (1 / 3) x1 < logb (1 / 3) 1 := by
              apply Real.logb_lt_logb_of_base_lt_one
              all_goals
                linarith
            have h8 : logb (1 / 3) 1 = 0 := by
              norm_num [logb_one]
            linarith
          linarith
      have h2 : g x2 ≥ 1 / 4 := by
        have h3 : g x2 = abs (x2 - k) + abs (x2 - 1) := by
          specialize hg x2
          simpa using hg
        have h4 : abs (x2 - k) + abs (x2 - 1) ≥ abs (k - 1) := by
          have h5 : abs (x2 - k) + abs (x2 - 1) ≥ abs ((x2 - k) - (x2 - 1)) := by
            apply abs_sub
          have h6 : (x2 - k) - (x2 - 1) = 1 - k := by
            linarith
          have h7 : abs ((x2 - k) - (x2 - 1)) = abs (1 - k) := by
            rw [h6]
          have h8 : abs (1 - k) = abs (k - 1) := by
            rw [show 1 - k = -(k - 1) by ring]
            rw [abs_neg]
          linarith [h5, h7, h8, abs_nonneg (x2 - k), abs_nonneg (x2 - 1)]
        have h5 : abs (k - 1) ≥ 1 / 4 := by
          have h6 : k ≥ 5 / 4 := h
          have h7 : k - 1 ≥ 5 / 4 - 1 := by linarith
          rw [abs_of_nonneg (by linarith : k - 1 ≥ 0)]
          linarith
        linarith [h3, h4, h5]
      linarith