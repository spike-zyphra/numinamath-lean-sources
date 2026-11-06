import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_318053 (a b c : ℝ) (ha : a < b) (hb : b < c) :
    IsLeast {x | ∃ t, x = abs (t - a) + abs (t - b) + abs (t - c)} (c - a) := by
  constructor
  · -- prove c - a in the set
    use b
    have h1 : abs (b - a) = b - a := abs_of_pos (by linarith)
    have h2 : abs (b - b) = 0 := by norm_num
    have h3 : abs (b - c) = c - b := by
      rw [show b - c = -(c - b) by ring]
      rw [abs_neg]
      apply abs_of_pos (by linarith)
    rw [h1, h2, h3]
    linarith
  · -- prove c - a ≤ x for all x in the set
    rintro x ⟨t, ht⟩
    have h1 : abs (t - a) + abs (t - b) + abs (t - c) ≥ c - a := by
      by_cases h1 : t ≥ c
      · -- case t ≥ c
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- case b ≤ t < c
        by_cases h2 : t ≥ b
        · -- case b ≤ t < c
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith)]
          linarith
        · -- case a ≤ t < b
          by_cases h3 : t ≥ a
          · -- case a ≤ t < b
            rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
            linarith
          · -- case t < a
            rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
            linarith
    linarith [ht, h1]