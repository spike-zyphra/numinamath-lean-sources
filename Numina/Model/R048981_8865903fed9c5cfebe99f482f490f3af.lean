import Mathlib

open Real Set

theorem inequalities_8864 (a b c : ℝ) (ha : 0 < a ∧ a ≤ 2) (hb : 0 < b ∧ b ≤ 2)
    (hc : 0 < c ∧ c ≤ 2) (h : b ≥ 3 * a ∨ a + b ≤ 4 / 3) :
    max (max (b - a) (c - b)) (4 - 2 * c) ≥ 2 / 3 := by
  rcases h with (h | h)
  · -- Case 1: b ≥ 3a
    by_cases h1 : b - a ≥ c - b
    · -- If b - a ≥ c - b, then max (b - a) (c - b) = b - a
      have h1' : max (b - a) (c - b) = b - a := by apply max_eq_left; linarith
      rw [h1']
      by_cases h2 : b - a ≥ 4 - 2 * c
      · -- If b - a ≥ 4 - 2 * c, then max (b - a) (4 - 2 * c) = b - a
        have h2' : max (b - a) (4 - 2 * c) = b - a := by apply max_eq_left; linarith
        rw [h2']
        linarith [h1, h2, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
      · -- Otherwise, max (b - a) (4 - 2 * c) = 4 - 2 * c
        have h2' : max (b - a) (4 - 2 * c) = 4 - 2 * c := by apply max_eq_right; linarith
        rw [h2']
        linarith [h1, h2, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
    · -- If b - a < c - b, then max (b - a) (c - b) = c - b
      have h1' : max (b - a) (c - b) = c - b := by apply max_eq_right; linarith
      rw [h1']
      by_cases h2 : c - b ≥ 4 - 2 * c
      · -- If c - b ≥ 4 - 2 * c, then max (c - b) (4 - 2 * c) = c - b
        have h2' : max (c - b) (4 - 2 * c) = c - b := by apply max_eq_left; linarith
        rw [h2']
        linarith [h1, h2, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
      · -- Otherwise, max (c - b) (4 - 2 * c) = 4 - 2 * c
        have h2' : max (c - b) (4 - 2 * c) = 4 - 2 * c := by apply max_eq_right; linarith
        rw [h2']
        linarith [h1, h2, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
  · -- Case 2: a + b ≤ 4 / 3
    by_cases h1 : b - a ≥ c - b
    · -- If b - a ≥ c - b, then max (b - a) (c - b) = b - a
      have h1' : max (b - a) (c - b) = b - a := by apply max_eq_left; linarith
      rw [h1']
      by_cases h2 : b - a ≥ 4 - 2 * c
      · -- If b - a ≥ 4 - 2 * c, then max (b - a) (4 - 2 * c) = b - a
        have h2' : max (b - a) (4 - 2 * c) = b - a := by apply max_eq_left; linarith
        rw [h2']
        linarith [h1, h2, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
      · -- Otherwise, max (b - a) (4 - 2 * c) = 4 - 2 * c
        have h2' : max (b - a) (4 - 2 * c) = 4 - 2 * c := by apply max_eq_right; linarith
        rw [h2']
        linarith [h1, h2, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
    · -- If b - a < c - b, then max (b - a) (c - b) = c - b
      have h1' : max (b - a) (c - b) = c - b := by apply max_eq_right; linarith
      rw [h1']
      by_cases h2 : c - b ≥ 4 - 2 * c
      · -- If c - b ≥ 4 - 2 * c, then max (c - b) (4 - 2 * c) = c - b
        have h2' : max (c - b) (4 - 2 * c) = c - b := by apply max_eq_left; linarith
        rw [h2']
        linarith [h1, h2, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
      · -- Otherwise, max (c - b) (4 - 2 * c) = 4 - 2 * c
        have h2' : max (c - b) (4 - 2 * c) = 4 - 2 * c := by apply max_eq_right; linarith
        rw [h2']
        linarith [h1, h2, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]