import Mathlib

open Real Set

theorem inequalities_93262 (x : ℝ) :
    2 ≤ abs (x - 1) ∧ abs (x - 1) ≤ 5 ↔
    (x ≤ -1 ∧ x ≥ -4) ∨ (x ≥ 3 ∧ x ≤ 6) := by
  constructor
  · -- Assume 2 ≤ abs (x - 1) ∧ abs (x - 1) ≤ 5, prove (x ≤ -1 ∧ x ≥ -4) ∨ (x ≥ 3 ∧ x ≤ 6)
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : -4 ≤ x ∧ x ≤ 6 := by
      constructor
      · -- Rewrite abs (x - 1) ≤ 5 as -5 ≤ x - 1 ∧ x - 1 ≤ 5
        linarith [abs_le.mp h2]
      · -- Rewrite abs (x - 1) ≤ 5 as -5 ≤ x - 1 ∧ x - 1 ≤ 5
        linarith [abs_le.mp h2]
    by_cases h4 : x - 1 ≥ 0
    · -- If x - 1 ≥ 0, then abs (x - 1) = x - 1
      have h5 : abs (x - 1) = x - 1 := abs_of_nonneg h4
      have h6 : 2 ≤ x - 1 := by linarith [h1, h5]
      have h7 : x - 1 ≤ 5 := by linarith [h2, h5]
      have hx1 : x ≥ 3 := by linarith
      have hx2 : x ≤ 6 := by linarith
      right
      constructor <;> linarith
    · -- If x - 1 < 0, then abs (x - 1) = -(x - 1)
      have h4' : abs (x - 1) = -(x - 1) := abs_of_neg (lt_of_not_ge h4)
      have h6 : 2 ≤ -(x - 1) := by linarith [h1, h4']
      have h7 : -(x - 1) ≤ 5 := by linarith [h2, h4']
      have hx1 : x ≤ -1 := by linarith
      have hx2 : x ≥ -4 := by linarith
      left
      constructor <;> linarith
  · -- Assume (x ≤ -1 ∧ x ≥ -4) ∨ (x ≥ 3 ∧ x ≤ 6), prove 2 ≤ abs (x - 1) ∧ abs (x - 1) ≤ 5
    rintro (h | h)
    · -- Case (x ≤ -1 ∧ x ≥ -4)
      have h1 : x ≤ -1 := h.1
      have h2 : x ≥ -4 := h.2
      have h3 : x - 1 ≤ -2 := by linarith
      have h4 : abs (x - 1) = -(x - 1) := by
        rw [abs_of_nonpos (by linarith)]
      constructor
      · -- 2 ≤ abs (x - 1)
        rw [h4]
        linarith
      · -- abs (x - 1) ≤ 5
        rw [h4]
        linarith
    · -- Case (x ≥ 3 ∧ x ≤ 6)
      have h1 : x ≥ 3 := h.1
      have h2 : x ≤ 6 := h.2
      have h3 : x - 1 ≥ 2 := by linarith
      have h4 : abs (x - 1) = x - 1 := by
        rw [abs_of_nonneg (by linarith)]
      constructor
      · -- 2 ≤ abs (x - 1)
        rw [h4]
        linarith
      · -- abs (x - 1) ≤ 5
        rw [h4]
        linarith