import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_12729 (M N : ℝ × ℝ)
  (hM : M.1 ≥ 0 ∧ M.2 ≥ 0 ∧ M.1 + 2 * M.2 ≤ 6 ∧ 3 * M.1 + M.2 ≤ 12)
  (hN : N.1 ≥ 0 ∧ N.2 ≥ 0 ∧ N.1 + 2 * N.2 ≤ 6 ∧ 3 * N.1 + N.2 ≤ 12)
  (a : ℝ × ℝ) (ha : a = (1, -1)) :
  -7 ≤ (M.1 - N.1) * a.1 + (M.2 - N.2) * a.2 ∧
  (M.1 - N.1) * a.1 + (M.2 - N.2) * a.2 ≤ 7 := by

  rcases hM with ⟨hm1, hm2, hm3, hm4⟩
  rcases hN with ⟨hn1, hn2, hn3, hn4⟩
  have ha1 : a.1 = 1 := by
    simp [ha]
  have ha2 : a.2 = -1 := by
    simp [ha]

  constructor
  · -- proving the left part: -7 ≤ (M.1 - N.1) * a.1 + (M.2 - N.2) * a.2
    rw [ha1, ha2]
    linarith
  · -- proving the right part: (M.1 - N.1) * a.1 + (M.2 - N.2) * a.2 ≤ 7
    rw [ha1, ha2]
    linarith