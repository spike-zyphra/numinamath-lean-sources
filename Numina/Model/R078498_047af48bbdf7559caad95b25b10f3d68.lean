import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_212132 (M N : ℝ × ℝ)
  (hM : M.1 ≥ 0 ∧ M.2 ≥ 0 ∧ M.1 + 2 * M.2 ≤ 6 ∧ 3 * M.1 + M.2 ≤ 12)
  (hN : N.1 ≥ 0 ∧ N.2 ≥ 0 ∧ N.1 + 2 * N.2 ≤ 6 ∧ 3 * N.1 + N.2 ≤ 12)
  (a : ℝ × ℝ) (ha : a = (1, -1)) :
  (N.1 - M.1) * a.1 + (N.2 - M.2) * a.2 ∈ Icc (-7) 7 := by
  rcases hM with ⟨hm1, hm2, hm3, hm4⟩
  rcases hN with ⟨hn1, hn2, hn3, hn4⟩
  rw [ha]
  simp [mem_Icc]
  constructor
  · -- Show that the expression is greater than or equal to -7
    ring_nf
    linarith
  · -- Show that the expression is less than or equal to 7
    ring_nf
    linarith