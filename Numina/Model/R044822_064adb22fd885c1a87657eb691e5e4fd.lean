import Mathlib

theorem inequalities_86043 {s : Finset ℝ} (h : s.card = 101):
    ∃ u v, u ∈ s ∧ v ∈ s ∧ 100 * |u - v| * |1 - u * v| ≤ (1 + u ^ 2) * (1 + v ^ 2) := by

  have h1 : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    by_contra h'
    rw [h'] at h
    simp at h

  rcases h1 with ⟨a, ha⟩

  use a, a
  constructor
  · exact ha
  constructor
  · exact ha
  have h2 : |a - a| = 0 := by
    simp

  have h3 : 100 * |a - a| * |1 - a * a| = 0 := by
    rw [h2]
    norm_num

  have h4 : (1 + a ^ 2) * (1 + a ^ 2) ≥ 0 := by
    positivity

  linarith [h3, h4]