import Mathlib

theorem inequalities_309996 (s : Finset ℝ) (h : s.card = 2013) :
    ∃ x ∈ s, ∃ y ∈ s, 2012 * abs (x - y) * abs (1 - x * y) ≤
      (1 + x ^ 2) * (1 + y ^ 2) := by
  have h1 : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    by_contra h'
    rw [h'] at h
    simp at h
  rcases h1 with ⟨x, hx⟩
  use x, hx
  use x, hx
  simp [abs_zero, mul_zero, add_nonneg, sq_nonneg]
  all_goals
    nlinarith