import Mathlib

theorem algebra_92294 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h : l' = l * 1.1 ∧ w' = w * 1.1) :
    (2 * (l' + w')) / (2 * (l + w)) = 1.1 := by
  rcases h with ⟨hl', hw'⟩
  have h1 : l' = l * 1.1 := hl'
  have h2 : w' = w * 1.1 := hw'
  have h3 : l + w > 0 := by linarith
  have eq1 : 2 * (l' + w') = 2.2 * (l + w) := by
    rw [h1, h2]
    ring
  have eq2 : (2 * (l' + w')) / (2 * (l + w)) = 1.1 := by
    rw [eq1]
    have h4 : (l + w) > 0 := h3
    field_simp
    <;> ring_nf
  exact eq2