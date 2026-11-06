import Mathlib

theorem algebra_144061 (f : ℝ → ℝ) :
    (∀ x y, x * f x - y * f y = (x - y) * f (x + y)) ↔ ∃ a b, ∀ x, f x = a * x + b := by
  constructor
  · -- Assume the functional equation, prove ∃ a, b, ∀ x, f x = a * x + b.
    intro h
    use (f 1 - f 0)
    use f 0
    intro x
    -- We need to show f x = (f 1 - f 0) * x + f 0.
    have eq1 := h x 0
    simp at eq1
    have eq2 := h x 1
    simp at eq2
    have eq3 := h 1 x
    simp at eq3
    have eq4 := h (x + 1) (-1)
    simp at eq4
    have eq5 := h 1 (-1)
    simp at eq5
    have eq6 := h (-x) x
    simp at eq6
    ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 ⊢
    all_goals
      try { nlinarith [h 1 1, h (-1) (-1), sq_nonneg (f 1 - f 0), sq_nonneg (f x - (f 1 - f 0) * x - f 0), sq_nonneg x, sq_nonneg (x - 1), sq_nonneg (f 1 - f (-1)), sq_nonneg (f 0 - f 1), sq_nonneg (f 1)] }
      <;> try { linarith [eq1, eq2, eq3, eq4, eq5, eq6] }
      <;> try { field_simp }
      <;> try { tauto }
      <;> try { try { tauto } }
  · -- Now prove the reverse direction: if ∃ a b, ∀ x, f x = a * x + b, then functional equation.
    rintro ⟨a, b, hf⟩
    intro x y
    have hx := hf x
    have hy := hf y
    have hxy := hf (x + y)
    rw [hx, hy, hxy]
    ring_nf
    <;> try { nlinarith }
    <;> try { field_simp }
    <;> try { tauto }
    <;> try { linarith }