import Mathlib

theorem algebra_235270 (f : ℝ → ℝ) (hf : f = fun x => (3 * x - 1) / (x + 1)) :
    {y | y ≠ 3} = {y | ∃ x, f x = y} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Show that if y ≠ 3, then there exists some x such that f x = y
    intro hy
    use (-1 - y) / (y - 3)
    rw [hf]
    field_simp [(show y - 3 ≠ 0 by
      intro h'
      apply hy
      linarith
    ), (show (-1 - y) / (y - 3) + 1 ≠ 0 by
      by_contra h
      have h1 : (-1 - y) / (y - 3) + 1 = 0 := by linarith
      have h2 : y - 3 ≠ 0 := by
        intro h3
        apply hy
        linarith
      have eq : (-1 - y) + (y - 3) * 1 = 0 := by
        field_simp [h2] at h1
        linarith
      nlinarith
    )
    ]
    <;> ring_nf <;> field_simp [(show y - 3 ≠ 0 by
      intro h'
      apply hy
      linarith
    )] <;> nlinarith
  · -- Show that if there exists some x such that f x = y, then y ≠ 3
    intro hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    by_contra h
    have h1 : y = 3 := by
      tauto
    rw [h1] at hx
    by_cases h' : x + 1 = 0
    · -- Case where x + 1 = 0, so x = -1
      rw [h'] at hx
      norm_num [h'] at hx
      all_goals linarith
    · -- Case where x + 1 ≠ 0
      have h2 : x + 1 ≠ 0 := h'
      field_simp [h2] at hx
      all_goals nlinarith