import Mathlib

theorem number_theory_326142 :
    {x : ℤ | ∃ u v w : ℤ, x = 12 * u + 8 * v + 4 * w} =
    {x : ℤ | ∃ u v w : ℤ, x = 20 * u + 16 * v + 12 * w} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume $x \in \{ \ldots \mid \ldots \}$ (i.e., the first set
    rintro ⟨u, v, w, h⟩
    use (3 * u + 2 * v + w), (- (3 * u + 2 * v + w)), (0)
    linarith
  · -- Assume $x \in \{\ldots \mid \ldots \}$ (i.e., the second set),
    rintro ⟨u, v, w, h⟩
    use (5 * u + 4 * v + 3 * w), (0), (-2 * (5 * u + 4 * v + 3 * w))
    linarith