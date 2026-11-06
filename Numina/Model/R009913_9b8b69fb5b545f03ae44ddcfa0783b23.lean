import Mathlib

theorem algebra_10774 (x : ℝ) :
    (2 * x ∈ Set.Ioo 1 2 ∧ 3 * x ∈ Set.Ioo 1 2) ↔
    x ∈ Set.Ioo (1 / 2) (2 / 3) := by
  simp only [Set.mem_Ioo]
  constructor
  · -- Assume both $2x$ and $3x$ are in $(1,2)$, we need to show $x \in \left( \frac{1}{2}, \frac{2}{3} \right)$
    rintro ⟨⟨h21, h22⟩, ⟨h31, h32⟩⟩
    constructor
    · -- Show $\frac{1}{2} < x$
      linarith
    · -- Show $x < \frac{2}{3}$
      linarith
  · -- Assume $x \in \left( \frac{1}{2}, \frac{2}{3} \right)$, we need to show both $2x$ and $3x$ are in $(1,2)$
    rintro ⟨h1, h2⟩
    constructor
    · -- Show $2 * x \in Set.Ioo 1 2$
      constructor
      · -- Show $1 < 2 * x$
        linarith
      · -- Show $2 * x < 2$
        linarith
    · -- Show $3 * x \in Set.Ioo 1 2$
      constructor
      · -- Show $1 < 3 * x$
        linarith
      · -- Show $3 * x < 2$
        linarith