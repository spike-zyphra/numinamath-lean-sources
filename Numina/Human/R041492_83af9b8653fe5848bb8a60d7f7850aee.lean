import Mathlib

open Set

/- 3. Let $A$ be the set of all integers that can be represented in the form $x^{2}+2 y^{2}$ where $x, y$ are integers. Let $B$ be the set of all integers that can be represented in the form $x^{2}$ $6 x y+11 y^{2}$ where $x, y$ are integers (for example, $6 \in A$, since $6=2^{2}+2 \cdot 1^{2}$ ). Are the sets $A$ and $B$ equal? Justify your answer. -/
theorem number_theory_235743 :
    {n : ℤ | ∃ x y, n = x^2 + 2 * y^2} =
    {n : ℤ | ∃ x y, n = x^2 + 6 * x * y + 11 * y^2} := by
  ext n
  simp
  -- when we have x, y for first set, we can use x-3y, y for second set and vice versa, so we provide explicit mapping
  constructor <;> (rintro h; obtain ⟨x, y, hxy⟩ := h)
  . use x-3*y,y
    rw [hxy]
    ring
  . use x+3*y,y
    rw [hxy]
    ring